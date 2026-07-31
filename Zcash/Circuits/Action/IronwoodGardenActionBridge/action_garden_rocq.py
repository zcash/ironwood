"""Restricted, parser-backed ActionGarden Lean-to-Rocq translation.

This module consumes the concrete syntax tree emitted by ``actionGardenToIR``.
It intentionally implements only the small, axiom-free surface language used
by ``ActionGarden.lean``.  Every command, type, term, pattern, identifier, and
representation-changing lowering is checked before text is emitted.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import subprocess
from typing import Any, Iterable


class TranslationError(Exception):
    """A fail-closed source translation error."""


def _kind(node: dict[str, Any]) -> str:
    return node.get("kind", "")


def _args(node: dict[str, Any]) -> list[dict[str, Any]]:
    return node.get("args", [])


def _is_null(node: dict[str, Any]) -> bool:
    return node.get("tag") == "node" and _kind(node) == "null"


def _ident(node: dict[str, Any]) -> str:
    if node.get("tag") != "ident":
        raise TranslationError(f"expected identifier, found {_kind(node)!r}")
    return node["raw"]


def _atom(node: dict[str, Any]) -> str:
    if node.get("tag") != "atom":
        raise TranslationError(f"expected atom, found {_kind(node)!r}")
    return node["value"]


def _children_of_kind(
    node: dict[str, Any], kind: str
) -> list[dict[str, Any]]:
    return [child for child in _args(node) if _kind(child) == kind]


def _only(items: Iterable[Any], description: str) -> Any:
    values = list(items)
    if len(values) != 1:
        raise TranslationError(
            f"expected exactly one {description}; found {len(values)}"
        )
    return values[0]


@dataclass(frozen=True)
class Binder:
    names: tuple[str, ...]
    type_node: dict[str, Any]
    implicit: bool = False


@dataclass(frozen=True)
class Declaration:
    kind: str
    name: str
    binders: tuple[Binder, ...]
    result: dict[str, Any] | None
    value: dict[str, Any] | None
    equations: tuple[dict[str, Any], ...] = ()
    fields: tuple[Binder, ...] = ()
    constructors: tuple[tuple[str, tuple[Binder, ...], dict[str, Any]], ...] = ()
    source_node: dict[str, Any] | None = None


def _unwrap_paren(node: dict[str, Any]) -> dict[str, Any]:
    while _kind(node) == "Lean.Parser.Term.paren":
        args = _args(node)
        if len(args) != 3:
            raise TranslationError("unsupported parenthesized term")
        node = args[1]
    return node


def _type_spec(node: dict[str, Any]) -> dict[str, Any]:
    specs = _children_of_kind(node, "Lean.Parser.Term.typeSpec")
    spec = _only(specs, "type specification")
    args = _args(spec)
    if len(args) != 2 or _atom(args[0]) != ":":
        raise TranslationError("unsupported type specification")
    return args[1]


def _binder_type(node: dict[str, Any]) -> dict[str, Any]:
    args = _args(node)
    if (
        len(args) == 2
        and args[0].get("tag") == "atom"
        and _atom(args[0]) == ":"
    ):
        return args[1]
    return _type_spec(node)


def _parse_binder(node: dict[str, Any]) -> Binder:
    kind = _kind(node)
    if kind not in {
        "Lean.Parser.Term.explicitBinder",
        "Lean.Parser.Term.implicitBinder",
    }:
        raise TranslationError(f"unsupported binder {kind!r}")
    args = _args(node)
    names_node = args[1]
    names = tuple(_ident(item) for item in _args(names_node))
    if not names:
        raise TranslationError("empty binder")
    type_container = args[2]
    return Binder(
        names,
        _binder_type(type_container),
        kind == "Lean.Parser.Term.implicitBinder",
    )


def _parse_signature(
    node: dict[str, Any],
) -> tuple[tuple[Binder, ...], dict[str, Any] | None]:
    if _kind(node) != "Lean.Parser.Command.optDeclSig":
        raise TranslationError("expected declaration signature")
    args = _args(node)
    binders: list[Binder] = []
    for item in _args(args[0]):
        binders.append(_parse_binder(item))
    result = None
    result_items = _args(args[1])
    if result_items:
        result = _type_spec(args[1])
    return tuple(binders), result


def _parse_fields(node: dict[str, Any]) -> tuple[Binder, ...]:
    fields: list[Binder] = []
    for field in node.get("args", []):
        if _kind(field) != "Lean.Parser.Command.structSimpleBinder":
            raise TranslationError(
                f"unsupported structure field {_kind(field)!r}"
            )
        args = _args(field)
        name = _ident(args[1])
        binders, result = _parse_signature(args[2])
        if binders or result is None:
            raise TranslationError(f"unsupported structure field {name}")
        fields.append(Binder((name,), result))
    return tuple(fields)


def _check_modifiers(node: dict[str, Any]) -> None:
    if _kind(node) != "Lean.Parser.Command.declModifiers":
        raise TranslationError("expected declaration modifiers")
    stack = list(_args(node))
    while stack:
        item = stack.pop()
        kind = _kind(item)
        if _is_null(item):
            stack.extend(_args(item))
        elif kind == "Lean.Parser.Command.docComment":
            continue
        else:
            raise TranslationError(
                f"unsupported declaration modifier {kind!r}"
            )


def _decl_name(node: dict[str, Any]) -> str:
    if _kind(node) != "Lean.Parser.Command.declId":
        raise TranslationError("expected declaration identifier")
    args = _args(node)
    if len(args) != 2 or _args(args[1]):
        raise TranslationError("namespaces or declaration parameters unsupported")
    return _ident(args[0])


def _parse_declaration(wrapper: dict[str, Any]) -> Declaration:
    if _kind(wrapper) != "Lean.Parser.Command.declaration":
        raise TranslationError("expected declaration command")
    args = _args(wrapper)
    if len(args) != 2:
        raise TranslationError("unsupported declaration wrapper")
    _check_modifiers(args[0])
    command = args[1]
    kind = _kind(command)
    values = _args(command)
    if kind in {
        "Lean.Parser.Command.abbrev",
        "Lean.Parser.Command.definition",
    }:
        expected = 4 if kind.endswith("abbrev") else 5
        if len(values) != expected:
            raise TranslationError(f"unsupported {kind} shape")
        name = _decl_name(values[1])
        binders, result = _parse_signature(values[2])
        value_node = values[3]
        value_kind = _kind(value_node)
        if value_kind == "Lean.Parser.Command.declValSimple":
            value_args = _args(value_node)
            if len(value_args) != 4 or _atom(value_args[0]) != ":=":
                raise TranslationError(f"unsupported definition value for {name}")
            return Declaration(
                "abbrev" if kind.endswith("abbrev") else "def",
                name,
                binders,
                result,
                value_args[1],
                source_node=wrapper,
            )
        if value_kind == "Lean.Parser.Command.declValEqns":
            eqn_root = _only(
                _children_of_kind(
                    value_node,
                    "Lean.Parser.Term.matchAltsWhereDecls",
                ),
                "equation block",
            )
            alts_node = _only(
                _children_of_kind(
                    eqn_root, "Lean.Parser.Term.matchAlts"
                ),
                "equation alternatives",
            )
            alternatives = tuple(
                item
                for group in _args(alts_node)
                for item in _args(group)
                if _kind(item) == "Lean.Parser.Term.matchAlt"
            )
            if not alternatives:
                raise TranslationError(f"empty equation block for {name}")
            return Declaration(
                "def",
                name,
                binders,
                result,
                None,
                alternatives,
                source_node=wrapper,
            )
        raise TranslationError(
            f"unsupported definition value {value_kind!r} for {name}"
        )
    if kind == "Lean.Parser.Command.structure":
        if len(values) != 6:
            raise TranslationError("unsupported structure shape")
        name = _decl_name(values[1])
        binders, result = _parse_signature(values[2])
        if binders or result is not None:
            raise TranslationError(f"parameterized structure unsupported: {name}")
        where = values[4]
        fields_node = _only(
            _children_of_kind(where, "Lean.Parser.Command.structFields"),
            f"field block for {name}",
        )
        deriving = values[5]
        deriving_names: list[str] = []
        stack = list(_args(deriving))
        while stack:
            item = stack.pop()
            if item.get("tag") == "ident":
                deriving_names.append(_ident(item))
            else:
                stack.extend(_args(item))
        if sorted(deriving_names) not in ([], ["DecidableEq", "Repr"]):
            raise TranslationError(
                f"unsupported deriving clause for {name}: {deriving_names}"
            )
        return Declaration(
            "structure",
            name,
            (),
            None,
            None,
            fields=_parse_fields(_args(fields_node)[0]),
            source_node=wrapper,
        )
    if kind == "Lean.Parser.Command.inductive":
        if len(values) != 7:
            raise TranslationError("unsupported inductive shape")
        name = _decl_name(values[1])
        binders, result = _parse_signature(values[2])
        if result is None:
            raise TranslationError(f"inductive {name} lacks a result type")
        constructors: list[
            tuple[str, tuple[Binder, ...], dict[str, Any]]
        ] = []
        ctor_container = values[4]
        for ctor in _args(ctor_container):
            if _kind(ctor) != "Lean.Parser.Command.ctor":
                raise TranslationError(
                    f"unsupported inductive item {_kind(ctor)!r}"
                )
            ctor_args = _args(ctor)
            _check_modifiers(ctor_args[2])
            ctor_name = _ident(ctor_args[3])
            ctor_binders, ctor_result = _parse_signature(ctor_args[4])
            if ctor_result is None:
                raise TranslationError(
                    f"constructor {ctor_name} lacks a result type"
                )
            constructors.append((ctor_name, ctor_binders, ctor_result))
        if not constructors:
            raise TranslationError(f"inductive {name} has no constructors")
        return Declaration(
            "inductive",
            name,
            binders,
            result,
            None,
            constructors=tuple(constructors),
            source_node=wrapper,
        )
    raise TranslationError(f"unsupported declaration kind {kind!r}")


def declarations_from_ir(
    ir: dict[str, Any],
) -> list[Declaration]:
    if ir.get("schema") != 1:
        raise TranslationError(
            f"unsupported parser IR schema {ir.get('schema')!r}"
        )
    root = ir.get("syntax")
    if _kind(root) != "Lean.Parser.Module.module":
        raise TranslationError("parser IR does not contain a Lean module")
    root_args = _args(root)
    if len(root_args) != 2:
        raise TranslationError("unsupported module syntax")
    header = root_args[0]
    imports: list[str] = []
    stack = [header]
    while stack:
        item = stack.pop()
        if _kind(item) == "Lean.Parser.Module.import":
            identifiers = [
                child
                for child in _args(item)
                if child.get("tag") == "ident"
            ]
            imports.append(_ident(_only(identifiers, "import module")))
        stack.extend(_args(item))
    if imports != ["Init.Prelude"]:
        raise TranslationError(
            "standalone source must import exactly Init.Prelude; "
            f"found {imports!r}"
        )

    commands = _args(root_args[1])
    namespace_open = False
    namespace_closed = False
    declarations: list[Declaration] = []
    for command in commands:
        kind = _kind(command)
        if kind in {
            "Lean.Parser.Command.moduleDoc",
            "Lean.Parser.Command.eoi",
        }:
            continue
        if kind == "Lean.Parser.Command.namespace":
            args = _args(command)
            if namespace_open or namespace_closed or _ident(args[1]) != "ActionGarden":
                raise TranslationError("expected one ActionGarden namespace")
            namespace_open = True
            continue
        if kind == "Lean.Parser.Command.end":
            identifiers: list[str] = []
            stack = list(_args(command))
            while stack:
                item = stack.pop()
                if item.get("tag") == "ident":
                    identifiers.append(_ident(item))
                stack.extend(_args(item))
            if not namespace_open or identifiers != ["ActionGarden"]:
                raise TranslationError("unexpected namespace end")
            namespace_open = False
            namespace_closed = True
            continue
        if not namespace_open or namespace_closed:
            raise TranslationError(
                f"command outside ActionGarden namespace: {kind!r}"
            )
        if kind == "Lean.Parser.Command.in":
            args = _args(command)
            if len(args) != 3 or _kind(args[0]) != "Lean.Parser.Command.set_option":
                raise TranslationError("unsupported scoped command")
            option = _args(args[0])
            option_name = _ident(option[1])
            if (
                option_name != "maxRecDepth"
                or _kind(option[3]) != "num"
                or _atom(_args(option[3])[0]) != "100000"
                or _atom(args[1]) != "in"
            ):
                raise TranslationError(
                    "only `set_option maxRecDepth 100000 in` is supported"
                )
            command = args[2]
            kind = _kind(command)
        if kind != "Lean.Parser.Command.declaration":
            raise TranslationError(f"unsupported command {kind!r}")
        declarations.append(_parse_declaration(command))
    if namespace_open or not namespace_closed:
        raise TranslationError("unterminated ActionGarden namespace")
    names = [declaration.name for declaration in declarations]
    duplicates = sorted(
        name for name in set(names) if names.count(name) != 1
    )
    if duplicates:
        raise TranslationError(f"duplicate declarations: {duplicates}")
    reserved = {
        "Int",
        "Nat",
        "Bool",
        "List",
        "Prop",
        "Type",
        "True",
        "Not",
        "decide",
        "and",
    }
    collisions = sorted(reserved.intersection(names))
    if collisions:
        raise TranslationError(
            f"declarations shadow reserved source names: {collisions}"
        )
    if len(declarations) != 119:
        raise TranslationError(
            f"expected 119 source declarations; found {len(declarations)}"
        )
    return declarations


BUILTINS = {
    "Int": "BinNums.Z",
    "Nat": "nat",
    "Bool": "bool",
    "Prop": "Prop",
    "Type": "Type",
    "True": "True",
    "Not": "not",
    "Int.ofNat": "Z.of_nat",
    "Int.add": "Z.add",
    "Int.sub": "Z.sub",
    "Int.mul": "Z.mul",
    "Int.neg": "Z.opp",
    "Int.toNat": "Z.to_nat",
    "Int.le": "Z.le",
    "Int.lt": "Z.lt",
    "Nat.add": "Nat.add",
    "Nat.mul": "Nat.mul",
    "Nat.succ": "S",
    "Nat.zero": "O",
    "List.nil": "nil",
    "List.cons": "cons",
    "List.Mem": "In",
    "and": "andb",
}

SPECIAL_FIELD_NAMES = {
    "x": "actionGardenPointX",
    "y": "actionGardenPointY",
    # Preserve the established Garden-facing selector ABI. These prefixes
    # disambiguate fields whose short Lean names would otherwise collide with
    # declarations or make their owning record unclear.
    "noteCommitQ": "ActionGardenZ_paramsNoteCommitQ",
    "commitIvkQ": "ActionGardenZ_paramsCommitIvkQ",
    "merkleCrhQ": "ActionGardenZ_paramsMerkleCrhQ",
    "action": "ActionGardenZ_fullAction",
    "rcmOld": "ActionGardenZ_fullRcmOld",
    "enableSpend": "ActionGardenZ_fullEnableSpend",
    "enableOutput": "ActionGardenZ_fullEnableOutput",
    "disableCrossAddress": "ActionGardenZ_fullDisableCrossAddress",
}

CONSTRUCTOR_NAMES = {
    "Point.mk": "Build_ActionGardenPointData",
    "State3.mk": "Build_ActionGardenState3Data",
    "nil": "ActionGardenMerklePathDefinedNil",
    "cons": "ActionGardenMerklePathDefinedCons",
}


class Emitter:
    def __init__(self, declarations: list[Declaration]):
        self.declarations = declarations
        self.declaration_names = {declaration.name for declaration in declarations}
        self.fields = {
            name
            for declaration in declarations
            for binder in declaration.fields
            for name in binder.names
        }
        self.prior: set[str] = set()

    @staticmethod
    def global_name(name: str) -> str:
        return f"ActionGardenZ_{name}"

    @staticmethod
    def field_name(name: str) -> str:
        return SPECIAL_FIELD_NAMES.get(name, f"ActionGardenZ_{name}")

    def render_type(
        self, node: dict[str, Any], locals_: set[str] | None = None
    ) -> str:
        locals_ = locals_ or set()
        node = _unwrap_paren(node)
        kind = _kind(node)
        if node.get("tag") == "ident":
            return self.render_identifier(_ident(node), locals_, type_mode=True)
        if kind in {
            "Lean.Parser.Term.prop",
            "Lean.Parser.Term.type",
        }:
            atoms = [
                item for item in _args(node) if item.get("tag") == "atom"
            ]
            return _atom(_only(atoms, "sort"))
        if kind == "Lean.Parser.Term.app":
            args = _args(node)
            function = _ident(args[0])
            operands = _args(args[1])
            if function == "List" and len(operands) == 1:
                return f"list {self.render_type(operands[0], locals_)}"
            rendered = self.render_identifier(
                function, locals_, type_mode=True
            )
            return " ".join(
                [rendered]
                + [self.parenthesize_type(item, locals_) for item in operands]
            )
        if kind == "Lean.Parser.Term.arrow":
            left, arrow, right = _args(node)
            if _atom(arrow) not in {"→", "->"}:
                raise TranslationError("unsupported arrow")
            return (
                f"{self.parenthesize_type(left, locals_)} -> "
                f"{self.render_type(right, locals_)}"
            )
        if kind == "«term_×_»":
            left, _, right = _args(node)
            parts = self.product_parts(left) + self.product_parts(right)
            if len(parts) not in {2, 3}:
                raise TranslationError(
                    "only pairs and Garden path triples are supported"
                )
            # Garden's existing ABI represents Lean's right-nested triples as
            # left-nested Rocq products.
            rendered = self.render_type(parts[0], locals_)
            for item in parts[1:]:
                rendered = (
                    f"({rendered} * {self.render_type(item, locals_)})"
                )
            return rendered
        raise TranslationError(f"unsupported type syntax {kind!r}")

    def parenthesize_type(
        self, node: dict[str, Any], locals_: set[str]
    ) -> str:
        rendered = self.render_type(node, locals_)
        if _kind(_unwrap_paren(node)) in {
            "Lean.Parser.Term.arrow",
            "«term_×_»",
            "Lean.Parser.Term.app",
        }:
            return f"({rendered})"
        return rendered

    def product_parts(
        self, node: dict[str, Any]
    ) -> list[dict[str, Any]]:
        node = _unwrap_paren(node)
        if _kind(node) != "«term_×_»":
            return [node]
        args = _args(node)
        return self.product_parts(args[0]) + self.product_parts(args[2])

    def render_identifier(
        self, raw: str, locals_: set[str], *, type_mode: bool = False
    ) -> str:
        if raw in locals_:
            return raw
        if "." in raw and raw.split(".", maxsplit=1)[0] in locals_:
            head, *tail = raw.split(".")
            expression = head
            for field in tail:
                if field == "length":
                    expression = f"(List.length {expression})"
                elif field in self.fields:
                    expression = f"({self.field_name(field)} {expression})"
                else:
                    raise TranslationError(
                        f"unknown field projection {raw!r}"
                    )
            return expression
        if raw in BUILTINS:
            return BUILTINS[raw]
        if raw in self.declaration_names:
            if raw not in self.prior:
                raise TranslationError(
                    f"forward or unresolved declaration reference {raw!r}"
                )
            return self.global_name(raw)
        if raw == "List":
            return "list"
        if raw in CONSTRUCTOR_NAMES:
            return CONSTRUCTOR_NAMES[raw]
        if "." in raw:
            head, *tail = raw.split(".")
            if head in {"Point", "State3"} and tail == ["mk"]:
                return CONSTRUCTOR_NAMES[raw]
            raise TranslationError(f"unknown global reference {raw!r}")
        raise TranslationError(f"unknown identifier {raw!r}")

    def render_binders(
        self, binders: tuple[Binder, ...], locals_: set[str]
    ) -> tuple[str, set[str]]:
        rendered: list[str] = []
        environment = set(locals_)
        for binder in binders:
            binder_type = self.render_type(binder.type_node, environment)
            names = " ".join(binder.names)
            delimiters = ("{", "}") if binder.implicit else ("(", ")")
            rendered.append(
                f"{delimiters[0]}{names} : {binder_type}{delimiters[1]}"
            )
            environment.update(binder.names)
        return " ".join(rendered), environment

    def render_number(
        self, node: dict[str, Any], expected: str | None
    ) -> str:
        value = _atom(_args(node)[0])
        if expected == "nat":
            if value == "0":
                return "O"
            return f"{value}%nat"
        return value

    def render_projection(
        self, node: dict[str, Any], locals_: set[str]
    ) -> str:
        first_args = _args(node)
        if first_args[2].get("tag") == "ident":
            field = _ident(first_args[2])
            if field not in self.fields:
                raise TranslationError(
                    f"unknown named projection {field!r}"
                )
            return (
                f"({self.field_name(field)} "
                f"{self.render_expr(first_args[0], locals_)})"
            )
        indices: list[str] = []
        while _kind(node) == "Lean.Parser.Term.proj":
            args = _args(node)
            index = _atom(_args(args[2])[0])
            indices.append(index)
            node = args[0]
        indices.reverse()
        base = self.render_expr(node, locals_)
        chain = ".".join(indices)
        triple = {
            "1": f"(fst (fst {base}))",
            "2.1": f"(snd (fst {base}))",
            "2.2": f"(snd {base})",
        }
        if chain not in triple:
            raise TranslationError(
                f"unsupported tuple projection chain .{chain}"
            )
        return triple[chain]

    def render_pattern(
        self, node: dict[str, Any], locals_: set[str]
    ) -> tuple[str, set[str]]:
        node = _unwrap_paren(node)
        kind = _kind(node)
        if node.get("tag") == "ident":
            raw = _ident(node)
            if raw in {"List.nil", "Nat.zero"}:
                return BUILTINS[raw], set()
            if raw in {"True"}:
                return raw, set()
            return raw, {raw}
        if kind == "Lean.Parser.Term.hole":
            return "_", set()
        if kind == "num":
            value = _atom(_args(node)[0])
            if value != "0":
                raise TranslationError(
                    f"only zero numeric patterns supported, found {value}"
                )
            return "O", set()
        if kind == "Lean.Parser.Term.app":
            args = _args(node)
            function = _ident(args[0])
            if function not in {
                "Nat.succ",
                "List.cons",
            }:
                raise TranslationError(
                    f"unsupported pattern constructor {function!r}"
                )
            rendered: list[str] = [BUILTINS[function]]
            bound: set[str] = set()
            for argument in _args(args[1]):
                text, names = self.render_pattern(argument, locals_ | bound)
                rendered.append(text)
                bound.update(names)
            return " ".join(rendered), bound
        raise TranslationError(f"unsupported pattern syntax {kind!r}")

    def render_match_alt(
        self, node: dict[str, Any], locals_: set[str]
    ) -> str:
        args = _args(node)
        patterns_container = args[1]
        pattern_groups = _args(patterns_container)
        if len(pattern_groups) != 1:
            raise TranslationError("unsupported match pattern group")
        pattern_items = _args(pattern_groups[0])
        patterns: list[dict[str, Any]] = []
        for item in pattern_items:
            if item.get("tag") == "atom" and _atom(item) == ",":
                continue
            patterns.append(item)
        rendered_patterns: list[str] = []
        bound: set[str] = set()
        for pattern in patterns:
            text, names = self.render_pattern(pattern, locals_ | bound)
            rendered_patterns.append(text)
            bound.update(names)
        body = self.render_expr(args[3], locals_ | bound)
        return f"| {', '.join(rendered_patterns)} => {body}"

    def render_struct(
        self, node: dict[str, Any], locals_: set[str]
    ) -> str:
        fields_node = _only(
            _children_of_kind(
                node, "Lean.Parser.Term.structInstFields"
            ),
            "structure literal field block",
        )
        fields: list[str] = []
        pending = list(reversed(_args(fields_node)))
        while pending:
            item = pending.pop()
            if _is_null(item):
                pending.extend(reversed(_args(item)))
                continue
            if item.get("tag") == "atom" and _atom(item) == ",":
                continue
            if _kind(item) != "Lean.Parser.Term.structInstField":
                raise TranslationError(
                    f"unsupported structure literal item {_kind(item)!r}"
                )
            item_args = _args(item)
            lvalue = item_args[0]
            field = _ident(_args(lvalue)[0])
            if field not in self.fields:
                raise TranslationError(
                    f"unknown structure literal field {field!r}"
                )
            definition = _only(
                _children_of_kind(
                    item_args[1],
                    "Lean.Parser.Term.structInstFieldDef",
                ),
                f"value for field {field}",
            )
            value_args = _args(definition)
            value = value_args[-1]
            fields.append(
                f"{self.field_name(field)} := "
                f"{self.render_expr(value, locals_)}"
            )
        return "{| " + "; ".join(fields) + " |}"

    def render_app(
        self,
        node: dict[str, Any],
        locals_: set[str],
        expected: str | None,
    ) -> str:
        args = _args(node)
        if args[0].get("tag") != "ident":
            function = self.render_expr(args[0], locals_)
            raw = ""
        else:
            raw = _ident(args[0])
            function = ""
        operands = _args(args[1])
        if raw and (
            raw in locals_ or raw.split(".", maxsplit=1)[0] in locals_
        ):
            # A local name must never be mistaken for a primitive merely
            # because its spelling matches one of the audited source names.
            function = self.render_identifier(raw, locals_)
            raw = ""
        if raw == "decide":
            if len(operands) != 1:
                raise TranslationError("unsupported decide application")
            equality = _unwrap_paren(operands[0])
            if _kind(equality) != "«term_=_»":
                raise TranslationError("decide is supported only for equality")
            equality_args = _args(equality)
            return (
                f"(Z.eqb {self.render_expr(equality_args[0], locals_)} "
                f"{self.render_expr(equality_args[2], locals_)})"
            )
        if raw == "Int.ediv":
            if len(operands) != 2:
                raise TranslationError("Int.ediv expects two operands")
            dividend = self.render_expr(operands[0], locals_)
            divisor = self.render_expr(operands[1], locals_)
            return (
                f"(match {divisor} with "
                f"| Zneg magnitude => "
                f"Z.opp (Z.div {dividend} (Z.pos magnitude)) "
                f"| _ => Z.div {dividend} {divisor} end)"
            )
        if raw == "Int.emod":
            if len(operands) != 2:
                raise TranslationError("Int.emod expects two operands")
            dividend = self.render_expr(operands[0], locals_)
            modulus = self.render_expr(operands[1], locals_)
            return (
                f"(match {modulus} with "
                f"| Zneg magnitude => Z.modulo {dividend} (Z.pos magnitude) "
                f"| _ => Z.modulo {dividend} {modulus} end)"
            )
        if raw == "Int.pow":
            if len(operands) != 2:
                raise TranslationError("Int.pow expects two operands")
            return (
                f"(Z.pow {self.render_expr(operands[0], locals_)} "
                f"(Z.of_nat {self.render_expr(operands[1], locals_, 'nat')}))"
            )
        if raw == "List.foldl":
            if len(operands) != 3:
                raise TranslationError("List.foldl expects three operands")
            return (
                f"(fold_left {self.render_expr(operands[0], locals_)} "
                f"{self.render_expr(operands[2], locals_)} "
                f"{self.render_expr(operands[1], locals_)})"
            )
        if raw == "List.getD":
            raise TranslationError(
                "List.getD is permitted only in the audited "
                "listGetDAtZ representation lowering"
            )
        if raw:
            function = self.render_identifier(raw, locals_)
        expected_arguments: dict[str, dict[int, str]] = {
            "Int.ofNat": {0: "nat"},
            "Nat.add": {0: "nat", 1: "nat"},
            "Nat.mul": {0: "nat", 1: "nat"},
            "Nat.succ": {0: "nat"},
            "zPowNat": {1: "nat"},
            "iterateIndexed": {0: "nat"},
            "iterateIndexedFrom": {0: "nat", 1: "nat"},
            "wordsLe": {0: "nat"},
        }
        rendered_operands = [
            self.render_expr(
                operand,
                locals_,
                expected_arguments.get(raw, {}).get(index),
            )
            for index, operand in enumerate(operands)
        ]
        return "(" + " ".join([function] + rendered_operands) + ")"

    def render_expr(
        self,
        node: dict[str, Any],
        locals_: set[str],
        expected: str | None = None,
    ) -> str:
        node = _unwrap_paren(node)
        kind = _kind(node)
        if node.get("tag") == "ident":
            return self.render_identifier(_ident(node), locals_)
        if kind == "num":
            return self.render_number(node, expected)
        if kind == "Lean.Parser.Term.app":
            return self.render_app(node, locals_, expected)
        if kind in {"«term_∧_»", "«term_∨_»", "«term_=_»"}:
            left, operator, right = _args(node)
            op = {
                "«term_∧_»": "/\\",
                "«term_∨_»": "\\/",
                "«term_=_»": "=",
            }[kind]
            if _atom(operator) not in {"/\\", "\\/", "="}:
                raise TranslationError("unexpected infix operator")
            right_expected = None
            if (
                kind == "«term_=_»"
                and left.get("tag") == "ident"
                and _ident(left).endswith(".length")
            ):
                right_expected = "nat"
            return (
                f"({self.render_expr(left, locals_)} {op} "
                f"{self.render_expr(right, locals_, right_expected)})"
            )
        if kind == "Lean.Parser.Term.arrow":
            left, _, right = _args(node)
            return (
                f"({self.render_expr(left, locals_)} -> "
                f"{self.render_expr(right, locals_)})"
            )
        if kind == "termIfThenElse":
            args = _args(node)
            return (
                f"(if {self.render_expr(args[1], locals_)} then "
                f"{self.render_expr(args[3], locals_)} else "
                f"{self.render_expr(args[5], locals_)})"
            )
        if kind == "Lean.Parser.Term.let":
            args = _args(node)
            declaration = _only(
                _children_of_kind(args[2], "Lean.Parser.Term.letIdDecl"),
                "let declaration",
            )
            declaration_args = _args(declaration)
            let_id = declaration_args[0]
            if _kind(let_id) != "Lean.Parser.Term.letId":
                raise TranslationError("unsupported let identifier")
            name = _ident(_args(let_id)[0])
            if _args(declaration_args[1]) or _args(declaration_args[2]):
                raise TranslationError("typed or function let unsupported")
            value = declaration_args[4]
            body = args[4]
            return (
                f"(let {name} := {self.render_expr(value, locals_)} in "
                f"{self.render_expr(body, locals_ | {name})})"
            )
        if kind == "Lean.Parser.Term.structInst":
            return self.render_struct(node, locals_)
        if kind == "Lean.Parser.Term.fun":
            basic = _only(
                _children_of_kind(node, "Lean.Parser.Term.basicFun"),
                "function body",
            )
            basic_args = _args(basic)
            names = tuple(
                _ident(item) for item in _args(basic_args[0])
            )
            if not names or _args(basic_args[1]):
                raise TranslationError(
                    "only untyped explicit lambda binders supported"
                )
            return (
                f"(fun {' '.join(names)} => "
                f"{self.render_expr(basic_args[3], locals_ | set(names))})"
            )
        if kind == "Lean.Parser.Term.match":
            args = _args(node)
            discr_container = args[3]
            discriminants = []
            for item in _args(discr_container):
                if _kind(item) == "Lean.Parser.Term.matchDiscr":
                    discriminants.append(item)
                else:
                    discriminants.append(
                        _only(
                            _children_of_kind(
                                item, "Lean.Parser.Term.matchDiscr"
                            ),
                            "match discriminant",
                        )
                    )
            rendered_discriminants = [
                self.render_expr(_args(item)[1], locals_)
                for item in discriminants
            ]
            alts_node = args[5]
            alternatives = [
                item
                for group in _args(alts_node)
                for item in _args(group)
                if _kind(item) == "Lean.Parser.Term.matchAlt"
            ]
            return (
                f"(match {', '.join(rendered_discriminants)} with "
                + " ".join(
                    self.render_match_alt(item, locals_)
                    for item in alternatives
                )
                + " end)"
            )
        if kind == "Lean.Parser.Term.proj":
            return self.render_projection(node, locals_)
        if kind == "Lean.Parser.Term.tuple":
            tuple_items: list[dict[str, Any]] = []

            def collect(container: dict[str, Any]) -> None:
                for item in _args(container):
                    if item.get("tag") == "atom" and _atom(item) == ",":
                        continue
                    if _is_null(item):
                        collect(item)
                    else:
                        tuple_items.append(item)

            collect(_args(node)[1])
            if len(tuple_items) != 3:
                raise TranslationError(
                    "only Garden path triples are supported"
                )
            first, second, third = (
                self.render_expr(item, locals_) for item in tuple_items
            )
            return f"(({first}, {second}), {third})"
        if kind == "Lean.Parser.Term.forall":
            args = _args(node)
            names = tuple(_ident(item) for item in _args(args[1]))
            binder_type = _type_spec(args[2])
            return (
                f"(forall {' '.join(names)} : "
                f"{self.render_type(binder_type, locals_)}, "
                f"{self.render_expr(args[4], locals_ | set(names))})"
            )
        if kind in {"Lean.Parser.Term.prop", "Lean.Parser.Term.type"}:
            return self.render_type(node, locals_)
        raise TranslationError(f"unsupported term syntax {kind!r}")

    def _body_mentions(
        self, node: dict[str, Any], name: str
    ) -> bool:
        stack = [node]
        while stack:
            item = stack.pop()
            if item.get("tag") == "ident" and _ident(item) == name:
                return True
            stack.extend(_args(item))
        return False

    def _special_list_get(self, declaration: Declaration) -> str:
        if declaration.value is None:
            raise TranslationError("listGetDAtZ must have a body")
        rendered_binders, signature_locals = self.render_binders(
            declaration.binders, set()
        )
        if (
            rendered_binders
            != "{A : Type} (values : list A) "
            "(index : ActionGardenZ_Z) (fallback : A)"
            or declaration.result is None
            or self.render_type(declaration.result, signature_locals) != "A"
        ):
            raise TranslationError("unsupported listGetDAtZ signature")
        body = _unwrap_paren(declaration.value)
        if _kind(body) != "Lean.Parser.Term.app":
            raise TranslationError("unsupported listGetDAtZ body")
        args = _args(body)
        operands = _args(args[1])
        if (
            _ident(args[0]) != "List.getD"
            or len(operands) != 3
            or _ident(operands[0]) != "values"
            or _ident(operands[2]) != "fallback"
        ):
            raise TranslationError("unsupported listGetDAtZ body")
        index = _unwrap_paren(operands[1])
        if (
            _kind(index) != "Lean.Parser.Term.app"
            or _ident(_args(index)[0]) != "Int.toNat"
            or [_ident(item) for item in _args(_args(index)[1])]
            != ["index"]
        ):
            raise TranslationError("unsupported listGetDAtZ index conversion")
        name = self.global_name(declaration.name)
        z = self.global_name("Z")
        zero = self.global_name("zZero")
        return (
            f"Definition {name} {{A : Type}} "
            f"(values : PrimArray.array A) (index : {z}) "
            f"(fallback : A) : A :=\n"
            f"  let normalizedIndex := Z.max {zero} index in\n"
            f"  if Z.ltb normalizedIndex "
            f"(Uint63.to_Z (PrimArray.length values)) then\n"
            f"    PrimArray.get values (Uint63.of_Z normalizedIndex)\n"
            f"  else fallback."
        )

    def render_structure(self, declaration: Declaration) -> str:
        name = self.global_name(declaration.name)
        if declaration.name == "Point":
            expected = [("x", "Z"), ("y", "Z")]
            actual = [
                (
                    binder.names[0],
                    _ident(_unwrap_paren(binder.type_node)),
                )
                for binder in declaration.fields
            ]
            if actual != expected:
                raise TranslationError(
                    f"unsupported Point representation: {actual!r}"
                )
            return f"Definition {name} : Type := ActionGardenPointData."
        if declaration.name == "State3":
            expected = [("x0", "Z"), ("x1", "Z"), ("x2", "Z")]
            actual = [
                (
                    binder.names[0],
                    _ident(_unwrap_paren(binder.type_node)),
                )
                for binder in declaration.fields
            ]
            if actual != expected:
                raise TranslationError(
                    f"unsupported State3 representation: {actual!r}"
                )
            return f"Definition {name} : Type := ActionGardenState3Data."
        fields = [
            f"  {self.field_name(binder.names[0])} : "
            f"{self.render_type(binder.type_node)}"
            for binder in declaration.fields
        ]
        return (
            f"Record {name} : Type := {{\n"
            + ";\n".join(fields)
            + "\n}."
        )

    def render_equations(self, declaration: Declaration) -> str:
        if declaration.binders:
            raise TranslationError(
                "equation definitions with explicit binders unsupported"
            )
        if declaration.result is None:
            raise TranslationError(
                f"equation definition {declaration.name} lacks type"
            )
        types: list[dict[str, Any]] = []
        result = declaration.result
        while _kind(_unwrap_paren(result)) == "Lean.Parser.Term.arrow":
            arrow = _unwrap_paren(result)
            args = _args(arrow)
            types.append(args[0])
            result = args[2]
        if not types:
            raise TranslationError(
                f"equation definition {declaration.name} is not a function"
            )
        preferred = {
            "pointNatMul": ("scalar", "point"),
            "sinsemillaHashDefinedFromGarden": ("accumulator", "words"),
            "wordsLe": ("count", "value"),
            "pathLayersFrom": ("expected", "path"),
        }.get(declaration.name)
        if preferred is None or len(preferred) != len(types):
            raise TranslationError(
                f"unsupported equation definition {declaration.name}"
            )
        locals_ = set(preferred)
        binders = " ".join(
            f"({name} : {self.render_type(type_node)})"
            for name, type_node in zip(preferred, types, strict=True)
        )
        alternatives = " ".join(
            self.render_match_alt(item, locals_)
            for item in declaration.equations
        )
        discriminants = ", ".join(preferred)
        return (
            f"Fixpoint {self.global_name(declaration.name)} {binders} : "
            f"{self.render_type(result)} :=\n"
            f"  match {discriminants} with {alternatives} end."
        )

    def render_inductive(self, declaration: Declaration) -> str:
        if declaration.name != "merklePathDefinedFromGarden":
            raise TranslationError(
                f"unsupported inductive {declaration.name!r}"
            )
        binders, locals_ = self.render_binders(
            declaration.binders, set()
        )
        result = self.render_type(declaration.result, locals_)
        constructors: list[str] = []
        for ctor_name, ctor_binders, ctor_result in declaration.constructors:
            mapped = CONSTRUCTOR_NAMES.get(ctor_name)
            if mapped is None:
                raise TranslationError(
                    f"unsupported constructor {ctor_name!r}"
                )
            rendered_binders, ctor_locals = self.render_binders(
                ctor_binders, locals_
            )
            rendered_result = self.render_expr(
                ctor_result, ctor_locals
            )
            constructors.append(
                f"| {mapped} {rendered_binders} : {rendered_result}"
            )
        return (
            f"Inductive {self.global_name(declaration.name)} {binders} : "
            f"{result} :=\n  "
            + "\n  ".join(constructors)
            + "."
        )

    def render_declaration(self, declaration: Declaration) -> str:
        if declaration.kind == "structure":
            return self.render_structure(declaration)
        if declaration.kind == "inductive":
            return self.render_inductive(declaration)
        if declaration.equations:
            return self.render_equations(declaration)
        if declaration.name == "listGetDAtZ":
            return self._special_list_get(declaration)
        if declaration.name in {
            "orchardPoseidonRoundConstants",
            "orchardSinsemillaGenerators",
        }:
            expected_source_type = (
                f"list {self.global_name('State3')}"
                if declaration.name == "orchardPoseidonRoundConstants"
                else f"list {self.global_name('Point')}"
            )
            if (
                declaration.binders
                or declaration.result is None
                or self.render_type(declaration.result)
                != expected_source_type
            ):
                raise TranslationError(
                    f"unsupported {declaration.name} signature"
                )
            target_type = (
                f"PrimArray.array {self.global_name('State3')}"
                if declaration.name == "orchardPoseidonRoundConstants"
                else f"PrimArray.array {self.global_name('Point')}"
            )
            storage = (
                "actionGardenPoseidonRoundConstantsData"
                if declaration.name == "orchardPoseidonRoundConstants"
                else "actionGardenSinsemillaGeneratorsData"
            )
            return (
                f"Definition {self.global_name(declaration.name)} : "
                f"{target_type} := {storage}."
            )
        if declaration.value is None or declaration.result is None:
            if declaration.kind == "abbrev" and declaration.value is not None:
                result = "Type"
            else:
                raise TranslationError(
                    f"declaration {declaration.name} lacks type or body"
                )
        binders, locals_ = self.render_binders(
            declaration.binders, set()
        )
        if declaration.result is not None:
            result = self.render_type(declaration.result, locals_)
        recursive = (
            declaration.kind == "def"
            and self._body_mentions(declaration.value, declaration.name)
        )
        keyword = "Fixpoint" if recursive else "Definition"
        body = self.render_expr(declaration.value, locals_)
        separator = " " if binders else ""
        return (
            f"{keyword} {self.global_name(declaration.name)}"
            f"{separator}{binders} : {result} :=\n  {body}."
        )

    def render(self, source_hash: str) -> str:
        preamble = f"""(** Generated from the axiom-free Lean ActionGarden.
    Lean source SHA-256: {source_hash}

    This file is emitted from Lean's parser syntax tree by a closed,
    fail-closed translation. *)

From Stdlib Require Import ZArith List Bool Uint63 Array.PrimArray.
Require Export
  Garden.Orchard.IronwoodGardenActionBridge.action_garden_constants.
Import ListNotations.
Open Scope Z_scope.

"""
        rendered: list[str] = []
        for declaration in self.declarations:
            # The current declaration may occur recursively in its own body.
            # Later declarations are still rejected because they are absent.
            self.prior.add(declaration.name)
            text = self.render_declaration(declaration)
            rendered.append(text)
        return preamble + "\n\n".join(rendered) + "\n"


def _table_rows(
    declaration: Declaration,
    constructor: str,
    arity: int,
    count: int,
) -> list[tuple[str, ...]]:
    if declaration.value is None:
        raise TranslationError(f"{declaration.name} lacks a table body")
    rows: list[tuple[str, ...]] = []
    node = _unwrap_paren(declaration.value)
    while True:
        if node.get("tag") == "ident" and _ident(node) == "List.nil":
            break
        if _kind(node) != "Lean.Parser.Term.app":
            raise TranslationError(
                f"unsupported list spine in {declaration.name}"
            )
        args = _args(node)
        if _ident(args[0]) != "List.cons":
            raise TranslationError(
                f"unsupported list constructor in {declaration.name}"
            )
        operands = _args(args[1])
        if len(operands) != 2:
            raise TranslationError(
                f"invalid list constructor in {declaration.name}"
            )
        row = _unwrap_paren(operands[0])
        if _kind(row) != "Lean.Parser.Term.app":
            raise TranslationError(
                f"invalid table row in {declaration.name}"
            )
        row_args = _args(row)
        if _ident(row_args[0]) != constructor:
            raise TranslationError(
                f"expected {constructor} row in {declaration.name}"
            )
        values = _args(row_args[1])
        if len(values) != arity:
            raise TranslationError(
                f"expected arity {arity} in {declaration.name}"
            )
        rendered: list[str] = []
        for value in values:
            value = _unwrap_paren(value)
            if _kind(value) != "num":
                raise TranslationError(
                    f"table cells must be integer literals in {declaration.name}"
                )
            rendered.append(_atom(_args(value)[0]))
        rows.append(tuple(rendered))
        node = _unwrap_paren(operands[1])
    if len(rows) != count:
        raise TranslationError(
            f"expected {count} rows in {declaration.name}; found {len(rows)}"
        )
    return rows


def render_constants(
    declarations: list[Declaration],
    source_hash: str,
) -> str:
    by_name = {declaration.name: declaration for declaration in declarations}
    state_rows = _table_rows(
        by_name["orchardPoseidonRoundConstants"],
        "State3.mk",
        3,
        64,
    )
    point_rows = _table_rows(
        by_name["orchardSinsemillaGenerators"],
        "Point.mk",
        2,
        1024,
    )

    def data_record(
        source_name: str, target_name: str
    ) -> str:
        declaration = by_name[source_name]
        fields: list[str] = []
        for binder in declaration.fields:
            if len(binder.names) != 1:
                raise TranslationError(
                    f"unsupported field binder in {source_name}"
                )
            field_type = _unwrap_paren(binder.type_node)
            if (
                field_type.get("tag") != "ident"
                or _ident(field_type) != "Z"
            ):
                raise TranslationError(
                    f"{source_name} storage fields must have type Z"
                )
            field = Emitter.field_name(binder.names[0])
            fields.append(f"  {field} : BinNums.Z")
        if not fields:
            raise TranslationError(
                f"{source_name} storage record has no fields"
            )
        return (
            f"Record {target_name} : Type := {{\n"
            + ";\n".join(fields)
            + "\n}."
        )

    state_record = data_record("State3", "ActionGardenState3Data")
    point_record = data_record("Point", "ActionGardenPointData")
    state_payload = (
        "[|\n"
        + ";\n".join(
            "  Build_ActionGardenState3Data " + " ".join(row)
            for row in state_rows
        )
        + "\n| Build_ActionGardenState3Data 0 0 0 |]"
    )
    point_payload = (
        "[|\n"
        + ";\n".join(
            "  Build_ActionGardenPointData " + " ".join(row)
            for row in point_rows
        )
        + "\n| Build_ActionGardenPointData 0 0 |]"
    )
    return f"""(** Generated storage for the two large tables in the axiom-free Lean
    ActionGarden source.

    Lean source SHA-256: {source_hash}

    The Lean source deliberately uses ordinary lists. This generated Rocq
    target stores the same rows in immutable primitive arrays so lookup is
    constant-time and the 1,024-entry table has no list spine for Rocq to
    reduce or serialize. Array indices are an implementation detail: the
    generated public accessor still accepts [Z] and checks bounds before
    converting to Rocq's primitive index type. *)

From Stdlib Require Import ZArith Array.PrimArray.
Open Scope Z_scope.

{state_record}

Definition actionGardenPoseidonRoundConstantsData
    : PrimArray.array ActionGardenState3Data :=
{state_payload}.

{point_record}

Definition actionGardenSinsemillaGeneratorsData
    : PrimArray.array ActionGardenPointData :=
{point_payload}.

(** Keep aliases in the main generated file from unfolding the complete
    payload while Rocq serializes them. Auditing proofs may locally use
    [Transparent] because these are ordinary definitions, not axioms. *)
Global Opaque
  actionGardenPoseidonRoundConstantsData
  actionGardenSinsemillaGeneratorsData.
"""


def load_ir(source_path: Path, repository: Path) -> dict[str, Any]:
    executable = repository / ".lake" / "build" / "bin" / "actionGardenToIR"
    command = (
        [str(executable), str(source_path)]
        if executable.exists()
        else ["lake", "exe", "actionGardenToIR", str(source_path)]
    )
    completed = subprocess.run(
        command,
        cwd=repository,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise TranslationError(
            "Lean frontend rejected ActionGarden source"
            + (f":\n{detail}" if detail else "")
        )
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise TranslationError(
            f"invalid JSON from actionGardenToIR: {error}"
        ) from error


def translate(
    source_path: Path,
    repository: Path,
) -> tuple[str, str, list[Declaration], str]:
    ir = load_ir(source_path, repository)
    source = ir.get("contents")
    if not isinstance(source, str):
        raise TranslationError("parser IR lacks its immutable source snapshot")
    source_hash = hashlib.sha256(source.encode()).hexdigest()
    declarations = declarations_from_ir(ir)
    emitter = Emitter(declarations)
    main = emitter.render(source_hash)
    constants = render_constants(declarations, source_hash)
    return main, constants, declarations, source
