"""Regression tests for the fail-closed ActionGarden translator."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from action_garden_rocq import (
    TranslationError,
    declarations_from_ir,
    load_ir,
    translate,
)


BRIDGE = Path(__file__).resolve().parent
REPOSITORY = BRIDGE.parents[3]
SOURCE = BRIDGE / "ActionGarden.lean"
GENERATOR = BRIDGE / "lean_to_rocq.py"
HASH = re.compile(r"Lean source SHA-256: [0-9a-f]{64}")


def without_hash(value: str) -> str:
    return HASH.sub("Lean source SHA-256: HASH", value)


class TranslatorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        subprocess.run(
            ["lake", "build", "actionGardenToIR"],
            cwd=REPOSITORY,
            check=True,
        )

    def translate_source(self, source: str) -> tuple[str, str]:
        with tempfile.TemporaryDirectory() as directory:
            input_path = Path(directory) / "ActionGarden.lean"
            input_path.write_text(source)
            main, constants, declarations, snapshot = translate(
                input_path, REPOSITORY
            )
            self.assertEqual(len(declarations), 119)
            self.assertEqual(snapshot, source)
            return main, constants

    def test_parser_ir_has_complete_inventory_and_spans(self) -> None:
        ir = load_ir(SOURCE, REPOSITORY)
        declarations = declarations_from_ir(ir)
        self.assertEqual(len(declarations), 119)
        self.assertEqual(declarations[0].name, "Z")
        self.assertEqual(declarations[-1].name, "orchardAction")
        def token_spans(node: dict) -> list[dict]:
            spans = []
            if isinstance(node.get("span"), dict):
                spans.append(node["span"])
            for child in node.get("args", []):
                spans.extend(token_spans(child))
            return spans

        first_spans = token_spans(declarations[0].source_node)
        last_spans = token_spans(declarations[-1].source_node)
        self.assertTrue(first_spans)
        self.assertTrue(last_spans)
        self.assertIn("start", first_spans[0])
        self.assertIn("stop", last_spans[-1])

    def test_translation_is_deterministic(self) -> None:
        first = self.translate_source(SOURCE.read_text())
        second = self.translate_source(SOURCE.read_text())
        self.assertEqual(first, second)

    def test_body_only_modulus_mutation_changes_rocq_literal(self) -> None:
        source = SOURCE.read_text()
        original = self.translate_source(source)[0]
        mutated = self.translate_source(
            source.replace(
                "28948022309329048855892746252171976963363056481941560715954676764349967630337",
                "28948022309329048855892746252171976963363056481941560715954676764349967630338",
                1,
            )
        )[0]
        self.assertNotEqual(without_hash(original), without_hash(mutated))
        self.assertIn("49967630338", mutated)

    def test_body_only_primitive_mutation_changes_rocq_body(self) -> None:
        source = SOURCE.read_text()
        original = self.translate_source(source)[0]
        mutated = self.translate_source(
            source.replace(
                "def zAdd (left right : Z) : Z := Int.add left right",
                "def zAdd (left right : Z) : Z := Int.sub left right",
                1,
            )
        )[0]
        self.assertNotEqual(without_hash(original), without_hash(mutated))
        self.assertIn(
            "ActionGardenZ_zAdd (left right : ActionGardenZ_Z)",
            mutated,
        )
        zadd = mutated.split("Definition ActionGardenZ_zAdd", 1)[1].split(
            "\n\n", 1
        )[0]
        self.assertIn("Z.sub left right", zadd)

    def test_special_primitives_cannot_bypass_lowering(self) -> None:
        source = SOURCE.read_text()
        mutations = [
            (
                "def zDiv (dividend divisor : Z) : Z := "
                "Int.ediv dividend divisor",
                "def zDiv : Z → Z → Z := Int.ediv",
            ),
            (
                "def zMod (dividend modulus : Z) : Z := "
                "Int.emod dividend modulus",
                "def zMod : Z → Z → Z := Int.emod",
            ),
            (
                "def zPowNat (base : Z) (exponent : Nat) : Z := "
                "Int.pow base exponent",
                "def zPowNat : Z → Nat → Z := Int.pow",
            ),
            (
                "def sinsemillaHashToPointGarden\n"
                "    (domain : Point) (words : List Z) : Point :=\n"
                "  List.foldl sinsemillaRound domain words",
                "def sinsemillaHashToPointGarden : "
                "Point → List Z → Point :=\n"
                "  List.foldl sinsemillaRound",
            ),
        ]
        for original, mutated in mutations:
            with self.subTest(primitive=mutated):
                self.assertIn(original, source)
                with self.assertRaisesRegex(
                    TranslationError,
                    r"(unknown global reference|expects .* operands)",
                ):
                    self.translate_source(source.replace(original, mutated, 1))

    def test_control_flow_mutation_changes_rocq_body(self) -> None:
        source = SOURCE.read_text()
        original = self.translate_source(source)[0]
        mutated = self.translate_source(
            source.replace(
                "if pointIsIdentity point then pointIdentity\n"
                "  else { x := baseNormalize point.x, y := baseNeg point.y }",
                "if pointIsIdentity point then pointNormalize point\n"
                "  else { x := baseNormalize point.x, y := baseNeg point.y }",
                1,
            )
        )[0]
        self.assertNotEqual(without_hash(original), without_hash(mutated))
        point_neg = mutated.split(
            "Definition ActionGardenZ_pointNeg", 1
        )[1].split("\n\n", 1)[0]
        self.assertIn(
            "then (ActionGardenZ_pointNormalize point)", point_neg
        )

    def test_table_cell_mutation_changes_constants_payload(self) -> None:
        source = SOURCE.read_text()
        original = self.translate_source(source)[1]
        mutated = self.translate_source(
            source.replace(
                "24448666467656506447555018649749346340705294023832615387641453784702583464707",
                "24448666467656506447555018649749346340705294023832615387641453784702583464708",
                1,
            )
        )[1]
        self.assertNotEqual(without_hash(original), without_hash(mutated))
        self.assertIn("02583464708", mutated)

    def test_sinsemilla_cell_mutation_changes_constants_payload(self) -> None:
        source = SOURCE.read_text()
        original = self.translate_source(source)[1]
        mutated = self.translate_source(
            source.replace(
                "6200097879647205583499851243213148560621730003917924543823561700220554504799",
                "6200097879647205583499851243213148560621730003917924543823561700220554504800",
                1,
            )
        )[1]
        self.assertNotEqual(without_hash(original), without_hash(mutated))
        self.assertIn("20554504800", mutated)

    def test_signed_euclidean_lowerings_are_explicit(self) -> None:
        main = self.translate_source(SOURCE.read_text())[0]
        zdiv = main.split("Definition ActionGardenZ_zDiv", 1)[1].split(
            "\n\n", 1
        )[0]
        zmod = main.split("Definition ActionGardenZ_zMod", 1)[1].split(
            "\n\n", 1
        )[0]
        self.assertIn("match divisor with | Zneg magnitude", zdiv)
        self.assertIn(
            "Z.opp (Z.div dividend (Z.pos magnitude))", zdiv
        )
        self.assertIn("match modulus with | Zneg magnitude", zmod)
        self.assertIn(
            "Z.modulo dividend (Z.pos magnitude)", zmod
        )

    def test_representation_lowerings_preserve_public_abi(self) -> None:
        main, constants = self.translate_source(SOURCE.read_text())
        self.assertIn(
            "Definition ActionGardenZ_Point : Type := "
            "ActionGardenPointData.",
            main,
        )
        self.assertIn(
            "PrimArray.array ActionGardenZ_State3", main
        )
        self.assertIn(
            "fold_left ActionGardenZ_sinsemillaRound words domain",
            main,
        )
        self.assertIn("(fst (fst element))", main)
        self.assertIn(
            "ActionGardenZ_paramsNoteCommitQ : ActionGardenZ_Point",
            main,
        )
        self.assertIn(
            "ActionGardenZ_fullAction : ActionGardenZ_ActionInputs",
            main,
        )
        self.assertEqual(
            constants.count("Build_ActionGardenState3Data "), 65
        )
        self.assertEqual(
            constants.count("Build_ActionGardenPointData "), 1025
        )

    def test_extra_import_is_rejected(self) -> None:
        source = SOURCE.read_text().replace(
            "import Init.Prelude",
            "import Init.Prelude\nimport Lean",
            1,
        )
        with self.assertRaisesRegex(
            TranslationError, "import exactly Init.Prelude"
        ):
            self.translate_source(source)

    def test_parser_valid_but_ill_typed_source_is_rejected(self) -> None:
        source = SOURCE.read_text().replace(
            "Int.add left right", "Nat.add left right", 1
        )
        with self.assertRaisesRegex(
            TranslationError, "Lean frontend rejected"
        ):
            self.translate_source(source)

    def test_unknown_global_is_rejected(self) -> None:
        source = SOURCE.read_text().replace(
            "Int.add left right", "Int.tdiv left right", 1
        )
        with self.assertRaisesRegex(
            TranslationError, "unknown global reference"
        ):
            self.translate_source(source)

    def test_unsupported_command_is_rejected(self) -> None:
        source = SOURCE.read_text().replace(
            "namespace ActionGarden",
            "namespace ActionGarden\naxiom hidden : Prop",
            1,
        )
        with self.assertRaisesRegex(
            TranslationError, "unsupported declaration kind"
        ):
            self.translate_source(source)

    def test_tactic_body_is_rejected_before_elaboration(self) -> None:
        source = SOURCE.read_text().replace(
            "def zAdd (left right : Z) : Z := Int.add left right",
            "def zAdd (left right : Z) : Z := by\n"
            "  exact Int.add left right",
            1,
        )
        with self.assertRaisesRegex(
            TranslationError, "unsupported pre-elaboration syntax"
        ):
            self.translate_source(source)

    def test_failed_generation_changes_no_destination(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            bad_source = root / "ActionGarden.lean"
            bad_source.write_text(
                SOURCE.read_text().replace(
                    "Int.add left right", "Int.tdiv left right", 1
                )
            )
            output = root / "action_garden_generated.v"
            constants = root / "action_garden_constants.v"
            diff = root / "ActionGarden.diff"
            for path in (output, constants, diff):
                path.write_text("sentinel\n")
            completed = subprocess.run(
                [
                    sys.executable,
                    str(GENERATOR),
                    str(bad_source),
                    str(output),
                    "--constants-output",
                    str(constants),
                    "--diff",
                    str(diff),
                ],
                cwd=REPOSITORY,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(completed.returncode, 0)
            for path in (output, constants, diff):
                self.assertEqual(path.read_text(), "sentinel\n")

    def test_check_mode_is_write_free(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "action_garden_generated.v"
            constants = root / "action_garden_constants.v"
            diff = root / "ActionGarden.diff"
            completed = subprocess.run(
                [
                    sys.executable,
                    str(GENERATOR),
                    str(SOURCE),
                    str(output),
                    "--constants-output",
                    str(constants),
                    "--diff",
                    str(diff),
                    "--check",
                ],
                cwd=REPOSITORY,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(completed.returncode, 0)
            self.assertFalse(output.exists())
            self.assertFalse(constants.exists())
            self.assertFalse(diff.exists())

    def test_check_rejects_body_mutation_without_rewriting(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "action_garden_generated.v"
            constants = root / "action_garden_constants.v"
            original_source = root / "ActionGarden.lean"
            original_source.write_text(SOURCE.read_text())
            subprocess.run(
                [
                    sys.executable,
                    str(GENERATOR),
                    str(original_source),
                    str(output),
                    "--constants-output",
                    str(constants),
                ],
                cwd=REPOSITORY,
                check=True,
            )
            original_output = output.read_text()
            original_constants = constants.read_text()
            original_source.write_text(
                SOURCE.read_text().replace(
                    "def zAdd (left right : Z) : Z := Int.add left right",
                    "def zAdd (left right : Z) : Z := Int.sub left right",
                    1,
                )
            )
            completed = subprocess.run(
                [
                    sys.executable,
                    str(GENERATOR),
                    str(original_source),
                    str(output),
                    "--constants-output",
                    str(constants),
                    "--check",
                ],
                cwd=REPOSITORY,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(completed.returncode, 0)
            self.assertEqual(output.read_text(), original_output)
            self.assertEqual(constants.read_text(), original_constants)


if __name__ == "__main__":
    unittest.main()
