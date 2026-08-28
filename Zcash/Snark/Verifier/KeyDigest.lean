import Zcash.Snark.Verifier.Transcript
import Zcash.Snark.Verifier.Key

/-!
# Halo2's verifying-key digest

The first element halo2 absorbs into the Fiat–Shamir transcript is `transcript_repr`, the
verifying key's digest. `VerifyingKey::from_parts` computes it as BLAKE2b-512, personalized
`Halo2-Verify-Key`, over the key's *pinned description* — the compact `Debug` rendering of
`PinnedVerificationKey` — prefixed by that text's byte length as a little-endian `u64`, and
reduces the digest modulo `p` exactly as a squeeze does. This module recomputes it (`keyDigest`)
and reads the pinned description back into the verifier's own vocabulary, so the digest that
opens the transcript can be checked to be the digest of the key Lean derives rather than a
captured scalar.

The description is Rust's derived-`Debug` value language: atoms (identifiers, numbers,
`0x`-hex, quoted strings), `Name { field: value, … }` structs, `Name(a, b)` tuples, bare
`(a, b)` tuples, and `[a, b]` lists. `DebugValue.parse?` reads it with whitespace ignored, so
both the compact form that is hashed and the pretty form orchard commits parse to the same
tree; `DebugValue.renderCompact` writes the compact form back, which is what `{:?}` prints for
these shapes: `Name { f: v, g: w }`, `Name(a, b)`, `[a, b]`, and a bare `Name` for a
field-less struct or argument-less tuple. The extractors at the end turn the pinned fields into
`Expr`, `ColumnRef`, query layouts, and Vesta points — the shapes `VerifyingKey` carries.

The parser and digest computation are checked, but the exporter-emitted string remains a deployment
input: the fixture checks that hashing that exact string reproduces the captured digest, and
`Describes` below relates its represented fields to a designated canonical key and the key used by
the verifier. It does not reconstruct Rust's unique `Debug` output from a key. In particular,
proof-reader dimensions and printed keygen-only values have separate provenance, stated below
and checked for the capture in `Fixtures/PinnedKey.lean`. What the digest cannot give is cross-key
binding — that no other key hashes to it. That is collision resistance of the *reduced*
digest `keyDigest`, BLAKE2b's 512-bit output taken modulo `p`: two descriptions whose digests are
merely congruent modulo `p` share a key digest with no BLAKE2b collision
(`challengeOfDigest_eq_iff_modEq`), so bare BLAKE2b collision resistance does not imply it. Under
the random-oracle idealization the squeeze already takes, it holds at the usual birthday bound; it
is idealized like BLAKE2b's randomness, not proved.
-/

namespace Zcash.Snark

open CompElliptic CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta
open Zcash.Common

/-! ## The digest -/

/-- The ASCII bytes of `Halo2-Verify-Key`, the key digest's BLAKE2b personalization. -/
def verifyKeyPersonal : Vector UInt8 16 :=
  #v[0x48, 0x61, 0x6c, 0x6f, 0x32, 0x2d, 0x56, 0x65, 0x72, 0x69, 0x66, 0x79, 0x2d, 0x4b, 0x65, 0x79]

/-- `u64::to_le_bytes`: eight little-endian bytes of `n`. -/
def u64LE (n : ℕ) : List UInt8 :=
  (List.range 8).map fun i => UInt8.ofNat (n / 256 ^ i % 256)

/-- What `from_parts` hashes: the description's byte length as a little-endian `u64`, then its
bytes. -/
def keyDigestPreimage (s : String) : List UInt8 :=
  u64LE s.utf8ByteSize ++ s.toUTF8.toList

/-- `transcript_repr` from the pinned description: BLAKE2b-512 under `Halo2-Verify-Key` over the
length-prefixed text, reduced modulo `p` by `from_uniform_bytes`. -/
def keyDigest (s : String) : Fp :=
  challengeOfDigest (Blake2b.digest64 verifyKeyPersonal (keyDigestPreimage s))

/-! ## Rust's `Debug` value language -/

/-- A value as Rust's derived `Debug` prints it. A quoted string is an `atom` that keeps its
quotes; a bare `(a, b)` is a `tuple` with the empty name. -/
inductive DebugValue where
  | atom : String → DebugValue
  | struct : String → List (String × DebugValue) → DebugValue
  | tuple : String → List DebugValue → DebugValue
  | list : List DebugValue → DebugValue
deriving Repr

namespace DebugValue

/-- Whitespace, which the pretty form inserts freely and the compact form does not. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\r' || c == '\t'

/-- The characters that end a bare token. -/
def isDelim (c : Char) : Bool :=
  isWs c || c == ',' || c == '(' || c == ')' || c == '{' || c == '}' || c == '[' || c == ']'
    || c == ':'

/-- Drop leading whitespace. -/
def skipWs : List Char → List Char
  | c :: cs => if isWs c then skipWs cs else c :: cs
  | [] => []

/-- Read a bare token up to the next delimiter. -/
def takeTok : List Char → List Char → String × List Char
  | acc, c :: cs =>
      if isDelim c then (String.ofList acc.reverse, c :: cs) else takeTok (c :: acc) cs
  | acc, [] => (String.ofList acc.reverse, [])

/-- Read a quoted string literal, quotes included, honouring `\` escapes; `none` if unterminated. -/
def takeStringLit : List Char → List Char → Option (String × List Char)
  | acc, '\\' :: c :: cs => takeStringLit (c :: '\\' :: acc) cs
  | acc, '"' :: cs => some (String.ofList ('"' :: acc).reverse, cs)
  | acc, c :: cs => takeStringLit (c :: acc) cs
  | _, [] => none

mutual
  /-- Parse one value; the fuel bounds recursion and one unit per element or nesting suffices. -/
  def parseValue : ℕ → List Char → Option (DebugValue × List Char)
    | 0, _ => none
    | fuel + 1, cs =>
        match skipWs cs with
        | '"' :: rest => (takeStringLit ['"'] rest).map fun p => (.atom p.1, p.2)
        | '[' :: rest => (parseSeq fuel ']' rest).map fun p => (.list p.1, p.2)
        | '(' :: rest => (parseSeq fuel ')' rest).map fun p => (.tuple "" p.1, p.2)
        | cs' =>
            let p := takeTok [] cs'
            if p.1.isEmpty then none
            else
              match skipWs p.2 with
              | '{' :: rest => (parseFields fuel rest).map fun q => (.struct p.1 q.1, q.2)
              | '(' :: rest => (parseSeq fuel ')' rest).map fun q => (.tuple p.1 q.1, q.2)
              | _ => some (.atom p.1, p.2)

  /-- Parse comma-separated values up to `close`, a trailing comma allowed. -/
  def parseSeq : ℕ → Char → List Char → Option (List DebugValue × List Char)
    | 0, _, _ => none
    | fuel + 1, close, cs =>
        match skipWs cs with
        | [] => none
        | c :: rest =>
            if c == close then some ([], rest)
            else
              match parseValue fuel (c :: rest) with
              | none => none
              | some (v, rest') =>
                  match skipWs rest' with
                  | ',' :: rest'' =>
                      (parseSeq fuel close rest'').map fun q => (v :: q.1, q.2)
                  | c' :: rest'' =>
                      if c' == close then some ([v], rest'') else none
                  | [] => none

  /-- Parse `field: value` pairs up to `}`, a trailing comma allowed. -/
  def parseFields : ℕ → List Char → Option (List (String × DebugValue) × List Char)
    | 0, _ => none
    | fuel + 1, cs =>
        match skipWs cs with
        | [] => none
        | '}' :: rest => some ([], rest)
        | cs' =>
            let p := takeTok [] cs'
            if p.1.isEmpty then none
            else
              match skipWs p.2 with
              | ':' :: rest =>
                  match parseValue fuel rest with
                  | none => none
                  | some (v, rest') =>
                      match skipWs rest' with
                      | ',' :: rest'' =>
                          (parseFields fuel rest'').map fun q => ((p.1, v) :: q.1, q.2)
                      | '}' :: rest'' => some ([(p.1, v)], rest'')
                      | _ => none
              | _ => none
end

/-- Parse a whole description; `none` unless exactly one value spans the text. -/
def parse? (s : String) : Option DebugValue :=
  match parseValue (s.length + 1) s.toList with
  | some (v, rest) => if (skipWs rest).isEmpty then some v else none
  | none => none

mutual
  /-- The compact `{:?}` rendering. -/
  def renderCompact : DebugValue → String
    | .atom s => s
    | .list xs => "[" ++ ", ".intercalate (renderList xs) ++ "]"
    | .tuple name xs =>
        if xs.isEmpty && !name.isEmpty then name
        else name ++ "(" ++ ", ".intercalate (renderList xs) ++ ")"
    | .struct name fs =>
        if fs.isEmpty then name else name ++ " { " ++ ", ".intercalate (renderFields fs) ++ " }"

  /-- Render list elements. -/
  def renderList : List DebugValue → List String
    | [] => []
    | v :: vs => renderCompact v :: renderList vs

  /-- Render `field: value` pairs. -/
  def renderFields : List (String × DebugValue) → List String
    | [] => []
    | (f, v) :: fs => (f ++ ": " ++ renderCompact v) :: renderFields fs
end

/-! ## Reading the pinned fields -/

/-- The value of field `name` of a struct. -/
def field? (v : DebugValue) (name : String) : Option DebugValue :=
  match v with
  | .struct _ fs => (fs.find? fun p => p.1 == name).map (·.2)
  | _ => none

/-- A structure has exactly the expected Rust type name and field-name sequence. Besides pinning
derived-`Debug`'s field order, this excludes duplicate and unknown fields before `field?` is used. -/
def hasStructFields (v : DebugValue) (typeName : String) (fieldNames : List String) : Prop :=
  match v with
  | .struct actual fields => actual = typeName ∧ fields.map Prod.fst = fieldNames
  | _ => False

instance (v : DebugValue) (typeName : String) (fieldNames : List String) :
    Decidable (hasStructFields v typeName fieldNames) := by
  cases v with
  | atom _ => exact isFalse id
  | tuple _ _ => exact isFalse id
  | list _ => exact isFalse id
  | struct actual fields =>
      simp only [hasStructFields]
      infer_instance

/-- The text of an atom. -/
def atom? : DebugValue → Option String
  | .atom s => some s
  | _ => none

/-- The elements of a list. -/
def items? : DebugValue → Option (List DebugValue)
  | .list xs => some xs
  | _ => none

/-- The value of one hex digit. -/
def hexDigitVal? (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- A `0x`-prefixed lowercase hex literal as `pasta_curves` prints field elements (most significant
digit first). -/
def hexNat? (s : String) : Option ℕ :=
  match s.toList with
  | '0' :: 'x' :: ds =>
      if ds.isEmpty then none
      else ds.foldl (fun acc c => do let a ← acc; let d ← hexDigitVal? c; pure (16 * a + d)) (some 0)
  | _ => none

/-- A decimal natural. -/
def decNat? (s : String) : Option ℕ :=
  if s.isEmpty then none
  else s.toList.foldl (fun acc c => do
    let a ← acc
    if '0' ≤ c ∧ c ≤ '9' then pure (10 * a + (c.toNat - '0'.toNat)) else none) (some 0)

/-- A decimal integer, `-` allowed. -/
def decInt? (s : String) : Option ℤ :=
  match s.toList with
  | '-' :: ds => (decNat? (String.ofList ds)).map fun n => -(n : ℤ)
  | _ => (decNat? s).map fun n => (n : ℤ)

/-- A natural-number atom. -/
def nat? (v : DebugValue) : Option ℕ := v.atom? >>= decNat?

/-- A canonical 32-byte field `Debug` literal: exactly 64 lowercase hexadecimal digits and a
value strictly below `modulus`. This rejects the modulo-reduction aliases that a plain cast to
`ZMod` would otherwise accept. -/
def canonicalFieldNat? (modulus : ℕ) (v : DebugValue) : Option ℕ := do
  let s ← v.atom?
  if s.length = 66 then
    let n ← hexNat? s
    if n < modulus then some n else none
  else none

/-- A canonical hex field element in `F_p` (Vesta's scalar field). -/
def fp? (v : DebugValue) : Option Fp :=
  (canonicalFieldNat? PALLAS_BASE_CARD v).map fun n => (n : Fp)

/-- A canonical hex field element in `F_q` (Vesta's base field). -/
def fq? (v : DebugValue) : Option VestaBaseField :=
  (canonicalFieldNat? PALLAS_SCALAR_CARD v).map fun n => (n : VestaBaseField)

/-- A quoted modulus string as the number it names. -/
def quotedHexNat? (v : DebugValue) : Option ℕ := do
  let s ← v.atom?
  let cs := s.toList
  match cs with
  | '"' :: rest => hexNat? (String.ofList (rest.dropLast))
  | _ => none

/-- `Rotation(r)`. -/
def rotation? (v : DebugValue) : Option ℤ :=
  match v with
  | .tuple "Rotation" [r] => r.atom? >>= decInt?
  | _ => none

/-- `Column { index: i, column_type: Advice | Fixed | Instance }` as a `ColumnRef`. -/
def columnRef? (v : DebugValue) : Option ColumnRef :=
  match v with
  | .struct "Column" [("index", i), ("column_type", t)] => do
      let i ← nat? i
      let t ← atom? t
      match t with
      | "Advice" => pure (.advice i)
      | "Fixed" => pure (.fixed i)
      | "Instance" => pure (.instance i)
      | _ => none
  | _ => none

/-- A query `(Column { index: i, column_type: expected }, Rotation(r))` as the verifier's
`(column, rotation)`. Requiring the expected column type prevents one query family from being
accepted under another family's layout. -/
def query? (expected : String) (v : DebugValue) : Option (ℕ × ℤ) :=
  match v with
  | .tuple "" [c, r] => do
      let cr ← columnRef? c
      let i ← match expected, cr with
        | "Advice", .advice i => some i
        | "Fixed", .fixed i => some i
        | "Instance", .instance i => some i
        | _, _ => none
      let rot ← rotation? r
      pure (i, rot)
  | _ => none

/-- An affine Vesta point `(x, y)` with a curve check; the identity prints as `Infinity` and is
refused. -/
def point? (v : DebugValue) : Option VestaG :=
  match v with
  | .tuple "" [x, y] => do
      let xv ← fq? x
      let yv ← fq? y
      if h : OnCurve Vesta.a Vesta.b (xv, yv) then pure ⟨xv, yv, Or.inl h⟩ else none
  | _ => none

/-- A gate expression as halo2's `Expression` `Debug` prints it, in the verifier's `Expr`. For a
column query, the redundant printed `column_index` and `rotation` must agree with the layout entry
selected by `query_index`; accepting only the latter would leave hashed key data unchecked. -/
def expr? (instanceLayout adviceLayout fixedLayout : List (ℕ × ℤ)) :
    ℕ → DebugValue → Option (Expr Fp)
  | 0, _ => none
  | fuel + 1, v =>
      match v with
      | .tuple "Constant" [c] => (fp? c).map Expr.constant
      | .tuple "Negated" [e] =>
          (expr? instanceLayout adviceLayout fixedLayout fuel e).map Expr.negated
      | .tuple "Sum" [a, b] => do
          pure (Expr.sum
            (← expr? instanceLayout adviceLayout fixedLayout fuel a)
            (← expr? instanceLayout adviceLayout fixedLayout fuel b))
      | .tuple "Product" [a, b] => do
          pure (Expr.product
            (← expr? instanceLayout adviceLayout fixedLayout fuel a)
            (← expr? instanceLayout adviceLayout fixedLayout fuel b))
      | .tuple "Scaled" [e, c] => do
          pure (Expr.scaled
            (← expr? instanceLayout adviceLayout fixedLayout fuel e) (← fp? c))
      | .struct "Fixed"
          [("query_index", qi), ("column_index", column), ("rotation", rotation)] => do
          let qi ← nat? qi
          let q := (← columnRef? (.struct "Column"
            [("index", column), ("column_type", .atom "Fixed")]))
          let rot ← rotation? rotation
          match q with
          | .fixed column =>
              if fixedLayout[qi]? = some (column, rot) then some (.fixed qi) else none
          | _ => none
      | .struct "Advice"
          [("query_index", qi), ("column_index", column), ("rotation", rotation)] => do
          let qi ← nat? qi
          let q := (← columnRef? (.struct "Column"
            [("index", column), ("column_type", .atom "Advice")]))
          let rot ← rotation? rotation
          match q with
          | .advice column =>
              if adviceLayout[qi]? = some (column, rot) then some (.advice qi) else none
          | _ => none
      | .struct "Instance"
          [("query_index", qi), ("column_index", column), ("rotation", rotation)] => do
          let qi ← nat? qi
          let q := (← columnRef? (.struct "Column"
            [("index", column), ("column_type", .atom "Instance")]))
          let rot ← rotation? rotation
          match q with
          | .instance column =>
              if instanceLayout[qi]? = some (column, rot) then some (.instance qi) else none
          | _ => none
      | _ => none

/-- Map a parser over a list value. -/
def listOf? {α : Type} (f : DebugValue → Option α) (v : DebugValue) : Option (List α) :=
  (items? v).bind fun xs => xs.mapM f

/-- `Argument { input_expressions: [...], table_expressions: [...] }` as the verifier's lookup
expression lists. -/
def lookup? (instanceLayout adviceLayout fixedLayout : List (ℕ × ℤ))
    (fuel : ℕ) (v : DebugValue) : Option (List (Expr Fp) × List (Expr Fp)) :=
  match v with
  | .struct "Argument"
      [("input_expressions", inputs), ("table_expressions", tables)] => do
      let inputs ← listOf? (expr? instanceLayout adviceLayout fixedLayout fuel) inputs
      let tables ← listOf? (expr? instanceLayout adviceLayout fixedLayout fuel) tables
      pure (inputs, tables)
  | _ => none

end DebugValue

/-! ## The description against a designated canonical and verifier-used key

Halo2's `PinnedVerificationKey` description intentionally omits verifier-active values that it
reconstructs from the constraint system, including the blinding count, permutation delta, chunk
width, and common-evaluation indices. Consequently no predicate over only the description and an
arbitrary `VerifyingKey` can identify those fields. `Describes` therefore takes two keys: the key
designated canonical by its caller and the key actually used by the verifier. It checks the
description against every represented field of the first and separately requires behavioral
agreement of every field the Lean verifier consumes. The Action instantiation supplies its first
key from the circuit-derived keygen pipeline.

This relation does not derive every `readProof?` dimension from the description. In particular,
`numQuotientPieces` and the invocation-specific `numPointSets` come from `Shape` rather than a
printed field. `numPermutationSets` is checked against `permutationChunks.length`, while the
chunk width and partition regularity come from the circuit-derived key. Those are named deployment
shape agreements, not consequences of parsing the description. -/

open DebugValue

/-- The parsed description; a failed parse falls back to the field-less empty atom, which
satisfies none of the `some`-valued reads below. -/
def descriptionValue (s : String) : DebugValue := (parse? s).getD (.atom "")

/-- The `cs` (constraint system) field of the parsed description. -/
def descriptionCs (s : String) : DebugValue := ((descriptionValue s).field? "cs").getD (.atom "")

/-- The `domain` field of the parsed description. -/
def descriptionDomain (s : String) : DebugValue :=
  ((descriptionValue s).field? "domain").getD (.atom "")

/-- Recursion budget for reading expressions: one unit per character bounds every nesting. -/
def descriptionFuel (s : String) : ℕ := s.length

/-- The first query of raw column `c` at rotation 0 in the layout `l` — halo2's
`get_any_query_index(column, Rotation::cur())`, which is how `permutation::verifier` locates
the evaluation of a permutation column. -/
def queryIndexAt (l : List (ℕ × ℤ)) (c : ℕ) : Option ℕ := l.findIdx? (· = (c, 0))

/-- A pinned permutation column, moved from the description's raw column space into the
verifier's query-index space — the vocabulary `permutationChunks` speaks — through the key's
query layouts, themselves compared with the pinned ones by `Describes`. -/
def toQuerySpace {shape : CircuitShape} (vk : VerifyingKey shape Fp VestaG) :
    ColumnRef → Option ColumnRef
  | .advice c => (queryIndexAt vk.adviceQueryLayout c).map .advice
  | .fixed c => (queryIndexAt vk.fixedQueryLayout c).map .fixed
  | .instance c => (queryIndexAt vk.instanceQueryLayout c).map .instance

/-- **Behavioral equality of verifier keys.** Every field consumed by `validateInstances?`,
`deriveChallengesForStatement`, or `assemble?` agrees. Function-valued commitment fields are
compared over exactly the finite layouts the verifier can reach. This is stronger than comparing
only fields printed by `PinnedVerificationKey`: in particular it binds `blindingFactors`, `delta`,
`chunkLen`, the permutation chunk partition, and every common-evaluation index. -/
def VerifyingKeyAgrees {shape : CircuitShape}
    (canonical used : VerifyingKey shape Fp VestaG) : Prop :=
  canonical.omega = used.omega ∧
  canonical.n = used.n ∧
  canonical.blindingFactors = used.blindingFactors ∧
  canonical.delta = used.delta ∧
  canonical.chunkLen = used.chunkLen ∧
  canonical.gates = used.gates ∧
  canonical.instanceQueryLayout = used.instanceQueryLayout ∧
  canonical.adviceQueryLayout = used.adviceQueryLayout ∧
  canonical.fixedQueryLayout = used.fixedQueryLayout ∧
  canonical.fixedQueryLayout.map (fun q => canonical.fixedCommitment q.1) =
    used.fixedQueryLayout.map (fun q => used.fixedCommitment q.1) ∧
  List.ofFn canonical.permutationCommonCommitment =
    List.ofFn used.permutationCommonCommitment ∧
  canonical.permutationChunks = used.permutationChunks ∧
  (List.ofFn fun l : Fin shape.numLookups =>
      (canonical.lookupInputExprs l, canonical.lookupTableExprs l)) =
    (List.ofFn fun l : Fin shape.numLookups =>
      (used.lookupInputExprs l, used.lookupTableExprs l))

/-- Behavioral key agreement is reflexive. -/
theorem verifyingKeyAgrees_refl {shape : CircuitShape}
    (vk : VerifyingKey shape Fp VestaG) : VerifyingKeyAgrees vk vk := by
  simp [VerifyingKeyAgrees]

/-- The description is one exact compact derived-`Debug` value with the expected nested struct
names and field sequences. -/
def DescriptionSyntaxCanonical (s : String) : Prop :=
  (parse? s).isSome = true ∧
  renderCompact (descriptionValue s) = s ∧
  hasStructFields (descriptionValue s) "PinnedVerificationKey"
    ["base_modulus", "scalar_modulus", "domain", "cs", "fixed_commitments", "permutation"] ∧
  hasStructFields (descriptionDomain s) "PinnedEvaluationDomain" ["k", "extended_k", "omega"] ∧
  hasStructFields (descriptionCs s) "PinnedConstraintSystem"
    ["num_fixed_columns", "num_advice_columns", "num_instance_columns", "num_selectors", "gates",
      "advice_queries", "instance_queries", "fixed_queries", "permutation", "lookups",
      "constants", "minimum_degree"] ∧
  hasStructFields (((descriptionCs s).field? "permutation").getD (.atom ""))
    "Argument" ["columns"] ∧
  hasStructFields (((descriptionValue s).field? "permutation").getD (.atom ""))
    "VerifyingKey" ["commitments"]

/-- Moduli, domain, shape, gates, and typed query layouts represented by the description. -/
def DescriptionCoreFieldsMatch {shape : CircuitShape}
    (s : String) (vk : VerifyingKey shape Fp VestaG) : Prop :=
  ((descriptionValue s).field? "base_modulus" >>= quotedHexNat?) = some PALLAS_SCALAR_CARD ∧
  ((descriptionValue s).field? "scalar_modulus" >>= quotedHexNat?) = some PALLAS_BASE_CARD ∧
  ((descriptionDomain s).field? "k" >>= nat?) = some shape.k ∧
  vk.n = 2 ^ shape.k ∧
  ((descriptionDomain s).field? "omega" >>= fp?) = some vk.omega ∧
  ((descriptionCs s).field? "num_advice_columns" >>= nat?) = some shape.numAdviceColumns ∧
  ((descriptionCs s).field? "num_instance_columns" >>= nat?) = some shape.numInstanceColumns ∧
  ((descriptionCs s).field? "gates" >>= listOf?
      (expr? vk.instanceQueryLayout vk.adviceQueryLayout vk.fixedQueryLayout
        (descriptionFuel s))) = some vk.gates ∧
  ((descriptionCs s).field? "advice_queries" >>= listOf? (query? "Advice")) =
    some vk.adviceQueryLayout ∧
  ((descriptionCs s).field? "instance_queries" >>= listOf? (query? "Instance")) =
    some vk.instanceQueryLayout ∧
  ((descriptionCs s).field? "fixed_queries" >>= listOf? (query? "Fixed")) =
    some vk.fixedQueryLayout ∧
  vk.adviceQueryLayout.length = shape.numAdviceQueries ∧
  vk.instanceQueryLayout.length = shape.numInstanceQueries ∧
  vk.fixedQueryLayout.length = shape.numFixedQueries

/-- Permutation columns and lookup expressions represented by the description. -/
def DescriptionArgumentFieldsMatch {shape : CircuitShape}
    (s : String) (vk : VerifyingKey shape Fp VestaG) : Prop :=
  ((((descriptionCs s).field? "permutation" >>= (·.field? "columns")) >>= listOf? columnRef?)
      >>= fun l => l.mapM (toQuerySpace vk))
    = some (vk.permutationChunks.flatten.map Prod.fst) ∧
  vk.permutationChunks.length = shape.numPermutationSets ∧
  ((descriptionCs s).field? "lookups" >>= listOf?
      (lookup? vk.instanceQueryLayout vk.adviceQueryLayout vk.fixedQueryLayout
        (descriptionFuel s)))
    = some (List.ofFn fun l : Fin shape.numLookups =>
        (vk.lookupInputExprs l, vk.lookupTableExprs l))

/-- Fixed and permutation commitment vectors represented by the description. -/
def DescriptionCommitmentsMatch {shape : CircuitShape}
    (s : String) (vk : VerifyingKey shape Fp VestaG) : Prop :=
  ((descriptionCs s).field? "num_fixed_columns" >>= nat?) ≠ none ∧
  ((descriptionValue s).field? "fixed_commitments" >>= listOf? point?)
    = ((descriptionCs s).field? "num_fixed_columns" >>= nat?).map
        (fun n => (List.range n).map vk.fixedCommitment) ∧
  (((descriptionValue s).field? "permutation" >>= (·.field? "commitments")) >>= listOf? point?)
    = some (List.ofFn vk.permutationCommonCommitment)

/-- Every represented verifier field of a designated canonical key is read from an exact compact
Rust `Debug` description. The grammar checks above reject missing commas, noncanonical field values,
wrong query column types, inconsistent query metadata, duplicate/unknown top-level fields, and
trailing text. Keygen-only fields remain part of the exact hashed string but have no verifier-side
counterpart; concrete deployment pins their values and the exporter-emitted string separately.
Thus this predicate validates *a* description of the key; it does not compute Rust's unique
description from the key. -/
def DescriptionFieldsMatch {shape : CircuitShape}
    (s : String) (vk : VerifyingKey shape Fp VestaG) : Prop :=
  DescriptionSyntaxCanonical s ∧
  DescriptionCoreFieldsMatch s vk ∧
  DescriptionArgumentFieldsMatch s vk ∧
  DescriptionCommitmentsMatch s vk

/-- **Relate a description, a designated canonical key, and the verifier-used key.** The
description matches every represented field of the designated key, while the actual key agrees
with that key on every verifier-reachable field. The explicit canonical argument is necessary
because Halo2 omits several reconstructed runtime fields from `PinnedVerificationKey`; its
circuit-derived provenance and the exact exporter string are separate deployment facts. -/
def Describes {shape : CircuitShape} (s : String)
    (canonical used : VerifyingKey shape Fp VestaG) : Prop :=
  DescriptionFieldsMatch s canonical ∧ VerifyingKeyAgrees canonical used

/-- `Describes` is a finite conjunction of decidable equations, so captures and key mutations can
be checked by evaluation. -/
instance decidableVerifyingKeyAgrees {shape : CircuitShape}
    (canonical used : VerifyingKey shape Fp VestaG) :
    Decidable (VerifyingKeyAgrees canonical used) := by
  unfold VerifyingKeyAgrees
  infer_instance

instance decidableDescriptionSyntaxCanonical (s : String) :
    Decidable (DescriptionSyntaxCanonical s) := by
  unfold DescriptionSyntaxCanonical
  infer_instance

instance decidableDescriptionCoreFieldsMatch {shape : CircuitShape} (s : String)
    (vk : VerifyingKey shape Fp VestaG) : Decidable (DescriptionCoreFieldsMatch s vk) := by
  unfold DescriptionCoreFieldsMatch
  infer_instance

instance decidableDescriptionArgumentFieldsMatch {shape : CircuitShape} (s : String)
    (vk : VerifyingKey shape Fp VestaG) : Decidable (DescriptionArgumentFieldsMatch s vk) := by
  unfold DescriptionArgumentFieldsMatch
  infer_instance

instance decidableDescriptionCommitmentsMatch {shape : CircuitShape} (s : String)
    (vk : VerifyingKey shape Fp VestaG) : Decidable (DescriptionCommitmentsMatch s vk) := by
  unfold DescriptionCommitmentsMatch
  infer_instance

instance decidableDescriptionFieldsMatch {shape : CircuitShape} (s : String)
    (vk : VerifyingKey shape Fp VestaG) : Decidable (DescriptionFieldsMatch s vk) := by
  unfold DescriptionFieldsMatch
  infer_instance

instance decidableDescribes {shape : CircuitShape} (s : String)
    (canonical used : VerifyingKey shape Fp VestaG) : Decidable (Describes s canonical used) := by
  unfold Describes
  infer_instance

/-- A described verifier uses the canonical blinding count. -/
theorem Describes.blindingFactors_eq {shape : CircuitShape} {s : String}
    {canonical used : VerifyingKey shape Fp VestaG} (h : Describes s canonical used) :
    canonical.blindingFactors = used.blindingFactors :=
  h.2.2.2.1

/-- A described verifier uses the canonical permutation delta. -/
theorem Describes.delta_eq {shape : CircuitShape} {s : String}
    {canonical used : VerifyingKey shape Fp VestaG} (h : Describes s canonical used) :
    canonical.delta = used.delta :=
  h.2.2.2.2.1

/-- A described verifier uses the canonical permutation chunk width. -/
theorem Describes.chunkLen_eq {shape : CircuitShape} {s : String}
    {canonical used : VerifyingKey shape Fp VestaG} (h : Describes s canonical used) :
    canonical.chunkLen = used.chunkLen :=
  h.2.2.2.2.2.1

/-- A described verifier uses the canonical chunk partition and common-evaluation indices. -/
theorem Describes.permutationChunks_eq {shape : CircuitShape} {s : String}
    {canonical used : VerifyingKey shape Fp VestaG} (h : Describes s canonical used) :
    canonical.permutationChunks = used.permutationChunks :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! Parser hardening regressions. -/

example : parse? "Pair(1 2)" = none := by decide +kernel

example : query? "Advice"
    (.tuple "" [.struct "Column" [("index", .atom "0"), ("column_type", .atom "Fixed")],
      .tuple "Rotation" [.atom "0"]]) = none := by
  decide +kernel

example : canonicalFieldNat? PALLAS_BASE_CARD
    (.atom "0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001") = none := by
  decide +kernel

example : fq?
    (.atom "0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001") = none := by
  decide +kernel

end Zcash.Snark
