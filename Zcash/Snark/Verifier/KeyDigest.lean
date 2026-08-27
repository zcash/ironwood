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

Nothing here is trusted: the fixture checks that hashing the description reproduces the captured
digest, and `Describes` below reads the description's fields back against the key and shape it
claims to describe — the conjunct `DeployedAcceptsBytes` carries, discharged at each honest
capture and restated field by field in `Fixtures/PinnedKey.lean`. What the digest cannot give is
cross-key binding — that no other key hashes to it. That is collision resistance of the *reduced*
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

/-- Skip one `,` if present. -/
def skipComma : List Char → List Char
  | ',' :: cs => cs
  | cs => cs

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
                  (parseSeq fuel close (skipComma (skipWs rest'))).map fun q => (v :: q.1, q.2)

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
                      (parseFields fuel (skipComma (skipWs rest'))).map fun q =>
                        ((p.1, v) :: q.1, q.2)
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

/-- A hex field element in `F_p` (Vesta's scalar field). -/
def fp? (v : DebugValue) : Option Fp := (v.atom? >>= hexNat?).map fun n => (n : Fp)

/-- A hex field element in `F_q` (Vesta's base field). -/
def fq? (v : DebugValue) : Option VestaBaseField :=
  (v.atom? >>= hexNat?).map fun n => (n : VestaBaseField)

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
def columnRef? (v : DebugValue) : Option ColumnRef := do
  let i ← (v.field? "index") >>= nat?
  let t ← (v.field? "column_type") >>= atom?
  match t with
  | "Advice" => pure (.advice i)
  | "Fixed" => pure (.fixed i)
  | "Instance" => pure (.instance i)
  | _ => none

/-- A query `(Column { index: i, … }, Rotation(r))` as the verifier's `(column, rotation)`. -/
def query? (v : DebugValue) : Option (ℕ × ℤ) :=
  match v with
  | .tuple "" [c, r] => do
      let i ← (c.field? "index") >>= nat?
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

/-- A gate expression as halo2's `Expression` `Debug` prints it, in the verifier's `Expr`: the
`query_index` of a column query is what `Expr` carries. -/
def expr? : ℕ → DebugValue → Option (Expr Fp)
  | 0, _ => none
  | fuel + 1, v =>
      match v with
      | .tuple "Constant" [c] => (fp? c).map Expr.constant
      | .tuple "Negated" [e] => (expr? fuel e).map Expr.negated
      | .tuple "Sum" [a, b] => do pure (Expr.sum (← expr? fuel a) (← expr? fuel b))
      | .tuple "Product" [a, b] => do pure (Expr.product (← expr? fuel a) (← expr? fuel b))
      | .tuple "Scaled" [e, c] => do pure (Expr.scaled (← expr? fuel e) (← fp? c))
      | .struct "Fixed" _ => ((v.field? "query_index") >>= nat?).map Expr.fixed
      | .struct "Advice" _ => ((v.field? "query_index") >>= nat?).map Expr.advice
      | .struct "Instance" _ => ((v.field? "query_index") >>= nat?).map Expr.instance
      | _ => none

/-- Map a parser over a list value. -/
def listOf? {α : Type} (f : DebugValue → Option α) (v : DebugValue) : Option (List α) :=
  (items? v).bind fun xs => xs.mapM f

/-- `Argument { input_expressions: [...], table_expressions: [...] }` as the verifier's lookup
expression lists. -/
def lookup? (fuel : ℕ) (v : DebugValue) : Option (List (Expr Fp) × List (Expr Fp)) := do
  let inputs ← (v.field? "input_expressions") >>= listOf? (expr? fuel)
  let tables ← (v.field? "table_expressions") >>= listOf? (expr? fuel)
  pure (inputs, tables)

end DebugValue

/-! ## The description against a key

`Describes` is the identification `DeployedAcceptsBytes` requires between the description whose
digest opens the transcript and the key the proof is checked against: the description's
constraint system is the key's, and the counts `readProof?` reads by are that constraint
system's. -/

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

/-- **The description describes the key.** Every pinned field with a counterpart in the verifier's
key or shape reads back to it: the moduli name Vesta's fields; the domain's `k` and `ω` are the
shape's and the key's, with `n` the domain size `2 ^ k`; the column counts are the shape's; the
gates, query layouts, permutation columns (through `toQuerySpace`), and lookups are the key's; and
both commitment vectors are the key's, the fixed one over the pinned column count. The shape's
query, permutation-set, and lookup counts are tied to those same pinned fields, so the counts
`readProof?` reads by are the pinned constraint system's — the agreements `Verifier/Key.lean`
names.

Not read here, because the verifier consumes no pinned counterpart: `blindingFactors`, `delta`,
and `chunkLen`, halo2 constants of the constraint system's degree that stay the named key
agreements of `Verifier/Key.lean`; and the keygen-only `extended_k`, `num_selectors`, `constants`,
and `minimum_degree`, pinned as deployment literals in `Fixtures/PinnedKey.lean`. -/
def Describes {shape : CircuitShape} (s : String) (vk : VerifyingKey shape Fp VestaG) : Prop :=
  ((descriptionValue s).field? "base_modulus" >>= quotedHexNat?) = some PALLAS_SCALAR_CARD ∧
  ((descriptionValue s).field? "scalar_modulus" >>= quotedHexNat?) = some PALLAS_BASE_CARD ∧
  ((descriptionDomain s).field? "k" >>= nat?) = some shape.k ∧
  vk.n = 2 ^ shape.k ∧
  ((descriptionDomain s).field? "omega" >>= fp?) = some vk.omega ∧
  ((descriptionCs s).field? "num_advice_columns" >>= nat?) = some shape.numAdviceColumns ∧
  ((descriptionCs s).field? "num_instance_columns" >>= nat?) = some shape.numInstanceColumns ∧
  ((descriptionCs s).field? "gates" >>= listOf? (expr? (descriptionFuel s))) = some vk.gates ∧
  ((descriptionCs s).field? "advice_queries" >>= listOf? query?) = some vk.adviceQueryLayout ∧
  ((descriptionCs s).field? "instance_queries" >>= listOf? query?) = some vk.instanceQueryLayout ∧
  ((descriptionCs s).field? "fixed_queries" >>= listOf? query?) = some vk.fixedQueryLayout ∧
  vk.adviceQueryLayout.length = shape.numAdviceQueries ∧
  vk.instanceQueryLayout.length = shape.numInstanceQueries ∧
  vk.fixedQueryLayout.length = shape.numFixedQueries ∧
  ((((descriptionCs s).field? "permutation" >>= (·.field? "columns")) >>= listOf? columnRef?)
      >>= fun l => l.mapM (toQuerySpace vk))
    = some (vk.permutationChunks.flatten.map Prod.fst) ∧
  vk.permutationChunks.length = shape.numPermutationSets ∧
  ((descriptionCs s).field? "lookups" >>= listOf? (lookup? (descriptionFuel s)))
    = some (List.ofFn fun l : Fin shape.numLookups =>
        (vk.lookupInputExprs l, vk.lookupTableExprs l)) ∧
  ((descriptionCs s).field? "num_fixed_columns" >>= nat?) ≠ none ∧
  ((descriptionValue s).field? "fixed_commitments" >>= listOf? point?)
    = ((descriptionCs s).field? "num_fixed_columns" >>= nat?).map
        (fun n => (List.range n).map vk.fixedCommitment) ∧
  (((descriptionValue s).field? "permutation" >>= (·.field? "commitments")) >>= listOf? point?)
    = some (List.ofFn vk.permutationCommonCommitment)

/-- `Describes` is a finite conjunction of decidable equations, so a capture discharges it by
evaluation. -/
instance decidableDescribes {shape : CircuitShape} (s : String)
    (vk : VerifyingKey shape Fp VestaG) : Decidable (Describes s vk) := by
  unfold Describes
  infer_instance

end Zcash.Snark
