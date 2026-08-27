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
digest, and the description's fields are compared with the derived key field by field. What the
digest cannot give is cross-key binding — that no other key hashes to it — which stays with
BLAKE2b's collision resistance, idealized like its randomness.
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

end Zcash.Snark
