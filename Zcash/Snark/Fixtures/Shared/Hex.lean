import Mathlib.Data.Nat.Notation

/-!
# Hex decoding for captured byte artifacts

The random capture families keep the fabricated proof string the deployed verifier consumed as a
`proof-bytes.hex` sibling, rendered into Lean as a hex string (each family's `ProofHex.lean`,
written by `scripts/render-proof-bytes.sh` and re-rendered and diffed by CI). `hexDecode?` turns
such a string back into bytes and accepts nothing else — an odd length or a non-hex character is
`none` — so a corrupted rendering fails the family's checks instead of decoding to some other
byte string.
-/

namespace Zcash.Snark

/-- The value of one hex digit, either case. -/
def hexDigit? (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode a hex string into bytes, two digits per byte, most significant digit first. -/
def hexDecode? (s : String) : Option (List UInt8) :=
  go s.toList
where
  /-- Decode a character list two digits at a time. -/
  go : List Char → Option (List UInt8)
    | [] => some []
    | [_] => none
    | hi :: lo :: rest => do
        let h ← hexDigit? hi
        let l ← hexDigit? lo
        let tail ← go rest
        pure (UInt8.ofNat (16 * h + l) :: tail)

example : hexDecode? "6e00Ff" = some [0x6e, 0x00, 0xff] := by decide
example : hexDecode? "6e0" = none := by decide
example : hexDecode? "6g" = none := by decide

end Zcash.Snark
