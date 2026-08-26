import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.TypeStar

/-!
# BLAKE2b

An executable BLAKE2b (RFC 7693) over `UInt64` words, in the one parameter configuration halo2's
Fiat–Shamir transcript uses: the full 64-byte digest, a 16-byte personalization, no key, no salt,
and the sequential (fanout 1, depth 1) mode. The deployed transcript hashes with `blake2b_simd`; this module
lets Lean recompute those digests, so the byte layer beneath the typed challenge schedule can be
checked against the captured runs instead of idealized away.

Everything here is a total function on lists and fixed-length vectors — no `IO`, no `extern`, no
`implemented_by` — so the kernel and compiled evaluation compute the same definitions. The
known-answer checks at the end pin the implementation to RFC 7693's test vector and to digests of
the halo2-personalized configuration produced independently by Python's `hashlib`.

## References

* M-J. Saarinen, J-P. Aumasson, "The BLAKE2 Cryptographic Hash and Message Authentication Code
  (MAC)", RFC 7693, <https://www.rfc-editor.org/rfc/rfc7693>.
* The parameter block (digest length, key length, fanout, depth, leaf length, node offset, node
  depth, inner length, salt, personalization) follows the BLAKE2 specification,
  <https://www.blake2.net/blake2.pdf>, §2.8, as `blake2b_simd::Params` lays it out.
-/

namespace Zcash.Common.Blake2b

/-- Replace entry `i` of a fixed-length vector. -/
def upd {α : Type*} {n : ℕ} (v : Vector α n) (i : Fin n) (x : α) : Vector α n :=
  v.set i.val x i.isLt

/-- The initialization vector (RFC 7693 §2.6): the first 64 bits of the fractional parts of the
square roots of the first eight primes. -/
def IV : Vector UInt64 8 :=
  #v[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
     0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The message-word permutation schedule σ (RFC 7693 §2.7). BLAKE2b runs twelve rounds; rounds
10 and 11 reuse the first two rows. -/
def sigma : Vector (Vector (Fin 16) 16) 12 :=
  #v[#v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
     #v[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
     #v[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
     #v[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
     #v[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
     #v[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
     #v[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
     #v[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
     #v[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
     #v[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
     #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
     #v[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3]]

/-- Rotate a 64-bit word right by `n` bits, for `0 < n < 64`. -/
def rotr (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- The mixing function `G` (RFC 7693 §3.1) on the working vector `v`, at the four word positions
`a b c d`, with message words `x` and `y`; the rotation constants are BLAKE2b's `32, 24, 16, 63`. -/
def mix (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) : Vector UInt64 16 :=
  let va := v.get a + v.get b + x
  let vd := rotr (v.get d ^^^ va) 32
  let vc := v.get c + vd
  let vb := rotr (v.get b ^^^ vc) 24
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 16
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 63
  upd (upd (upd (upd v a va) b vb) c vc) d vd

/-- One round (RFC 7693 §3.2): the four column mixes then the four diagonal mixes, each fed the
two message words its row of `s` selects. -/
def round (m : Vector UInt64 16) (s : Vector (Fin 16) 16) (v : Vector UInt64 16) :
    Vector UInt64 16 :=
  let v := mix v 0 4 8 12 (m.get (s.get 0)) (m.get (s.get 1))
  let v := mix v 1 5 9 13 (m.get (s.get 2)) (m.get (s.get 3))
  let v := mix v 2 6 10 14 (m.get (s.get 4)) (m.get (s.get 5))
  let v := mix v 3 7 11 15 (m.get (s.get 6)) (m.get (s.get 7))
  let v := mix v 0 5 10 15 (m.get (s.get 8)) (m.get (s.get 9))
  let v := mix v 1 6 11 12 (m.get (s.get 10)) (m.get (s.get 11))
  let v := mix v 2 7 8 13 (m.get (s.get 12)) (m.get (s.get 13))
  mix v 3 4 9 14 (m.get (s.get 14)) (m.get (s.get 15))

/-- The compression function `F` (RFC 7693 §3.2): the state `h` and `IV` form the working vector,
the byte counter `t` and the final-block flag are folded into words 12 and 14, twelve rounds run,
and the two halves fold back into `h`. Only the low counter word is carried, which is exact below
`2^64` bytes. -/
def compress (h : Vector UInt64 8) (m : Vector UInt64 16) (t : UInt64) (last : Bool) :
    Vector UInt64 8 :=
  let v : Vector UInt64 16 := h ++ IV
  let v := upd v 12 (v.get 12 ^^^ t)
  let v := if last then upd v 14 (v.get 14 ^^^ 0xffffffffffffffff) else v
  let v := (List.finRange 12).foldl (fun v r => round m (sigma.get r) v) v
  Vector.ofFn fun i : Fin 8 => h.get i ^^^ v.get ⟨i.val, by omega⟩ ^^^ v.get ⟨i.val + 8, by omega⟩

/-- The little-endian word held by the first eight bytes of `bs`; missing bytes read as zero. -/
def wordLE (bs : List UInt8) : UInt64 :=
  (bs.take 8).reverse.foldl (fun acc b => (acc <<< 8) ||| b.toUInt64) 0

/-- Read a 128-byte block as sixteen little-endian words; a short block is zero-padded. -/
def loadBlock (bs : List UInt8) : Vector UInt64 16 :=
  Vector.ofFn fun i : Fin 16 => wordLE ((bs.drop (8 * i.val)).take 8)

/-- Compress the remaining message `rest` into `h`, `counter` bytes having been compressed already.
Every block but the last is full and not final; the last block — the whole of a message of at most
128 bytes, the empty message included — is zero-padded and flagged final with the total byte count
(RFC 7693 §3.3). -/
def hashBlocks (h : Vector UInt64 8) (counter : ℕ) (rest : List UInt8) : Vector UInt64 8 :=
  if rest.length ≤ 128 then
    compress h (loadBlock rest) (UInt64.ofNat (counter + rest.length)) true
  else
    hashBlocks (compress h (loadBlock (rest.take 128)) (UInt64.ofNat (counter + 128)) false)
      (counter + 128) (rest.drop 128)
termination_by rest.length
decreasing_by simp only [List.length_drop]; omega

/-- The initial state for an unkeyed sequential hash of `outLen` output bytes with the 16-byte
personalization `personal`: `IV` xor the parameter block, whose first word packs the digest length,
key length `0`, fanout `1`, and depth `1`, and whose last two words carry the personalization
(RFC 7693 §2.8, BLAKE2 specification §2.8). -/
def initialState (outLen : ℕ) (personal : Vector UInt8 16) : Vector UInt64 8 :=
  let h := upd IV 0 (IV.get 0 ^^^ (0x01010000 ||| UInt64.ofNat outLen))
  let h := upd h 6 (h.get 6 ^^^ wordLE (personal.toList.take 8))
  upd h 7 (h.get 7 ^^^ wordLE (personal.toList.drop 8))

/-- The 64 little-endian bytes of a final state. -/
def finalBytes (h : Vector UInt64 8) : Vector UInt8 64 :=
  Vector.ofFn fun i : Fin 64 =>
    (h.get ⟨i.val / 8, by omega⟩ >>> UInt64.ofNat (8 * (i.val % 8))).toUInt8

/-- The full 64-byte BLAKE2b digest of `msg` under personalization `personal`, unkeyed. -/
def digest64 (personal : Vector UInt8 16) (msg : List UInt8) : Vector UInt8 64 :=
  finalBytes (hashBlocks (initialState 64 personal) 0 msg)

/-- An all-zero personalization: the RFC 7693 configuration. -/
def noPersonal : Vector UInt8 16 := Vector.ofFn fun _ => 0

/-- The ASCII bytes of `Halo2-Transcript`, halo2's transcript personalization. -/
def halo2Personal : Vector UInt8 16 :=
  #v[0x48, 0x61, 0x6c, 0x6f, 0x32, 0x2d, 0x54, 0x72, 0x61, 0x6e, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]

/-! ## Known answers

The RFC 7693 Appendix A vector (`"abc"`, unkeyed, 64 bytes), and five digests of the halo2
personalization computed by Python's `hashlib.blake2b(msg, digest_size=64,
person=b"Halo2-Transcript")`. The five cover the padding boundaries: the empty message, one byte,
exactly one block, one block plus one byte, and three blocks with a partial tail.

The RFC vector and the two-block boundary vector are checked by the kernel (`decide +kernel`, about
15 s per block); the rest are checked by compiled evaluation, which is what the fixture-scale
digests use. These are regression tests, not trust elements: nothing downstream depends on them. -/

example : (digest64 noPersonal [0x61, 0x62, 0x63]).toList =
    [0xba, 0x80, 0xa5, 0x3f, 0x98, 0x1c, 0x4d, 0x0d, 0x6a, 0x27, 0x97, 0xb6,
     0x9f, 0x12, 0xf6, 0xe9, 0x4c, 0x21, 0x2f, 0x14, 0x68, 0x5a, 0xc4, 0xb7,
     0x4b, 0x12, 0xbb, 0x6f, 0xdb, 0xff, 0xa2, 0xd1, 0x7d, 0x87, 0xc5, 0x39,
     0x2a, 0xab, 0x79, 0x2d, 0xc2, 0x52, 0xd5, 0xde, 0x45, 0x33, 0xcc, 0x95,
     0x18, 0xd3, 0x8a, 0xa8, 0xdb, 0xf1, 0x92, 0x5a, 0xb9, 0x23, 0x86, 0xed,
     0xd4, 0x00, 0x99, 0x23] := by decide +kernel

example : (digest64 halo2Personal []).toList =
    [0xa0, 0x0b, 0x7d, 0x27, 0x46, 0x0f, 0xda, 0x08, 0xf2, 0x84, 0x38, 0x63,
     0xfb, 0x81, 0xf8, 0x90, 0x75, 0xb9, 0x95, 0x84, 0x45, 0x3a, 0x6b, 0xd8,
     0xa8, 0xc1, 0xe8, 0x46, 0x84, 0xac, 0x54, 0x22, 0x39, 0x17, 0x38, 0xd0,
     0x86, 0xdc, 0x74, 0x32, 0xf1, 0xdd, 0xee, 0xad, 0x5e, 0x4d, 0x4f, 0xb8,
     0x3d, 0x9b, 0xb8, 0x32, 0x38, 0x96, 0x10, 0x71, 0x17, 0x5e, 0xdf, 0x86,
     0x66, 0x75, 0xdd, 0xb2] := by native_decide

example : (digest64 halo2Personal [0x00]).toList =
    [0xc8, 0xed, 0x8d, 0x14, 0x68, 0xd8, 0xf5, 0x6b, 0x46, 0x01, 0xa9, 0x2a,
     0x58, 0xc8, 0xda, 0x8a, 0x3a, 0x61, 0xe1, 0x9c, 0xb0, 0x8a, 0x76, 0x9d,
     0x65, 0xf7, 0xcc, 0x0c, 0x81, 0xe3, 0xd6, 0x49, 0x21, 0x97, 0x2c, 0x1d,
     0x7e, 0x18, 0x3a, 0x70, 0x0f, 0xbd, 0xaf, 0x31, 0x6b, 0x63, 0x3a, 0x86,
     0x30, 0x22, 0xfc, 0xd8, 0xf0, 0xaa, 0xea, 0x06, 0xd4, 0x33, 0x49, 0x90,
     0xf1, 0xc9, 0xeb, 0x8e] := by native_decide

/-- The bytes `0, 1, …, n - 1` reduced modulo 256. -/
def countingBytes (n : ℕ) : List UInt8 := (List.range n).map UInt8.ofNat

example : (digest64 halo2Personal (countingBytes 128)).toList =
    [0x1d, 0xe5, 0xd0, 0x5c, 0xcf, 0xac, 0xa3, 0x25, 0xc6, 0x21, 0x16, 0x10,
     0xa3, 0xf3, 0x3c, 0xa9, 0xf3, 0xa5, 0xd3, 0x5a, 0x7e, 0xae, 0xb8, 0x07,
     0xad, 0x9e, 0x39, 0x3f, 0x31, 0x74, 0x91, 0x07, 0x45, 0x81, 0xf1, 0xd8,
     0x37, 0xf9, 0xcb, 0xee, 0x7b, 0x91, 0x83, 0x03, 0x82, 0x60, 0x95, 0x86,
     0xb8, 0x9c, 0x3e, 0xa6, 0xa8, 0x7f, 0x4d, 0x27, 0xf2, 0x34, 0x4f, 0xb0,
     0xd9, 0x08, 0x1a, 0x20] := by native_decide

example : (digest64 halo2Personal (countingBytes 129)).toList =
    [0x48, 0x35, 0xbf, 0x29, 0xe5, 0x45, 0x52, 0x0c, 0x5e, 0x62, 0x8a, 0xc0,
     0x24, 0xab, 0x2f, 0xc4, 0xe3, 0x4b, 0x36, 0xd9, 0x50, 0xa7, 0x87, 0x8a,
     0xb7, 0xdb, 0xfc, 0x12, 0x87, 0x7f, 0xd1, 0x06, 0x7b, 0x1c, 0x7c, 0xe2,
     0x46, 0xb7, 0x5b, 0xbc, 0xe7, 0x72, 0x85, 0x2c, 0xd8, 0x7e, 0x2f, 0xbd,
     0x0a, 0x53, 0x83, 0x40, 0x38, 0x32, 0xd5, 0x85, 0x8e, 0xc6, 0x31, 0x41,
     0x49, 0xeb, 0x5c, 0x91] := by decide +kernel

example : (digest64 halo2Personal (countingBytes 300)).toList =
    [0x17, 0x22, 0xcf, 0xfd, 0x15, 0xb7, 0x8c, 0x07, 0x3f, 0xaa, 0x6f, 0xa5,
     0x1e, 0x14, 0xab, 0x88, 0xc8, 0x7f, 0xd4, 0x5c, 0x87, 0x38, 0x18, 0x78,
     0xb0, 0x18, 0xb8, 0xeb, 0xa6, 0x01, 0x86, 0xf4, 0x3d, 0xe2, 0x3e, 0xbc,
     0x0d, 0x1e, 0x68, 0x00, 0x93, 0x79, 0x68, 0x90, 0x06, 0xb6, 0x01, 0x25,
     0xfd, 0x4c, 0xf8, 0x72, 0xc0, 0x0d, 0xd1, 0x38, 0xbc, 0x20, 0x2b, 0x96,
     0xd0, 0x36, 0x1b, 0xff] := by native_decide

end Zcash.Common.Blake2b
