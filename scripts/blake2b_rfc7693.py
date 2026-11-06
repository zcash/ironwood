#!/usr/bin/env python
"""BLAKE2b from the RFC 7693 pseudocode (sections 3.1-3.3), for known-answer vectors.

Independent of any other BLAKE2b implementation: the only inputs are the constants and
pseudocode in the RFC. `compress(h, m, t, last)` is the compression function F with the
128-bit byte counter t; `digest64(msg, personal)` is the unkeyed, sequential, 64-byte hash
with a 16-byte personalization, the configuration halo2's transcript uses.
"""
import sys

MASK = (1 << 64) - 1
IV = [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
      0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]
SIGMA = [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
         [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
         [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
         [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
         [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
         [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
         [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
         [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
         [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
         [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

def rotr(x, n):
    return ((x >> n) | (x << (64 - n))) & MASK

def G(v, a, b, c, d, x, y):
    v[a] = (v[a] + v[b] + x) & MASK
    v[d] = rotr(v[d] ^ v[a], 32)
    v[c] = (v[c] + v[d]) & MASK
    v[b] = rotr(v[b] ^ v[c], 24)
    v[a] = (v[a] + v[b] + y) & MASK
    v[d] = rotr(v[d] ^ v[a], 16)
    v[c] = (v[c] + v[d]) & MASK
    v[b] = rotr(v[b] ^ v[c], 63)

def compress(h, m, t, last):
    """RFC 7693 section 3.2: h is 8 words, m is 16 words, t the byte counter (an integer below
    2^128), last the final-block flag. Returns the new 8 words."""
    v = list(h) + list(IV)
    v[12] ^= t & MASK
    v[13] ^= (t >> 64) & MASK
    if last:
        v[14] ^= MASK
    for i in range(12):
        s = SIGMA[i % 10]
        G(v, 0, 4, 8, 12, m[s[0]], m[s[1]])
        G(v, 1, 5, 9, 13, m[s[2]], m[s[3]])
        G(v, 2, 6, 10, 14, m[s[4]], m[s[5]])
        G(v, 3, 7, 11, 15, m[s[6]], m[s[7]])
        G(v, 0, 5, 10, 15, m[s[8]], m[s[9]])
        G(v, 1, 6, 11, 12, m[s[10]], m[s[11]])
        G(v, 2, 7, 8, 13, m[s[12]], m[s[13]])
        G(v, 3, 4, 9, 14, m[s[14]], m[s[15]])
    return [h[i] ^ v[i] ^ v[i + 8] for i in range(8)]

def words(block):
    block = bytes(block) + bytes(128 - len(block))
    return [int.from_bytes(block[8 * i:8 * i + 8], "little") for i in range(16)]

def initial_state(out_len, personal):
    """IV xor the parameter block: digest length, key length 0, fanout 1, depth 1, and the
    personalization in parameter words 6 and 7 (BLAKE2 specification section 2.8)."""
    assert len(personal) == 16
    h = list(IV)
    h[0] ^= 0x01010000 | out_len
    h[6] ^= int.from_bytes(personal[:8], "little")
    h[7] ^= int.from_bytes(personal[8:], "little")
    return h

def digest64(msg, personal=bytes(16)):
    """RFC 7693 section 3.3, unkeyed: every block but the last is full and not final; the last
    block, the whole of a message of at most 128 bytes included, is zero-padded and flagged final
    with the total byte count."""
    h = initial_state(64, personal)
    msg = bytes(msg)
    pos = 0
    while len(msg) - pos > 128:
        h = compress(h, words(msg[pos:pos + 128]), pos + 128, False)
        pos += 128
    h = compress(h, words(msg[pos:]), len(msg), True)
    return b"".join(w.to_bytes(8, "little") for w in h)

def lean_list(bs):
    return "[" + ", ".join(f"0x{b:02x}" for b in bs) + "]"

if __name__ == "__main__":
    # The RFC 7693 Appendix A vector, as a self-check of the transcription.
    abc = digest64(b"abc")
    assert abc.hex().startswith("ba80a53f981c4d0d6a2797b69f12f6e9"), abc.hex()
    if len(sys.argv) > 1 and sys.argv[1] == "--counter-high":
        # The synthetic compression vector with the high counter word set: one zero block,
        # unkeyed, no personalization, final, at t = 2^64.
        out = compress(initial_state(64, bytes(16)), words(b""), 1 << 64, True)
        print(lean_list(b"".join(w.to_bytes(8, "little") for w in out)))
    else:
        personal = sys.argv[1].encode() if len(sys.argv) > 1 else bytes(16)
        print(digest64(sys.stdin.buffer.read(), personal).hex())
