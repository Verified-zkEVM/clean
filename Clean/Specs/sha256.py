"""
Reference implementation of SHA-256 (FIPS 180-4), mirroring Clean/Specs/SHA256.lean.
Tests against hashlib.sha256 to verify correctness.
"""
import hashlib
import struct
from random import randbytes, randint

# Round constants: first 32 bits of the fractional parts of cube roots of first 64 primes
K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]

# Initial hash values: first 32 bits of fractional parts of square roots of first 8 primes
H0 = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
]

MASK32 = 0xffffffff


def rotr32(x: int, n: int) -> int:
    return ((x >> n) | (x << (32 - n))) & MASK32


def sigma0(x: int) -> int:
    return rotr32(x, 7) ^ rotr32(x, 18) ^ (x >> 3)


def sigma1(x: int) -> int:
    return rotr32(x, 17) ^ rotr32(x, 19) ^ (x >> 10)


def Sigma0(x: int) -> int:
    return rotr32(x, 2) ^ rotr32(x, 13) ^ rotr32(x, 22)


def Sigma1(x: int) -> int:
    return rotr32(x, 6) ^ rotr32(x, 11) ^ rotr32(x, 25)


def Ch(e: int, f: int, g: int) -> int:
    return (e & f) ^ (~e & g) & MASK32


def Maj(a: int, b: int, c: int) -> int:
    return (a & b) ^ (a & c) ^ (b & c)


def message_schedule(block: list[int]) -> list[int]:
    """Expand a 16-word block into a 64-word message schedule."""
    w = list(block)
    for i in range(16, 64):
        w.append((sigma1(w[i - 2]) + w[i - 7] + sigma0(w[i - 15]) + w[i - 16]) & MASK32)
    return w


def sha256_round(state: list[int], k: int, w: int) -> list[int]:
    """Apply one SHA-256 round to [a, b, c, d, e, f, g, h]."""
    a, b, c, d, e, f, g, h = state
    t1 = (h + Sigma1(e) + Ch(e, f, g) + k + w) & MASK32
    t2 = (Sigma0(a) + Maj(a, b, c)) & MASK32
    return [(t1 + t2) & MASK32, a, b, c, (d + t1) & MASK32, e, f, g]


def sha256_compress(state: list[int], w: list[int]) -> list[int]:
    """Apply 64 rounds of SHA-256 compression."""
    s = list(state)
    for i in range(64):
        s = sha256_round(s, K[i], w[i])
    return s


def compress_block(state: list[int], block: list[int]) -> list[int]:
    """Process one 512-bit block (16 big-endian 32-bit words)."""
    w = message_schedule(block)
    state2 = sha256_compress(state, w)
    return [(x + y) & MASK32 for x, y in zip(state, state2)]


def pad(msg: bytes) -> list[list[int]]:
    """
    SHA-256 padding (FIPS 180-4):
    append 0x80, zeros until length ≡ 56 (mod 64), then 8-byte big-endian bit length.
    Returns a list of 512-bit blocks, each a list of 16 big-endian 32-bit words.
    """
    msg_len = len(msg)
    bit_len = msg_len * 8
    padded = bytearray(msg)
    padded.append(0x80)
    while len(padded) % 64 != 56:
        padded.append(0)
    padded += struct.pack(">Q", bit_len)
    blocks = []
    for i in range(0, len(padded), 64):
        blocks.append(list(struct.unpack(">16I", padded[i : i + 64])))
    return blocks


def sha256(msg: bytes) -> bytes:
    """Compute SHA-256 of msg, returning a 32-byte digest."""
    blocks = pad(msg)
    state = list(H0)
    for block in blocks:
        state = compress_block(state, block)
    return b"".join(struct.pack(">I", w) for w in state)


if __name__ == "__main__":
    # Verify known test vectors
    assert sha256(b"") == bytes.fromhex(
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    ), "empty string test failed"

    assert sha256(b"abc") == bytes.fromhex(
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    ), "'abc' test failed"

    # Property-based testing against hashlib
    for _ in range(100):
        msg = randbytes(randint(0, 1000))
        h1 = sha256(msg)
        h2 = hashlib.sha256(msg).digest()
        assert h1 == h2, f"FAIL: {h1.hex()} != {h2.hex()}"

    print("All tests passed!")
