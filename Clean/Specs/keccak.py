from math import log
from operator import xor
from functools import reduce
from typing import List
from copy import deepcopy

"""
Note: the whole implementation assumes 64 bit values represented as a list of 8 bytes.
The representation is little-endian, so the first byte is the least significant byte.
"""

RoundConstants = [
    [1, 0, 0, 0, 0, 0, 0, 0],
    [130, 128, 0, 0, 0, 0, 0, 0],
    [138, 128, 0, 0, 0, 0, 0, 128],
    [0, 128, 0, 128, 0, 0, 0, 128],
    [139, 128, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 128, 0, 0, 0, 0],
    [129, 128, 0, 128, 0, 0, 0, 128],
    [9, 128, 0, 0, 0, 0, 0, 128],
    [138, 0, 0, 0, 0, 0, 0, 0],
    [136, 0, 0, 0, 0, 0, 0, 0],
    [9, 128, 0, 128, 0, 0, 0, 0],
    [10, 0, 0, 128, 0, 0, 0, 0],
    [139, 128, 0, 128, 0, 0, 0, 0],
    [139, 0, 0, 0, 0, 0, 0, 128],
    [137, 128, 0, 0, 0, 0, 0, 128],
    [3, 128, 0, 0, 0, 0, 0, 128],
    [2, 128, 0, 0, 0, 0, 0, 128],
    [128, 0, 0, 0, 0, 0, 0, 128],
    [10, 128, 0, 0, 0, 0, 0, 0],
    [10, 0, 0, 128, 0, 0, 0, 128],
    [129, 128, 0, 128, 0, 0, 0, 128],
    [128, 128, 0, 0, 0, 0, 0, 128],
    [1, 0, 0, 128, 0, 0, 0, 0],
    [8, 128, 0, 128, 0, 0, 0, 128],
]

def bits2bytes(x):
    return (int(x) + 7) // 8


def rol_u64(value, left):
    off_bytes = left // 8
    off_bits = left % 8

    bot = value[-off_bytes:]
    top = value[:-off_bytes]
    value = bot + top

    high_bits = []
    low_bits = []
    for i in range(8):
        high_bits.append(value[i] >> (8 - off_bits))
        low_bits.append(value[i] & ((1 << (8 - off_bits)) - 1))
    
    res = [0] * 8
    for i in range(8):
        res[(i+1) % 8] = (high_bits[i] | low_bits[(i + 1) % 8] << off_bits)
    
    return res

def zero_u64():
    return [0] * 8

def xor_u64(a, b):
    assert len(a) == len(b) == 8
    return [x ^ y for x, y in zip(a, b)]

def not_u64(a):
    assert len(a) == 8
    return [~x & 0xFF for x in a]

def and_u64(a, b):
    assert len(a) == len(b) == 8
    return [x & y for x, y in zip(a, b)]


def multirate_padding(used_bytes, align_bytes):
    padlen = align_bytes - used_bytes
    if padlen == 0:
        padlen = align_bytes
    if padlen == 1:
        return [0x81]
    else:
        return [0x01] + ([0x00] * (padlen - 2)) + [0x80]

def theta_c(state : List[List[int]]):
    c = [zero_u64()] * 5
    c[0] = xor_u64(xor_u64(xor_u64(xor_u64(state[0], state[1]), state[2]), state[3]), state[4])
    c[1] = xor_u64(xor_u64(xor_u64(xor_u64(state[5], state[6]), state[7]), state[8]), state[9])
    c[2] = xor_u64(xor_u64(xor_u64(xor_u64(state[10], state[11]), state[12]), state[13]), state[14])
    c[3] = xor_u64(xor_u64(xor_u64(xor_u64(state[15], state[16]), state[17]), state[18]), state[19])
    c[4] = xor_u64(xor_u64(xor_u64(xor_u64(state[20], state[21]), state[22]), state[23]), state[24])
    return c

def theta_d(c : List[int]):
    d = [zero_u64()] * 5
    d[0] = xor_u64(c[4], rol_u64(c[1], 1))
    d[1] = xor_u64(c[0], rol_u64(c[2], 1))
    d[2] = xor_u64(c[1], rol_u64(c[3], 1))
    d[3] = xor_u64(c[2], rol_u64(c[4], 1))
    d[4] = xor_u64(c[3], rol_u64(c[0], 1))
    return d

def theta_xor(state : List[List[int]], c : List[int], d : List[int]):
    new_state = deepcopy(state)
    for i in range(25):
        new_state[i] = xor_u64(state[i], d[i // 5])
    return new_state

def theta(state : List[List[int]]):
    c = theta_c(state)
    d = theta_d(c)
    return theta_xor(state, c, d)

def rho_pi(state):
    b = [zero_u64()] * 25
    b[0] = rol_u64(state[0], 0)
    b[1] = rol_u64(state[15], 28)
    b[2] = rol_u64(state[5], 1)
    b[3] = rol_u64(state[20], 27)
    b[4] = rol_u64(state[10], 62)
    b[5] = rol_u64(state[6], 44)
    b[6] = rol_u64(state[21], 20)
    b[7] = rol_u64(state[11], 6)
    b[8] = rol_u64(state[1], 36)
    b[9] = rol_u64(state[16], 55)
    b[10] = rol_u64(state[12], 43)
    b[11] = rol_u64(state[2], 3)
    b[12] = rol_u64(state[17], 25)
    b[13] = rol_u64(state[7], 10)
    b[14] = rol_u64(state[22], 39)
    b[15] = rol_u64(state[18], 21)
    b[16] = rol_u64(state[8], 45)
    b[17] = rol_u64(state[23], 8)
    b[18] = rol_u64(state[13], 15)
    b[19] = rol_u64(state[3], 41)
    b[20] = rol_u64(state[24], 14)
    b[21] = rol_u64(state[14], 61)
    b[22] = rol_u64(state[4], 18)
    b[23] = rol_u64(state[19], 56)
    b[24] = rol_u64(state[9], 2)
    return b

def chi(b):
    new_state = [zero_u64()] * 25
    new_state[0] = xor_u64(b[0], and_u64(not_u64(b[5]), b[10]))
    new_state[1] = xor_u64(b[1], and_u64(not_u64(b[6]), b[11]))
    new_state[2] = xor_u64(b[2], and_u64(not_u64(b[7]), b[12]))
    new_state[3] = xor_u64(b[3], and_u64(not_u64(b[8]), b[13]))
    new_state[4] = xor_u64(b[4], and_u64(not_u64(b[9]), b[14]))
    new_state[5] = xor_u64(b[5], and_u64(not_u64(b[10]), b[15]))
    new_state[6] = xor_u64(b[6], and_u64(not_u64(b[11]), b[16]))
    new_state[7] = xor_u64(b[7], and_u64(not_u64(b[12]), b[17]))
    new_state[8] = xor_u64(b[8], and_u64(not_u64(b[13]), b[18]))
    new_state[9] = xor_u64(b[9], and_u64(not_u64(b[14]), b[19]))
    new_state[10] = xor_u64(b[10], and_u64(not_u64(b[15]), b[20]))
    new_state[11] = xor_u64(b[11], and_u64(not_u64(b[16]), b[21]))
    new_state[12] = xor_u64(b[12], and_u64(not_u64(b[17]), b[22]))
    new_state[13] = xor_u64(b[13], and_u64(not_u64(b[18]), b[23]))
    new_state[14] = xor_u64(b[14], and_u64(not_u64(b[19]), b[24]))
    new_state[15] = xor_u64(b[15], and_u64(not_u64(b[20]), b[0]))
    new_state[16] = xor_u64(b[16], and_u64(not_u64(b[21]), b[1]))
    new_state[17] = xor_u64(b[17], and_u64(not_u64(b[22]), b[2]))
    new_state[18] = xor_u64(b[18], and_u64(not_u64(b[23]), b[3]))
    new_state[19] = xor_u64(b[19], and_u64(not_u64(b[24]), b[4]))
    new_state[20] = xor_u64(b[20], and_u64(not_u64(b[0]), b[5]))
    new_state[21] = xor_u64(b[21], and_u64(not_u64(b[1]), b[6]))
    new_state[22] = xor_u64(b[22], and_u64(not_u64(b[2]), b[7]))
    new_state[23] = xor_u64(b[23], and_u64(not_u64(b[3]), b[8]))
    new_state[24] = xor_u64(b[24], and_u64(not_u64(b[4]), b[9]))
    return new_state

def iota(state, rc):
    new_state = deepcopy(state)
    new_state[0] = xor_u64(state[0], rc)
    return new_state

def keccak_round(state, rc):
    state1 = theta(state)
    b = rho_pi(state1)
    state2 = chi(b)
    state3 = iota(state2, rc)
    return state3

def keccak_f(state):
    nr = 24
    for ir in range(nr):
        state = keccak_round(state, RoundConstants[ir])
    return state

def state_absorb_block(state, bb):
    assert len(bb) == 136

    bb += [0] * bits2bytes(512)
    i = 0

    new_state = deepcopy(state)
    for y in range(5):
        for x in range(5):
            new_state[x*5 + y] = xor_u64(state[x * 5 + y], bb[i : i + 8])
            i += 8
    return new_state

def state_squeeze(state):
    out = [0] * bits2bytes(1600)
    i = 0
    for y in range(5):
        for x in range(5):
            for j in range(8):
                out[i] = state[x*5 + y][j]
                i += 1
    return out

def keccak256(data : List[int]):
    bitrate_bits = 1088
    bitrate_bytes = bits2bytes(bitrate_bits)
    output_bytes = 32

    state = [zero_u64() for _ in range(25)]

    # absorb data
    buffer = list(data)

    while len(buffer) >= bitrate_bytes:
        bb = buffer[: bitrate_bytes]
        state = state_absorb_block(state, bb)
        state = keccak_f(state)
        buffer = buffer[bitrate_bytes :]

    # absorb final
    padded = buffer + multirate_padding(len(buffer), bitrate_bytes)
    state = state_absorb_block(state, padded)
    state = keccak_f(state)

    # squeeze
    h = state_squeeze(state)[:output_bytes]
    return bytes(h)


# ==================== TESTS ====================

from web3 import Web3
from random import randint, randbytes

state = [[67, 168, 144, 181, 2, 173, 144, 47], [114, 52, 107, 105, 171, 22, 114, 75], [196, 118, 22, 253, 100, 162, 87, 52], [50, 65, 171, 81, 229, 6, 172, 155], [178, 167, 68, 225, 82, 73, 216, 194], [193, 5, 52, 193, 148, 168, 64, 147], [212, 142, 107, 244, 55, 237, 100, 203], [101, 34, 195, 62, 133, 216, 64, 34], [240, 214, 204, 27, 17, 231, 66, 179], [136, 37, 228, 137, 64, 208, 27, 90], [177, 229, 130, 4, 191, 7, 25, 117], [124, 168, 245, 7, 222, 138, 168, 16], [115, 130, 213, 74, 217, 123, 172, 109], [128, 149, 137, 6, 45, 133, 77, 101], [104, 90, 153, 237, 72, 44, 164, 84], [129, 177, 235, 28, 82, 30, 150, 201], [52, 55, 32, 241, 142, 211, 246, 68], [149, 124, 124, 204, 34, 220, 229, 69], [215, 168, 47, 96, 70, 5, 220, 2], [53, 224, 38, 18, 110, 66, 70, 9], [213, 122, 200, 196, 186, 122, 207, 42], [141, 103, 32, 88, 244, 160, 37, 76], [99, 242, 138, 24, 4, 30, 100, 196], [141, 253, 136, 54, 8, 21, 204, 152], [93, 161, 29, 12, 44, 252, 49, 57]]
rc = [235, 226, 178, 113, 2, 17, 87, 249]

for _ in range(100):
    input = randbytes(randint(0, 1000))
    h1 = keccak256(input)
    h2 = Web3.solidity_keccak(['bytes'], [input])
    print(h1.hex(), h2.hex())
    assert h1.hex() == h2.hex()

print(list(keccak256(b'')))