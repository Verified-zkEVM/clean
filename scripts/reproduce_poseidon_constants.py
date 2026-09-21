#!/usr/bin/env python3
"""Reproduce and audit circomlib's optimized BN254 Poseidon parameters.

The implementation is independent of ``poseidon_constants.circom``. It uses
the Grain-LFSR construction from the Poseidon reference generator, then applies
circomlibjs's constant compression and sparse-matrix factorization. The normal
check is offline and compares canonical SHA-256 digests of every generated
field element with digests recorded before the original Lean literal tables
were removed.

Pass ``--source`` for the stronger source audit: the script first verifies the
pinned circomlib file hash, then compares all generated C/M/P/S values with the
file. No upstream checkout is needed for normal Lean builds or the digest check.

The Sage reference applies additional security tests to candidate MDS matrices.
For every fixed circomlib width checked here, the first sampled Cauchy matrix is
the published matrix. This is a reproducer for those instances, not a general
security-parameter chooser.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import statistics
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator, Sequence


BN254_PRIME = 21888242871839275222246405745257275088548364400416034343698204186575808495617
FIELD_SIZE = 254
N_ROUNDS_F = 8
N_ROUNDS_P = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]
KINDS = ("C", "M", "P", "S")

SOURCE_COMMIT = "35e54ea21da3e8762557234298dbb553c175ea8d"
SOURCE_SHA256 = "94c9e4b5ea891ab4d1ba626f1d719f8c661014d9b628f6096c803f75f39e3eee"
ALL_TABLES_SHA256 = "a7bf61df7f046f2ceb1f1309e5207b272c7fbbac097d00a64d53de5353d7aa2e"

# Each digest covers C, M, P, then S, with every field element encoded as an
# unsigned 32-byte big-endian integer. These were computed from the old Lean
# literal file after it had been checked against the pinned circomlib source.
WIDTH_DIGESTS = {
    2: (248, "3a92d79b676792bd486e31b92ca9962709f4b904c968c12f4f1c25b60407a6e4"),
    3: (384, "b1074afddd3e3063b0a8621b246632f8a18c8d41af2f35947b111fbb07c701cf"),
    4: (512, "3bae61778c1231fdb17b353d96b624f1cacf8845648061471c813cffbe2ef8ca"),
    5: (690, "e4ff37fa54b6061528f87ced1af7931af741b5be0a1fb97660a96457d35d29ed"),
    6: (840, "c12ea60ac6b920502ee468ac64ab8a1279625be85956b1da7d784909a3142cab"),
    7: (1036, "4248e3dd629b319beda72ab6a79caeebfe5bf8fc731bd6a9fb5db64bc54d976f"),
    8: (1216, "2c4dad31d0a130c96c48d746c5dba366d7e99a0b12b7776a780c89eed70b496e"),
    9: (1368, "99de9155ee2d5409a2d52dd85441224591662e799c3d71a529d127560f01c221"),
    10: (1480, "a1f280eb48d2abafd83f9c1a12fc48953a1bb055b8b1c4e9238ebbbe7620dcb6"),
    11: (1782, "f023fd3c8f2cddce0eb1725aed1309e18fc647d338058a3688adc09d2fa8f756"),
    12: (1824, "4981098b340005252e0b989f66db9043d772c73740ebcade8de914f8ee28ee46"),
    13: (2132, "d2245bb967ef1939af1c6e48e02d7fc6c4c233358b870e3a3fa9c05c1486b23b"),
    14: (2464, "04da31903d98c169bad208b628d3e5e5ed226979db185eb214bd479f8aec7f50"),
    15: (2370, "3a11a3fcd0f127983f8aea9129dec7e9134f3f7bb04d1fc6bee358defc9f6f0b"),
    16: (2688, "39c86fcf82e41d9945274e9a433e383c4ab51430e76eb8ce71755d7f81a5f6e8"),
    17: (3026, "5392e6a93fb93f777d7edeef1e83e309fbedacc8a19db4a15dedd2fa547083c1"),
}

Matrix = list[list[int]]
Tables = dict[tuple[str, int], list[int]]


def fixed_bits(value: int, width: int) -> list[int]:
    bits = f"{value:0{width}b}"
    if len(bits) != width:
        raise ValueError(f"{value} does not fit in {width} bits")
    return [int(bit) for bit in bits]


class Grain:
    """The 80-bit self-shrinking LFSR used by the Poseidon reference."""

    def __init__(self, width: int, n_partial: int) -> None:
        self.state = (
            fixed_bits(1, 2)
            + fixed_bits(0, 4)
            + fixed_bits(FIELD_SIZE, 12)
            + fixed_bits(width, 12)
            + fixed_bits(N_ROUNDS_F, 10)
            + fixed_bits(n_partial, 10)
            + [1] * 30
        )
        if len(self.state) != 80:
            raise AssertionError("invalid Grain initial state")
        for _ in range(160):
            self.step()

    def step(self) -> int:
        bit = (
            self.state[62]
            ^ self.state[51]
            ^ self.state[38]
            ^ self.state[23]
            ^ self.state[13]
            ^ self.state[0]
        )
        self.state.pop(0)
        self.state.append(bit)
        return bit

    def bits(self) -> Iterator[int]:
        while True:
            selector = self.step()
            while selector == 0:
                self.step()
                selector = self.step()
            yield self.step()

    def random_int(self, bit_stream: Iterator[int], n_bits: int = FIELD_SIZE) -> int:
        value = 0
        for _ in range(n_bits):
            value = (value << 1) | next(bit_stream)
        return value


def generate_base(width: int, n_partial: int) -> tuple[list[int], Matrix]:
    grain = Grain(width, n_partial)
    bit_stream = grain.bits()
    constants = []
    for _ in range((N_ROUNDS_F + n_partial) * width):
        value = grain.random_int(bit_stream)
        while value >= BN254_PRIME:
            value = grain.random_int(bit_stream)
        constants.append(value)

    # The reference samples the Cauchy coordinates from the same stream after
    # the round constants and reduces them modulo p.
    while True:
        coordinates = [
            grain.random_int(bit_stream) % BN254_PRIME for _ in range(2 * width)
        ]
        if len(set(coordinates)) != len(coordinates):
            continue
        xs = coordinates[:width]
        ys = coordinates[width:]
        if any((x + y) % BN254_PRIME == 0 for x in xs for y in ys):
            continue
        matrix = [
            [pow((x + y) % BN254_PRIME, -1, BN254_PRIME) for y in ys]
            for x in xs
        ]
        return constants, matrix


def transpose(matrix: Matrix) -> Matrix:
    return [list(row) for row in zip(*matrix)]


def matrix_inverse(matrix: Matrix) -> Matrix:
    size = len(matrix)
    augmented = [
        [entry % BN254_PRIME for entry in row]
        + [int(row_index == column) for column in range(size)]
        for row_index, row in enumerate(matrix)
    ]
    for column in range(size):
        pivot = next(
            (row for row in range(column, size) if augmented[row][column] != 0),
            None,
        )
        if pivot is None:
            raise ValueError("matrix is not invertible")
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        scale = pow(augmented[column][column], -1, BN254_PRIME)
        augmented[column] = [(entry * scale) % BN254_PRIME for entry in augmented[column]]
        for row in range(size):
            if row == column:
                continue
            factor = augmented[row][column]
            if factor:
                augmented[row] = [
                    (left - factor * right) % BN254_PRIME
                    for left, right in zip(augmented[row], augmented[column])
                ]
    return [row[size:] for row in augmented]


def vector_times_matrix(vector: Sequence[int], matrix: Matrix) -> list[int]:
    return [
        sum(vector[row] * matrix[row][column] for row in range(len(vector)))
        % BN254_PRIME
        for column in range(len(vector))
    ]


def matrix_times_vector(matrix: Matrix, vector: Sequence[int]) -> list[int]:
    return [
        sum(entry * value for entry, value in zip(row, vector)) % BN254_PRIME
        for row in matrix
    ]


def matrix_multiply(left: Matrix, right: Matrix) -> Matrix:
    right_t = transpose(right)
    return [
        [sum(a * b for a, b in zip(row, column)) % BN254_PRIME for column in right_t]
        for row in left
    ]


def compress_constants(
    width: int, n_partial: int, constants: list[int], matrix: Matrix
) -> list[int]:
    matrix_inv = matrix_inverse(matrix)
    result = list(constants[:width])
    for round_index in range(N_ROUNDS_F // 2 - 1):
        start = (round_index + 1) * width
        result.extend(vector_times_matrix(constants[start : start + width], matrix_inv))

    start = (N_ROUNDS_F // 2 + n_partial) * width
    accumulator = list(constants[start : start + width])
    partial_constants = []
    for round_index in range(
        N_ROUNDS_F // 2 + n_partial - 1,
        N_ROUNDS_F // 2 - 1,
        -1,
    ):
        transformed = vector_times_matrix(accumulator, matrix_inv)
        partial_constants.append(transformed[0])
        transformed[0] = 0
        start = round_index * width
        accumulator = [
            (value + constant) % BN254_PRIME
            for value, constant in zip(transformed, constants[start : start + width])
        ]

    result.extend(vector_times_matrix(accumulator, matrix_inv))
    result.extend(reversed(partial_constants))
    for round_index in range(
        N_ROUNDS_F // 2 + n_partial,
        N_ROUNDS_F + n_partial - 1,
    ):
        start = (round_index + 1) * width
        result.extend(vector_times_matrix(constants[start : start + width], matrix_inv))

    expected = N_ROUNDS_F * width + n_partial
    if len(result) != expected:
        raise AssertionError(f"compressed C has {len(result)} values, expected {expected}")
    return result


def sparse_factorize(matrix: Matrix) -> tuple[Matrix, list[int]]:
    width = len(matrix)
    m_hat = [row[1:] for row in matrix[1:]]
    m_prime = [
        [
            matrix[row][column]
            if row > 0 and column > 0
            else int(row == 0 and column == 0)
            for column in range(width)
        ]
        for row in range(width)
    ]
    w = [matrix[row][0] for row in range(1, width)]
    w_prime = matrix_times_vector(matrix_inverse(m_hat), w)
    sparse = [matrix[0][0], *w_prime, *matrix[0][1:]]
    return m_prime, sparse


def calculate_sparse(width: int, n_partial: int, matrix: Matrix) -> tuple[Matrix, list[int]]:
    current = matrix
    sparse_matrices = []
    for _ in range(n_partial):
        m_prime, sparse = sparse_factorize(current)
        sparse_matrices.append(sparse)
        current = matrix_multiply(matrix, m_prime)
    sparse_values = [value for sparse in reversed(sparse_matrices) for value in sparse]
    expected = n_partial * (2 * width - 1)
    if len(sparse_values) != expected:
        raise AssertionError(f"S has {len(sparse_values)} values, expected {expected}")
    return current, sparse_values


def reproduce(width: int, n_partial: int) -> tuple[dict[str, list[int]], float, float]:
    started = time.perf_counter()
    constants, base_matrix = generate_base(width, n_partial)
    generated_at = time.perf_counter()
    # circomlibjs transposes the reference MDS matrix before optimizing it.
    matrix = transpose(base_matrix)
    compressed = compress_constants(width, n_partial, constants, matrix)
    pre_sparse, sparse = calculate_sparse(width, n_partial, matrix)
    optimized_at = time.perf_counter()
    return (
        {
            "C": compressed,
            "M": [value for row in matrix for value in row],
            "P": [value for row in pre_sparse for value in row],
            "S": sparse,
        },
        generated_at - started,
        optimized_at - generated_at,
    )


def matching_bracket(text: str, start: int) -> int:
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "[":
            depth += 1
        elif text[index] == "]":
            depth -= 1
            if depth == 0:
                return index
    raise ValueError(f"unclosed array starting at byte {start}")


def parse_source(source: str) -> Tables:
    tables: Tables = {}
    functions = list(re.finditer(r"function POSEIDON_([CMPS])\(t\)\s*\{", source))
    for function_index, function in enumerate(functions):
        kind = function.group(1)
        function_end = functions[function_index + 1].start() if function_index + 1 < len(functions) else len(source)
        body = source[function.end() : function_end]
        for branch in re.finditer(r"(?:if|else if)\s*\(t\s*==\s*(\d+)\)\s*\{", body):
            width = int(branch.group(1))
            return_index = body.find("return", branch.end())
            array_start = body.find("[", return_index)
            if return_index < 0 or array_start < 0:
                raise ValueError(f"missing return array for POSEIDON_{kind}({width})")
            array_end = matching_bracket(body, array_start)
            tables[(kind, width)] = [
                int(value, 16)
                for value in re.findall(r"0x[0-9a-fA-F]+", body[array_start : array_end + 1])
            ]

    for width, n_partial in enumerate(N_ROUNDS_P, 2):
        expected = {
            "C": N_ROUNDS_F * width + n_partial,
            "M": width * width,
            "P": width * width,
            "S": n_partial * (2 * width - 1),
        }
        for kind, length in expected.items():
            actual = len(tables.get((kind, width), []))
            if actual != length:
                raise ValueError(f"POSEIDON_{kind}({width}) has {actual} values; expected {length}")
    return tables


def compare_source(width: int, actual: dict[str, list[int]], source: Tables) -> int:
    checked = 0
    for kind in KINDS:
        expected = source[(kind, width)]
        if len(actual[kind]) != len(expected):
            raise AssertionError(f"{kind}_t{width} has the wrong length")
        for index, (generated, published) in enumerate(zip(actual[kind], expected)):
            if generated != published:
                raise AssertionError(
                    f"{kind}_t{width}[{index}] mismatch:\n"
                    f"  generated: 0x{generated:x}\n"
                    f"  published: 0x{published:x}"
                )
        checked += len(expected)
    return checked


def update_digest(digest: "hashlib._Hash", tables: dict[str, list[int]]) -> int:
    count = 0
    for kind in KINDS:
        for value in tables[kind]:
            digest.update(value.to_bytes(32, "big"))
            count += 1
    return count


def check_digest(width: int, tables: dict[str, list[int]]) -> int:
    digest = hashlib.sha256()
    count = update_digest(digest, tables)
    expected_count, expected_digest = WIDTH_DIGESTS[width]
    if count != expected_count or digest.hexdigest() != expected_digest:
        raise AssertionError(
            f"t={width} digest is {digest.hexdigest()} over {count} values; "
            f"expected {expected_digest} over {expected_count}"
        )
    return count


@dataclass
class Trial:
    base_seconds: float = 0.0
    optimize_seconds: float = 0.0
    total_seconds: float = 0.0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source",
        type=Path,
        help="optional pinned circomlib poseidon_constants.circom for a value-by-value audit",
    )
    parser.add_argument(
        "--width",
        type=int,
        action="append",
        dest="widths",
        help="state width to check (repeatable; default: 2 through 17)",
    )
    parser.add_argument(
        "--trials",
        type=int,
        default=3,
        help="number of timed reproduction-and-check trials (default: 3)",
    )
    args = parser.parse_args()

    widths = sorted(set(args.widths or range(2, 18)))
    if any(width < 2 or width > 17 for width in widths):
        parser.error("width must be between 2 and 17")
    if args.trials < 1:
        parser.error("trials must be positive")

    source_tables = None
    parse_seconds = 0.0
    if args.source:
        parse_started = time.perf_counter()
        source_bytes = args.source.read_bytes()
        source_digest = hashlib.sha256(source_bytes).hexdigest()
        if source_digest != SOURCE_SHA256:
            raise ValueError(
                f"source SHA-256 is {source_digest}; expected {SOURCE_SHA256} "
                f"(circomlib commit {SOURCE_COMMIT})"
            )
        source_tables = parse_source(source_bytes.decode())
        parse_seconds = time.perf_counter() - parse_started

    trials = []
    checked = 0
    full_digest = hashlib.sha256()
    for trial_index in range(args.trials):
        trial_started = time.perf_counter()
        trial = Trial()
        trial_checked = 0
        for width in widths:
            n_partial = N_ROUNDS_P[width - 2]
            tables, base_seconds, optimize_seconds = reproduce(width, n_partial)
            trial.base_seconds += base_seconds
            trial.optimize_seconds += optimize_seconds
            trial_checked += check_digest(width, tables)
            if source_tables is not None:
                compare_source(width, tables, source_tables)
            if trial_index == 0:
                update_digest(full_digest, tables)
                print(
                    f"t={width:2}: OK  base={base_seconds:7.3f}s  "
                    f"optimize={optimize_seconds:7.3f}s  "
                    f"values={sum(len(table) for table in tables.values()):5}"
                )
        trial.total_seconds = time.perf_counter() - trial_started
        trials.append(trial)
        checked = trial_checked

    if widths == list(range(2, 18)) and full_digest.hexdigest() != ALL_TABLES_SHA256:
        raise AssertionError(
            f"combined digest is {full_digest.hexdigest()}; expected {ALL_TABLES_SHA256}"
        )

    audit = "digests and pinned source" if source_tables is not None else "pinned digests"
    print(f"\nVerified {checked} generated values against {audit}.")
    if source_tables is not None:
        print(f"Pinned source parse: {parse_seconds:.3f}s")
    totals = [trial.total_seconds for trial in trials]
    print(
        f"Reproduction benchmark ({args.trials} trial{'s' if args.trials != 1 else ''}): "
        f"min={min(totals):.3f}s  median={statistics.median(totals):.3f}s  "
        f"max={max(totals):.3f}s"
    )
    print(
        f"Median phase totals: base={statistics.median(t.base_seconds for t in trials):.3f}s  "
        f"optimize={statistics.median(t.optimize_seconds for t in trials):.3f}s"
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (AssertionError, OSError, ValueError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
