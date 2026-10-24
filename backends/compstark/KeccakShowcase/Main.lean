import KeccakShowcase.Evidence
import CompStarkFixtures.Poseidon2Example

/-! # `keccak_showcase`

The keccak-air showcase's evidence and benchmark (`KeccakShowcase.Evidence`), on the Poseidon2
instances of Plonky3's example `prove_prime_field_31`.
-/

def main (args : List String) : IO UInt32 :=
  KeccakShowcase.main CompStark.Fixtures.Poseidon2Example.instances args
