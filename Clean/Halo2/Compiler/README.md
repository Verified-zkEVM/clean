# Compiled circuit semantics

This directory proves that the Halo2 compiler preserves circuit constraints. Its
public endpoint is `TopLevelCircuit.soundness_compiled` in `ConstraintsCompiled`:
compiled gate vanishing, resolved copy equality, and lookup tuple membership imply
the circuit specification for the public input and witness extracted from an assignment.
The circuit-owned environment already supplies the fixed columns and usable rows.

Selector packing, query indexing, region placement, constant allocation, and
permutation assembly are handled inside this layer. Lookup membership is needed at
the compiler's activation rows, with every usable table row available. The theory
uses arbitrary finite fields; `CircuitFieldSupport` relates a circuit's dimensions
to the chosen `FieldDomainParams`.

Polynomial commitments, verifier acceptance, and cryptographic failure events belong
to consumers of this API. `PermutationRows` exposes the executable column generator
separately from its correctness proofs so key generation can import it directly.
