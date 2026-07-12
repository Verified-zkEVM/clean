import Clean.Halo2.Provable
import Clean.Halo2.Basic

/-!
# `UnconstrainedNative` in Halo2-Clean — genuinely external prover hints

Main Clean's `UnconstrainedNative` (`Clean/Circuit/CircuitType.lean`) is already
environment-generic: its `CircuitTypeOver Env PEnv` instance instantiates at Halo2-Clean's
placed cell environments just as it does at main Clean's tape environments. This file pins
that down with compile-time checks (no new mechanism is needed — the "port" is the shared
definition itself) and documents the usage rule.

## When to use `UnconstrainedNative` vs deriving from a cell (the hard rule)

Per `Clean/Halo2/halo2-clean-requirements.md` ("No prover information at synthesis time"):

- **Derive from a cell** whenever the Rust circuit computes the prover-side value from a
  *witnessed cell* — e.g. variable-base scalar mul's bits come from
  `decompose_for_scalar_mul(alpha.value())`, so the port computes them inside the witness
  closures from the `alpha` cell (`MulIncomplete.bitsOf` / `kBitsWindow`), and the bundles
  carry only a window offset `w : ℕ`. Such values are NOT hints: modeling them as
  `UnconstrainedNative` inputs would weaken completeness (an arbitrary hint has to be
  *assumed* honest via `ProverAssumptions`) and would misstate the Rust dataflow.

- **`UnconstrainedNative Hint`** is for *genuinely external* prover inputs — `Value<F>`
  data that enters the circuit from outside and has no in-circuit source cell (main Clean's
  `witness_point`-style unassigned values). It erases to `Unit` for the verifier and
  evaluates to the actual `Hint` for the prover (`Var … = PEnv F → Hint`); honest-value
  facts about it live in `ProverAssumptions`/`ProverSpec`, never in `Assumptions`.

- Structured, serializable hint *computation* should prefer the witness IR
  (`Unconstrained`/`UnconstrainedBool`/`UnconstrainedNat` in `Clean/Circuit/WitnessIRSugar.lean`,
  also environment-generic); `UnconstrainedNative` is the closure-backed escape hatch.

KERNEL-SAFETY note (learned in C3): a hint carrying huge-numeral arithmetic (e.g. anything
unfolding to `x + tQNat` with the literal on the right) must keep that computation behind a
top-level def with a kernel-benign spelling — see `MulIncomplete.kBitsWindow`.
-/

namespace Halo2

variable {F : Type} [FiniteField F] {Hint : Type}

/-! ## The shared mechanism at the halo2 environments

Forwarding instances helping instance search through the defeq `Var (UnconstrainedNative
Hint) F = (Placed ProverEnvironment F → Hint)` — the halo2 counterparts of main Clean's
`VerifierEval`/`ProverEval` forwarders in `Clean/Circuit/CircuitType.lean`. -/

instance : Eval (Placed Environment F) (Placed ProverEnvironment F → Hint) Unit :=
  CircuitType.verifierEval (UnconstrainedNative Hint)

instance : Eval (Placed ProverEnvironment F) (Placed ProverEnvironment F → Hint) Hint :=
  CircuitType.proverEval (UnconstrainedNative Hint)

/-! ## Compile-time checks -/

/-- The halo2 `Var` view of an `UnconstrainedNative` input is a function of the *placed
prover environment* — the same shape the `.native` witness closures receive. -/
example : Var (UnconstrainedNative Hint) F = (Placed ProverEnvironment F → Hint) := rfl

/-- The verifier view erases to `Unit`. -/
example : Value (UnconstrainedNative Hint) F = Unit := rfl

/-- The prover view is the hint itself. -/
example : ProverValue (UnconstrainedNative Hint) F = Hint := rfl

/-- Prover-side evaluation applies the hint program to the placed prover environment. -/
example (env : Placed ProverEnvironment F) (v : Placed ProverEnvironment F → Hint) :
    eval env v = v env := by with_unfolding_all rfl

/-- Verifier-side evaluation is trivial. -/
example (env : Placed Environment F) (v : Placed ProverEnvironment F → Hint) :
    eval env v = () := rfl

end Halo2
