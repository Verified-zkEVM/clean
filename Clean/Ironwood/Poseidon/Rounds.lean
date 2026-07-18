import Clean.Ironwood.Poseidon.Pow5

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon/pow5.rs`
- `Pow5State::full_round` (lines 434-459) / `Pow5State::partial_round` (461-534) /
  `Pow5State::round` (552-592): enable the round gate at `offset`, assign the `rc_a`
  round constants at `offset` (partial rounds also `rc_b` and the `partial_sbox` mid
  value), assign the next state at `offset + 1`.

The rounds are positional (`MulIncompleteRound` pattern): the entering state row is the
`Witness`/`extract` neighborhood, the outgoing state row is the output. Round `r` at
region offset `o` writes row `o + 1`, which is round `r + 1`'s entering row — the loop
chains by `rfl`. Value-level contracts are the donor's `FullRound.value` /
`PartialRounds.value` (`Clean/Orchard/Poseidon/Pow5.lean`).
-/

namespace Halo2.Ironwood.Poseidon

open Halo2.Ironwood (Fp)
open Orchard.Poseidon
open Orchard.Poseidon.Permute (State)
open Orchard.Poseidon.Permute.P128Pow5T3 (mds mdsInv roundConstants)

/-- The state row at region offset `o`: the three state cells. -/
def stateRow (cfg : Config) (o : ℕ) (self : RegionIndex) : State (AssignedCell Fp) where
  x0 := .of self o (cfg.state 0)
  x1 := .of self o (cfg.state 1)
  x2 := .of self o (cfg.state 2)

/-- Name the entering state cells inside `synthesize` (no ops emitted). -/
def readStateRow (cfg : Config) (o : ℕ) : RegionCircuit Fp (State (AssignedCell Fp)) :=
  fun self => (stateRow cfg o self, [])

@[circuit_norm]
theorem operations_readStateRow (cfg : Config) (o : ℕ) (self : RegionIndex) :
    (readStateRow cfg o).operations self = [] := rfl

@[circuit_norm]
theorem output_readStateRow (cfg : Config) (o : ℕ) (self : RegionIndex) :
    (readStateRow cfg o).output self = stateRow cfg o self := rfl

/-- The prover-view values of a state row. -/
def rowValue (w : State (AssignedCell Fp)) (env : Placed ProverEnvironment Fp) : State Fp where
  x0 := readCell env w.x0
  x1 := readCell env w.x1
  x2 := readCell env w.x2

/-- A witness program computing one field of a state-function of the entering row. -/
def rowWit (w : State (AssignedCell Fp)) (f : State Fp → Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[f (rowValue w env)]

@[circuit_norm]
theorem rowWit_eval (w : State (AssignedCell Fp)) (f : State Fp → Fp)
    (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((rowWit w f).eval env)[j] = f (rowValue w env) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [rowWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Rust `Pow5State::full_round` at source round `r` (`pow5.rs:434-459` + `round`,
552-592): enable `s_full` at `offset`, load the `rc_a` round constants at `offset`,
assign the next state at `offset + 1`. Positional: `Witness` is the entering state row,
`Spec` is the donor `FullRound.value`. -/
def fullRound (r : ℕ) : FormalRegionCircuit Fp Config Config unit State where
  configure := pure

  synthesize cfg offset _ := do
    let w ← readStateRow cfg offset
    (fullRoundGate cfg).enable offset
    let _rc0 ← assignFixed (cfg.rcA 0) offset (roundConstants r).x0
    let _rc1 ← assignFixed (cfg.rcA 1) offset (roundConstants r).x1
    let _rc2 ← assignFixed (cfg.rcA 2) offset (roundConstants r).x2
    let _n0 ← assignAdvice (cfg.state 0) (offset + 1)
      (rowWit w fun s => (FullRound.value (FullRound.params roundConstants mds r) s).x0)
    let _n1 ← assignAdvice (cfg.state 1) (offset + 1)
      (rowWit w fun s => (FullRound.value (FullRound.params roundConstants mds r) s).x1)
    let _n2 ← assignAdvice (cfg.state 2) (offset + 1)
      (rowWit w fun s => (FullRound.value (FullRound.params roundConstants mds r) s).x2)
    readStateRow cfg (offset + 1)

  Witness := State
  extract cfg offset _ self env := eval env (stateRow cfg offset self)

  Spec _ out w := out = FullRound.value (FullRound.params roundConstants mds r) w

  ProverSpec _ out w _ := out = FullRound.value (FullRound.params roundConstants mds r) w

  soundness := by
    circuit_proof_start [fullRoundGate, pow5Expr, stateRow, FullRound.value,
      FullRound.params, pow5, Nat.add_assoc, Nat.reduceMod]
    obtain ⟨⟨hg0, hg1, hg2⟩, hrc0, hrc1, hrc2⟩ := hc
    rw [hrc0, hrc1, hrc2] at hg0 hg1 hg2
    exact ⟨by linear_combination -hg0, by linear_combination -hg1,
      by linear_combination -hg2⟩

  completeness := by
    circuit_proof_start [fullRoundGate, pow5Expr, stateRow, FullRound.value,
      FullRound.params, pow5]
    sorry

/-- Rust `Pow5State::partial_round` at source round `r` (`pow5.rs:461-534`): one row
checking two source rounds. Enable `s_partial` at `offset`, load `rc_a` (round `r`) and
`rc_b` (round `r + 1`) at `offset`, witness the first-round S-box into `partial_sbox` at
`offset`, assign the next state at `offset + 1`. `Spec` is the donor
`PartialRounds.value` at `paramsP128 r`. -/
def partialRound (r : ℕ) : FormalRegionCircuit Fp Config Config unit State where
  configure := pure

  synthesize cfg offset _ := do
    let w ← readStateRow cfg offset
    (partialRoundsGate cfg).enable offset
    let _rc0 ← assignFixed (cfg.rcA 0) offset (roundConstants r).x0
    let _rc1 ← assignFixed (cfg.rcA 1) offset (roundConstants r).x1
    let _rc2 ← assignFixed (cfg.rcA 2) offset (roundConstants r).x2
    let _mid ← assignAdvice cfg.partialSbox offset
      (rowWit w fun s => PartialRounds.mid0SboxValue
        (PartialRounds.paramsP128 roundConstants r) s)
    let _rb0 ← assignFixed (cfg.rcB 0) offset (roundConstants (r + 1)).x0
    let _rb1 ← assignFixed (cfg.rcB 1) offset (roundConstants (r + 1)).x1
    let _rb2 ← assignFixed (cfg.rcB 2) offset (roundConstants (r + 1)).x2
    let _n0 ← assignAdvice (cfg.state 0) (offset + 1)
      (rowWit w fun s =>
        (PartialRounds.value (PartialRounds.paramsP128 roundConstants r) s).x0)
    let _n1 ← assignAdvice (cfg.state 1) (offset + 1)
      (rowWit w fun s =>
        (PartialRounds.value (PartialRounds.paramsP128 roundConstants r) s).x1)
    let _n2 ← assignAdvice (cfg.state 2) (offset + 1)
      (rowWit w fun s =>
        (PartialRounds.value (PartialRounds.paramsP128 roundConstants r) s).x2)
    readStateRow cfg (offset + 1)

  Witness := State
  extract cfg offset _ self env := eval env (stateRow cfg offset self)

  Spec _ out w := out = PartialRounds.value (PartialRounds.paramsP128 roundConstants r) w

  ProverSpec _ out w _ :=
    out = PartialRounds.value (PartialRounds.paramsP128 roundConstants r) w

  soundness := by
    circuit_proof_start [partialRoundsGate, pow5Expr, stateRow,
      PartialRounds.value, PartialRounds.mid0SboxValue, PartialRounds.paramsP128,
      PartialRounds.params, pow5]
    sorry

  completeness := by
    circuit_proof_start [partialRoundsGate, pow5Expr, stateRow,
      PartialRounds.value, PartialRounds.mid0SboxValue, PartialRounds.paramsP128,
      PartialRounds.params, pow5]
    sorry

end Halo2.Ironwood.Poseidon
