import Clean.Ironwood.Poseidon.Permute

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon/pow5.rs`
- `initial_state` (lines 277-308): a region assigning the domain's initial state from
  constants (`assign_advice_from_constant`: zeros on the rate words, the capacity element
  on the last).
- `add_input` (lines 310-396): a region enabling `s_pad_and_add` at row 1, copying the
  initial state at row 0, the (already-padded) input words at row 1, and assigning the
  summed output state at row 2. For `ConstantLength<2>` both words are `Message` cells —
  no fixed padding.
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon.rs`
- `Hash::hash` for `ConstantLength<2>` (lines 269-286 + the sponge, 100-228): absorb both
  words (buffered), `finish_absorbing` = `add_input` + `permute`, `squeeze` returns
  `state[0]` with no further region. Region sequence: `"initial state for domain
  ConstantLength<2>"`, `"add input for domain ConstantLength<2>"`, `"permute state"`.

The value-level contract is the donor `Hash.HashPaddedBlock.value`
(`Clean/Orchard/Poseidon/Hash.lean`) at capacity `ConstantLength.capacity 2 = 2·2⁶⁴`.
-/

namespace Zcash.Circuits.Poseidon

open Halo2
open Poseidon
open Poseidon.Permute (State)
open Poseidon.Permute.P128Pow5T3 (roundConstants)

/-- A constant witness program. -/
def constWit (c : Fp) : WitgenIR Fp 1 := .native fun _ => #v[c]

@[circuit_norm]
theorem constWit_eval (c : Fp) (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((constWit c).eval env)[j] = c := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [constWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The sum of two read cells. -/
def addWit (a b : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env a + readCell env b]

@[circuit_norm]
theorem addWit_eval (a b : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((addWit a b).eval env)[j] = readCell env a + readCell env b := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [addWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- A copy of one read cell. -/
def readCellWit (a : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env a]

@[circuit_norm]
theorem readCellWit_eval (a : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((readCellWit a).eval env)[j] = readCell env a := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [readCellWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Rust `Pow5Chip::initial_state`'s region body (`pow5.rs:277-308`): the domain's
initial state from constrained constants. -/
def initRegion (capacity : Fp) : FormalRegionCircuit Fp Config Config unit State where
  configure := pure

  synthesize cfg offset _ := do
    let x0 ← assignAdvice (cfg.state 0) offset (constWit 0)
    constrainConstant x0 0
    let x1 ← assignAdvice (cfg.state 1) offset (constWit 0)
    constrainConstant x1 0
    let x2 ← assignAdvice (cfg.state 2) offset (constWit capacity)
    constrainConstant x2 capacity
    pure { x0, x1, x2 }

  Spec _ out _ := out = ({ x0 := 0, x1 := 0, x2 := capacity } : State Fp)
  ProverSpec _ out _ _ := out = ({ x0 := 0, x1 := 0, x2 := capacity } : State Fp)

  soundness := by
    circuit_proof_start
    simp_all only [circuit_norm]
  completeness := by
    circuit_proof_start
    simp_all only [circuit_norm]
    rw [← h_output.1, ← h_output.2.1]

/-- Rust `Pow5Chip::add_input`'s region body (`pow5.rs:310-396`), `ConstantLength<2>`
shape (both rate words are `Message` cells): `s_pad_and_add` at row 1, the initial state
copied at row 0, the input words copied at row 1, the summed output at row 2. `Spec` is
the donor `Sponge.AddInput.value`. -/
def addInputRegion : FormalRegionCircuit Fp Config Config Sponge.AddInputInput State where
  configure := pure

  synthesize cfg offset (input : Var Sponge.AddInputInput Fp) := do
    (padAndAddGate cfg).enable (offset + 1)
    let i0 ← copyAdvice input.initialState.x0 (cfg.state 0) offset
    let i1 ← copyAdvice input.initialState.x1 (cfg.state 1) offset
    let i2 ← copyAdvice input.initialState.x2 (cfg.state 2) offset
    -- pow5.rs:356-362 — `assign_advice` + explicit `constrain_equal(cell, var)`
    -- (source-left orientation, unlike `copy_advice`)
    let w0 ← assignAdvice (cfg.state 0) (offset + 1) (readCellWit input.input.x0)
    constrainEqual input.input.x0 w0
    let w1 ← assignAdvice (cfg.state 1) (offset + 1) (readCellWit input.input.x1)
    constrainEqual input.input.x1 w1
    let o0 ← assignAdvice (cfg.state 0) (offset + 2) (addWit i0 w0)
    let o1 ← assignAdvice (cfg.state 1) (offset + 2) (addWit i1 w1)
    let o2 ← assignAdvice (cfg.state 2) (offset + 2) (readCellWit i2)
    pure { x0 := o0, x1 := o1, x2 := o2 }

  Spec input out _ := out = Sponge.AddInput.value input
  ProverSpec input out _ _ := out = Sponge.AddInput.value input

  soundness := by
    circuit_proof_start [padAndAddGate, Sponge.AddInput.value]
    obtain ⟨⟨g0, g1, g2⟩, c0, c1, c2, c3, c4⟩ := hc
    rw [c0, ← c3] at g0
    rw [c1, ← c4] at g1
    rw [c2] at g2
    exact ⟨by linear_combination -g0, by linear_combination -g1, by linear_combination -g2⟩
  completeness := by
    circuit_proof_start [padAndAddGate, Sponge.AddInput.value, readCell]
    exact ⟨⟨by ring, by ring, by ring⟩,
      h_output.1.symm, h_output.2.1.symm, h_output.2.2.symm⟩

derive_contract_bridges initRegion (capacity : Fp) := initRegion capacity

derive_contract_bridges addInputRegion := addInputRegion

/-- The region count of `hash`: three regions. -/
private theorem hash_regionCount (capacity : Fp) (cfg : Config)
    (input : Var Sponge.Rate2 Fp) (i : RegionIndex) :
    Operations.regionCount
      (((do
        let init ← assignRegion "initial state for domain ConstantLength<2>"
          ((initRegion capacity).call cfg 0 ())
        let absorbed ← assignRegion "add input for domain ConstantLength<2>"
          (addInputRegion.call cfg 0 { initialState := init, input := input })
        let permuted ← assignRegion "permute state"
          (permuteRegion.call cfg 0 absorbed)
        pure permuted.x0) : Circuit Fp (Var field Fp)).operations i)
      = 3 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure, operations_assignRegion,
    Operations.regionCount_append, Operations.regionCount]

/-- Rust `Hash::<ConstantLength<2>>::hash` (`poseidon.rs:269-286`) on the Pow5 chip:
initial state, pad-and-add, one permutation; the digest is `state[0]`. `Spec` is the
donor one-block hash value `HashPaddedBlock.value`. -/
def hash (capacity : Fp) :
    FormalCircuit Fp Config Config Sponge.Rate2 field where
  name := "poseidon hash ConstantLength<2>"
  configure := pure

  synthesize cfg input := do
    let init ← assignRegion "initial state for domain ConstantLength<2>"
      ((initRegion capacity).call cfg 0 ())
    let absorbed ← assignRegion "add input for domain ConstantLength<2>"
      (addInputRegion.call cfg 0 { initialState := init, input := input })
    let permuted ← assignRegion "permute state"
      (permuteRegion.call cfg 0 absorbed)
    pure permuted.x0

  elaborated cfg :=
    { output := fun input i =>
        ((do
          let init ← assignRegion "initial state for domain ConstantLength<2>"
            ((initRegion capacity).call cfg 0 ())
          let absorbed ← assignRegion "add input for domain ConstantLength<2>"
            (addInputRegion.call cfg 0 { initialState := init, input := input })
          let permuted ← assignRegion "permute state"
            (permuteRegion.call cfg 0 absorbed)
          pure permuted.x0) : Circuit Fp (Var field Fp)).output i
      regionCount := fun _ => 3
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i => (hash_regionCount capacity cfg input i).symm }

  Spec input output _ :=
    output = Hash.HashPaddedBlock.value roundConstants capacity input

  ProverSpec input output _ _ :=
    output = Hash.HashPaddedBlock.value roundConstants capacity input

  soundness := by
    circuit_proof_start
    obtain ⟨hInit, hAdd, hPerm⟩ := hc
    have h0 := hInit trivial trivial
    simp only [initRegion_spec_eq] at h0
    have h1 := hAdd trivial trivial
    simp only [addInputRegion_spec_eq] at h1
    have h2 := hPerm trivial trivial
    simp only [permuteRegion_spec_eq] at h2
    rw [h0] at h1
    rw [h1] at h2
    rw [← h_output]
    rw [show env.get x_gen_out_2.x0.cell.column
        ((place x_gen_out_2.x0.cell.regionIndex
          + x_gen_out_2.x0.cell.rowOffset : ℕ) : ℤ)
      = (ProvableStruct.Halo2.eval place env x_gen_out_2 : State Fp).x0 from by
        provable_type_simp]
    rw [h2]
    rfl

  completeness := by
    circuit_proof_start
    have h0 := (h_spec_0 trivial trivial trivial).1
    simp only [initRegion_spec_eq] at h0
    have h1 := (h_spec_1 trivial trivial trivial).1
    simp only [addInputRegion_spec_eq] at h1
    have h2 := (h_spec_2 trivial trivial trivial).1
    simp only [permuteRegion_spec_eq] at h2
    rw [h0] at h1
    rw [h1] at h2
    refine ⟨⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩,
      trivial, trivial, trivial⟩, ?_⟩
    rw [← h_output]
    rw [show env.get x_gen_out_2.x0.cell.column
        ((place x_gen_out_2.x0.cell.regionIndex
          + x_gen_out_2.x0.cell.rowOffset : ℕ) : ℤ)
      = (ProvableStruct.Halo2.eval place env.toEnvironment x_gen_out_2
          : State Fp).x0 from by provable_type_simp]
    rw [h2]
    rw [h_input.1, h_input.2]
    rfl

derive_contract_bridges hash (capacity : Fp) := hash capacity

end Zcash.Circuits.Poseidon
