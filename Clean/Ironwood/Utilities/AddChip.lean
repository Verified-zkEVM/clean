import Clean.Halo2
import Clean.Ironwood.Ecc.Basic

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/gadget/add_chip.rs`
- `AddConfig` (lines 13-19): the three advice columns and the `q_add` selector.
- `AddChip::configure` (lines 43-61): a fresh selector and the single gate
  `"Field element addition: c = a + b"` with the one constraint `a + b - c`, all at
  `Rotation::cur`. No equality side-effects — the caller (orchard `circuit.rs`) enables
  equality on all advices.
- `AddInstruction::add` (lines 71-91): one region `"c = a + b"`; `q_add` at row 0, copy
  `a` and `b` in, assign `c = a + b`.

The phase-one donor is `Clean/Orchard/Utilities.lean` (`Utilities.AddChip`).
-/

namespace Zcash.Circuits.AddChip

open Halo2

/-- Rust `AddConfig` (`add_chip.rs:13-19`). -/
structure Config where
  a : Column .advice
  b : Column .advice
  c : Column .advice
  qAdd : Selector

/-- Rust `"Field element addition: c = a + b"` gate (`add_chip.rs:50-58`): the single
constraint `a + b - c`, all cells at `Rotation::cur`. -/
def addGate (cfg : Config) : Gate Fp :=
  let a : Expression Fp Query := queryAdvice cfg.a 0
  let b : Expression Fp Query := queryAdvice cfg.b 0
  let c : Expression Fp Query := queryAdvice cfg.c 0
  Gate.withSelector "Field element addition: c = a + b" cfg.qAdd
    [a, b, c] [("", a + b - c)]

/-- Rust `AddChip::configure` (`add_chip.rs:43-61`), VK-exact: the fresh `q_add`
selector, then the gate. -/
def configure (a b c : Column .advice) : Configure Fp Config := do
  let qAdd ← selector
  let cfg : Config := { a, b, c, qAdd }
  createGate (addGate cfg)
  return cfg

instance (a b c : Column .advice) :
    ElaboratedConfigure (configure a b c) := by
  unfold configure
  infer_instance

/-- The two summand cells (copied in). -/
structure Inputs (F : Type) where
  a : F
  b : F
deriving ProvableStruct

/-- The sum of two read cells. -/
def sumWit (a b : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env a + readCell env b]

@[circuit_norm]
theorem sumWit_eval (a b : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((sumWit a b).eval env)[j] = readCell env a + readCell env b := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [sumWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Rust `AddInstruction::add`'s region body (`add_chip.rs:71-91`). -/
def synthesize (cfg : Config) (offset : ℕ)
    (input : Inputs (AssignedCell Fp)) : RegionCircuit Fp (AssignedCell Fp) := do
    (addGate cfg).enable offset
    let _a ← copyAdvice input.a cfg.a offset
    let _b ← copyAdvice input.b cfg.b offset
    assignAdvice cfg.c offset (sumWit input.a input.b)

/-- Rust `AddInstruction::add`'s region body (`add_chip.rs:71-91`): `q_add` at row 0,
copy `a` and `b` in, assign `c = a + b`. `Spec`: the output is the field sum. -/
def synthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector cfg.qAdd.index,
      .column .advice cfg.a.index,
      .column .advice cfg.b.index,
      .column .advice cfg.c.index]
    (offset + 1) 0

def add : FormalRegionCircuit Fp Config Config Inputs field where
  configure := pure

  synthesize := synthesize

  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [addGate cfg]
          permutationColumns input _ := [input.a, input.b]
          inputPermutationColumns _ _ input :=
            [input.a.cell.column, input.b.cell.column] }
      registered := by keygen_registration [synthesize]
      output cfg offset _ self := .of self offset cfg.c
      synthesisSummary cfg offset _ _ := synthesisSummary cfg offset
      output_eq := by
        intro _ _ _ _
        simp only [synthesize, circuit_norm]
      synthesisSummary_eq := by
        intro _ _ _ _
        apply FloorPlanner.RegionSynthesisSummary.ext
        · rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns]
          simp only [synthesisSummary, synthesize, circuit_norm, addGate]
          simp only [List.flatMap_cons, List.flatMap_nil,
            FloorPlanner.regionOperationShapeColumns, List.append_nil,
            List.nil_append, List.singleton_append]
        · simp only [synthesisSummary, synthesize, circuit_norm, addGate]
          omega
        · simp only [synthesisSummary, synthesize, circuit_norm, addGate] }

  Spec input output _ := output = input.a + input.b
  ProverSpec input output _ _ := output = input.a + input.b

  soundness := by
    circuit_proof_start [addGate]
    obtain ⟨hg, ha, hb⟩ := hc
    rw [ha, hb] at hg
    linear_combination -hg

  completeness := by
    circuit_proof_start [addGate, readCell]
    exact ⟨by ring, h_output.symm⟩

/-- The layouter-level add: `add` in its own region, named once here as in the Rust
chip (`add_chip.rs`: `assign_region(|| "c = a + b", …)`). -/
def addFormal :=
  add.toFormal "c = a + b"

@[synthesis_summary_norm]
theorem addFormal_synthesisSummary_eq
    (cfg : Config) (input : Var Inputs Fp) (region : RegionIndex) :
    addFormal.elaborated.synthesisSummary cfg input region =
      FloorPlanner.SynthesisSummary.ofRegion (synthesisSummary cfg 0) := rfl

/-- The layouter add capability exported by one AddChip configure run. -/
def addFormalConfigureCertificate (a b c : Column .advice)
    (counts : ConfigureCounts) :
    addFormal.ConfigurationCertificate
      ((configure a b c).output counts)
      { gates := ((configure a b c).delta counts).gates
        lookups := ((configure a b c).delta counts).lookups
        permutationColumns := ([a, b] : List AnyColumn) ++
          ((configure a b c).delta counts).permutationRequests } := by
  let cfg := (configure a b c).output counts
  apply (add.configureCertificate cfg {} ()).mono
  · intro gate hgate
    simp only [add, FormalRegionCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil, List.mem_singleton] at hgate
    subst gate
    simp [cfg, configure]
  · intro argument hargument
    simp only [add, FormalRegionCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil] at hargument
    exact False.elim (List.not_mem_nil hargument)
  · intro column hcolumn
    simpa only [keygen_norm, add, cfg, configure,
      FormalRegionCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements] using hcolumn

derive_contract_bridges addFormal := addFormal

end Zcash.Circuits.AddChip
