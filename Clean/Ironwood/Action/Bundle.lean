import Clean.Ironwood.Action.CircuitPreIronwood

/-!
# The Orchard Action circuit: bundle contract (spec / extract / elaborated)

The e2e statement (protocol spec §4.17.4) over the *extracted* public inputs and
witness data — knowledge-sound at the extracted window scalars, with the Sinsemilla
incomplete-addition escapes carried as data (`SpecOrBreak`, zcash/ironwood#45):

- value-commitment integrity, nullifier integrity, spend authority (total);
- diversified-address integrity, old/new note-commitment integrity (breaks-as-data);
- Merkle path validity and the four `q_orchard` value checks (knowledge-sound at the
  extracted root cell).
-/

open ProvableStruct.Halo2 (eval_cells_eq_eval)

namespace Zcash.Circuits.Action.Circuit

open Halo2
open Ecc.MulFixed (FixedBase)
open Specs.Sinsemilla (Generators hashToPoint hashToPointB SpecOrBreak
  commitIvkChunks)
open CompElliptic.Fields.Pasta (Fq)

/-! ## Region counts -/

/-! ### Per-call `nextRegionIndex` advances

Each of these isolates the `Operations.regionCount ((call).operations j)` reduction into a
small lemma that is kernel-checked once, so that `synthChecks_nextRegionIndex` /
`synthChecks_output` can thread the offset towers using only the folded `= j + literal`
statements (never carrying `regionCount(operations)` into their own kernel-checked terms —
that is what made the `nextRegionIndex_call'`-based compositional proofs kernel-time-out). -/

private theorem merkle_call_nextRegionIndex (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l₀ : ℕ) (hld : l₀ + 16 ≤ 2 ^ 10)
    (wsib : ℕ → WitgenIR Fp 1) (wswap : ℕ → Placed ProverEnvironment Fp → Bool)
    (c : CondSwap.Config × Sinsemilla.Merkle.Config ×
      LookupRangeCheck.Config 10)
    (inp : Var Sinsemilla.Merkle.Layer.Input Fp) (j : RegionIndex) :
    (((Sinsemilla.Merkle.CalculateRoot.circuit G Q hQ l₀ 16 hld wsib wswap).call
        c inp).nextRegionIndex j) = j + 128 := by
  rw [FormalCircuit.nextRegionIndex_call, Sinsemilla.Merkle.CalculateRoot.circuit_call_regionCount]

private theorem vc_call_nextRegionIndex (V : Ecc.MulFixed.Short.FixedBase)
    (R : FixedBase)
    (c : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (inp : Var ValueCommit.Inputs Fp) (j : RegionIndex) :
    (((ValueCommit.circuit V R).call c inp).nextRegionIndex j) = j + 5 := by
  rw [FormalCircuit.nextRegionIndex_call, ValueCommit.circuit_call_regionCount]

private theorem dn_call_nextRegionIndex (K : FixedBase)
    (c : Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config ×
      Ecc.Add.Config)
    (inp : Var DeriveNullifier.Input Fp) (j : RegionIndex) :
    (((DeriveNullifier.circuit K).call c inp).nextRegionIndex j) = j + 9 := by
  rw [FormalCircuit.nextRegionIndex_call, DeriveNullifier.circuit_call_regionCount]

private theorem sa_call_nextRegionIndex (G : FixedBase)
    (c : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (inp : Var SpendAuthority.Input Fp) (j : RegionIndex) :
    (((SpendAuthority.circuit G).call c inp).nextRegionIndex j) = j + 3 := by
  rw [FormalCircuit.nextRegionIndex_call, SpendAuthority.circuit_call_regionCount]

private theorem civk_call_nextRegionIndex (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (c : CommitIvk.Main.Config) (inp : Var CommitIvk.Main.Inputs Fp)
    (j : RegionIndex) :
    (((CommitIvk.Main.circuit G R Q hQ).call c inp).nextRegionIndex j) = j + 14 := by
  rw [FormalCircuit.nextRegionIndex_call, CommitIvk.Main.circuit_call_regionCount]

private theorem ai_call_nextRegionIndex
    (c : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (inp : Var AddressIntegrity.Input Fp) (j : RegionIndex) :
    (((AddressIntegrity.circuit).call c inp).nextRegionIndex j) = j + 6 := by
  rw [FormalCircuit.nextRegionIndex_call, AddressIntegrity.circuit_call_regionCount]

/-- Compose two `nextRegionIndex` advances across a `bind`, over **opaque** `x`/`f`. Proven
once (the `nextRegionIndex_bind` `rfl` is checked with `x`/`f` variables, so the kernel never
reduces a concrete child); `synthChecks_nextRegionIndex` then only *applies* it, so the whole
stage's `nextRegionIndex` is computed without ever unfolding `synthChecks` in a kernel term
(the previous timeout). -/
private theorem nextRegionIndex_advance_bind {α β : Type} {n m N : ℕ}
    {x : Circuit Fp α} {f : α → Circuit Fp β} (hN : n + m = N)
    (hx : ∀ j, x.nextRegionIndex j = j + n)
    (hf : ∀ a j, (f a).nextRegionIndex j = j + m) :
    ∀ j, (x >>= f).nextRegionIndex j = j + N := by
  intro j
  rw [Circuit.nextRegionIndex_bind, hf, hx, Nat.add_assoc, hN]

private theorem nextRegionIndex_advance_pure {α : Type} (a : α) :
    ∀ j, (pure a : Circuit Fp α).nextRegionIndex j = j + 0 := by
  intro j; simp only [Circuit.nextRegionIndex_pure, Nat.add_zero]

private theorem nextRegionIndex_advance_assignRegion {α : Type} (name : String)
    (body : RegionCircuit Fp α) :
    ∀ j, (assignRegion name body).nextRegionIndex j = j + 1 := by
  intro j; rw [nextRegionIndex_assignRegion]

private theorem nextRegionIndex_advance_constrainInstance (cell : AssignedCell Fp)
    (col : Column .instance) (row : ℕ) :
    ∀ j, (constrainInstance cell col row).nextRegionIndex j = j + 0 := by
  intro j; simp only [Nat.add_zero]; rfl

/-- Step the `output` of a `bind` to the tail's output at the advanced index, over opaque
`x`/`f` (same kernel-safety rationale as `nextRegionIndex_advance_bind`). -/
private theorem output_advance_bind {α β : Type} {n : ℕ} {x : Circuit Fp α}
    {f : α → Circuit Fp β} (hx : ∀ j, x.nextRegionIndex j = j + n) (i : RegionIndex) :
    (x >>= f).output i = (f (x.output i)).output (i + n) := by
  rw [Circuit.output_bind, hx]

theorem synthWitness_regionCount (G : Generators) (W : Witnesses Fp) (cfg : Config)
    (i : RegionIndex) :
    Operations.regionCount ((synthWitness G W cfg).operations i) = 8 := by
  simp only [synthWitness, loadPrivate, Sinsemilla.load, circuit_norm,
    Circuit.operations_bind, Circuit.operations_pure, operations_assignRegion,
    operations_loadTable, Operations.regionCount_append, Operations.regionCount]

theorem synthChecks_regionCount (G : Generators) (B : Bases) (W : Witnesses Fp)
    (cfg : Config) (wc : WitnessCells) (i : RegionIndex) :
    Operations.regionCount ((synthChecks G B W cfg wc).operations i) = 295 := by
  simp only [synthChecks, loadPrivate, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, operations_assignRegion, operations_constrainInstance,
    Operations.regionCount_append, Operations.regionCount]

theorem synthNotes_regionCount (G : Generators) (B : Bases) (W : Witnesses Fp)
    (cfg : Config) (wc : WitnessCells) (cc : CheckCells) (i : RegionIndex) :
    Operations.regionCount ((synthNotes G B W cfg wc cc).operations i) = 91 := by
  simp only [synthNotes, loadPrivate, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, operations_assignRegion, operations_constrainInstance,
    Operations.regionCount_append, Operations.regionCount]

/-- The Action circuit's region count: the 8 witness regions, the 295-region check
stage, the 91-region note stage — 394. -/
theorem synthesize_regionCount (G : Generators) (B : Bases) (W : Witnesses Fp)
    (cfg : Config) (i : RegionIndex) :
    Operations.regionCount ((CircuitPreIronwood.synthesize G B W cfg).operations i)
      = 394 := by
  simp only [CircuitPreIronwood.synthesize, synthesizeBase, circuit_norm,
    Circuit.operations_bind, Circuit.operations_pure, Operations.regionCount_append]
  rw [synthWitness_regionCount, synthChecks_regionCount, synthNotes_regionCount]

/-- The `FormalCircuit` entry: the private witness programs in (`PrivateInputs`),
the witnessed old/new-note address point cells out. -/
def main (G : Generators) (B : Bases) (cfg : Config) :
    Var PrivateInputs Fp → Circuit Fp (Var AddressPoints Fp) := fun W =>
  CircuitPreIronwood.synthesize G B W cfg

theorem main_regionCount (G : Generators) (B : Bases) (cfg : Config)
    (W : Witnesses Fp) (i : RegionIndex) :
    Operations.regionCount ((main G B cfg W).operations i) = 394 := by
  simp only [main]
  rw [synthesize_regionCount]

/-! ## The extracted data -/

/-- Everything the Action statement speaks about, read off a satisfying assignment:
the nine public-input rows, the private witness cells, the six witnessed points, and
the five fixed-base window scalars. -/
structure ActionData where
  anchor : Fp
  cvX : Fp
  cvY : Fp
  nfOld : Fp
  rkX : Fp
  rkY : Fp
  cmx : Fp
  enableSpend : Fp
  enableOutput : Fp
  disableCrossAddress : Fp
  psiOld : Fp
  rhoOld : Fp
  nk : Fp
  vOld : Fp
  vNew : Fp
  psiNew : Fp
  magnitude : Fp
  sign : Fp
  cmOld : Point Fp
  gdOld : Point Fp
  akP : Point Fp
  pkdOld : Point Fp
  gdNew : Point Fp
  pkdNew : Point Fp
  merklePath : ℕ → Fp × Fp
  rcv : Vector Fp 85 × Fq
  alpha : Vector Fp 85 × Fq
  rivk : Vector Fp 85 × Fq
  rcmOld : Vector Fp 85 × Fq
  rcmNew : Vector Fp 85 × Fq
deriving Inhabited

/-- One advice cell read. -/
private def cellRead (env : Placed Environment Fp) (i : RegionIndex) (row : ℕ)
    (col : Column .advice) : Fp :=
  eval env (AssignedCell.of i row col : Var field Fp)

/-- The extraction: instance rows off `primary`, witness cells at their regions,
the witnessed points, and the five `fwExtract` window readings (region map in
`synthesize_regionCount`'s docstring). -/
def extract (cfg : Config) (_ : Var PrivateInputs Fp) (i₀ : RegionIndex)
    (env : Placed Environment Fp) : ActionData where
  anchor := env.env.get cfg.primary (ANCHOR : ℤ)
  cvX := env.env.get cfg.primary (CV_NET_X : ℤ)
  cvY := env.env.get cfg.primary (CV_NET_Y : ℤ)
  nfOld := env.env.get cfg.primary (NF_OLD : ℤ)
  rkX := env.env.get cfg.primary (RK_X : ℤ)
  rkY := env.env.get cfg.primary (RK_Y : ℤ)
  cmx := env.env.get cfg.primary (CMX : ℤ)
  enableSpend := env.env.get cfg.primary (ENABLE_SPEND : ℤ)
  enableOutput := env.env.get cfg.primary (ENABLE_OUTPUT : ℤ)
  disableCrossAddress := env.env.get cfg.primary (DISABLE_CROSS_ADDRESS : ℤ)
  psiOld := cellRead env i₀ 0 (cfg.advices 0)
  rhoOld := cellRead env (i₀ + 1) 0 (cfg.advices 0)
  nk := cellRead env (i₀ + 5) 0 (cfg.advices 0)
  vOld := cellRead env (i₀ + 6) 0 (cfg.advices 0)
  vNew := cellRead env (i₀ + 7) 0 (cfg.advices 0)
  psiNew := cellRead env (i₀ + 349) 0 (cfg.advices 0)
  magnitude := cellRead env (i₀ + 264) 0 (cfg.advices 9)
  sign := cellRead env (i₀ + 265) 0 (cfg.advices 9)
  cmOld := ⟨cellRead env (i₀ + 2) 0 cfg.eccConfig.witnessPoint.x,
            cellRead env (i₀ + 2) 0 cfg.eccConfig.witnessPoint.y⟩
  gdOld := ⟨cellRead env (i₀ + 3) 0 cfg.eccConfig.witnessPoint.x,
            cellRead env (i₀ + 3) 0 cfg.eccConfig.witnessPoint.y⟩
  akP := ⟨cellRead env (i₀ + 4) 0 cfg.eccConfig.witnessPoint.x,
          cellRead env (i₀ + 4) 0 cfg.eccConfig.witnessPoint.y⟩
  pkdOld := ⟨cellRead env (i₀ + 301) 0 cfg.eccConfig.witnessPoint.x,
             cellRead env (i₀ + 301) 0 cfg.eccConfig.witnessPoint.y⟩
  gdNew := ⟨cellRead env (i₀ + 347) 0 cfg.eccConfig.witnessPoint.x,
            cellRead env (i₀ + 347) 0 cfg.eccConfig.witnessPoint.y⟩
  pkdNew := ⟨cellRead env (i₀ + 348) 0 cfg.eccConfig.witnessPoint.x,
             cellRead env (i₀ + 348) 0 cfg.eccConfig.witnessPoint.y⟩
  merklePath := fun j =>
    if j < 16 then
      (cellRead env (i₀ + 8 + 8 * j) 0 cfg.merkle1.condSwap.b,
       cellRead env (i₀ + 8 + 8 * j) 0 cfg.merkle1.condSwap.swap)
    else
      (cellRead env (i₀ + 136 + 8 * (j - 16)) 0 cfg.merkle2.condSwap.b,
       cellRead env (i₀ + 136 + 8 * (j - 16)) 0 cfg.merkle2.condSwap.swap)
  rcv := Ecc.MulFixed.FullWidth.fwExtract cfg.eccConfig.mulFixedFull (i₀ + 268) env
  alpha := Ecc.MulFixed.FullWidth.fwExtract cfg.eccConfig.mulFixedFull (i₀ + 280) env
  rivk := Ecc.MulFixed.FullWidth.fwExtract cfg.eccConfig.mulFixedFull (i₀ + 290) env
  rcmOld := Ecc.MulFixed.FullWidth.fwExtract cfg.eccConfig.mulFixedFull (i₀ + 328) env
  rcmNew := Ecc.MulFixed.FullWidth.fwExtract cfg.eccConfig.mulFixedFull (i₀ + 375) env

/-! ## The statement (§4.17.4, knowledge-sound, breaks-as-data) -/

open NoteCommit (noteScalars)

/-- The Orchard Action statement over the extracted data: every §4.17.4 clause, with
the Sinsemilla escapes exhibited as data and the fixed-base scalars knowledge-sound at
the extracted window readings. -/
def SpecBase (G : Generators) (B : Bases) (wit : ActionData) : Prop :=
  -- the witnessed points are well-formed
  wit.cmOld.Valid ∧ wit.gdOld.OnCurve ∧ wit.akP.OnCurve ∧ wit.pkdOld.OnCurve ∧
  wit.gdNew.OnCurve ∧ wit.pkdNew.OnCurve ∧
  -- the note values are 64-bit, as §4.17.4 types them (exported from the NoteCommit
  -- value decompositions; the commitment clauses alone can't bound the field elements)
  wit.vOld.val < 2 ^ 64 ∧ wit.vNew.val < 2 ^ 64 ∧
  -- value-commitment integrity: `cv_net = [v_old − v_new] V + [rcv] R`
  (wit.magnitude.val < 2 ^ 64 ∧
    ((wit.sign = 1 ∧ (⟨wit.cvX, wit.cvY⟩ : Point Fp)
        = (wit.magnitude.val : Fq) • B.valueCommitV
          + wit.rcv.2 • B.valueCommitR) ∨
     (wit.sign = -1 ∧ (⟨wit.cvX, wit.cvY⟩ : Point Fp)
        = -(wit.magnitude.val : Fq) • B.valueCommitV
          + wit.rcv.2 • B.valueCommitR))) ∧
  -- nullifier integrity: `nf_old = Extract([PRF(nk, ρ) + ψ] K + cm_old)`
  wit.nfOld = (wit.cmOld +
    ((Poseidon.Hash.ConstantLength.value #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq)
      • B.nullifierK).x ∧
  -- spend authority: `rk = [α] SpendAuthG + ak_P`
  (⟨wit.rkX, wit.rkY⟩ : Point Fp)
    = wit.alpha.2 • B.spendAuthG + wit.akP ∧
  -- diversified-address integrity: `ivk ∈ {Commit^ivk, ⊥}` (break exhibited) and
  -- `pk_d_old = [ivk] g_d_old`
  (∃ ivk : Fp,
    SpecOrBreak G.S B.ivkQ
      (fun bp => ivk = (bp + wit.rivk.2 • B.commitIvkR).x)
      (hashToPointB G.S B.ivkQ (commitIvkChunks wit.akP.x.val wit.nk.val)) ∧
    wit.pkdOld = ivk.val • wit.gdOld) ∧
  -- old note-commitment integrity: `NoteCommit(…) ∈ {cm_old, ⊥}` (break exhibited)
  SpecOrBreak G.S B.noteQ
    (fun bp => wit.cmOld = bp + wit.rcmOld.2 • B.noteCommitR)
    (hashToPointB G.S B.noteQ
      (noteScalars wit.gdOld wit.pkdOld wit.vOld wit.rhoOld wit.psiOld).chunks) ∧
  -- new note-commitment integrity, `ρ_new = nf_old`:
  -- `Extract(NoteCommit(…)) ∈ {cmx, ⊥}` (break exhibited)
  SpecOrBreak G.S B.noteQ
    (fun bp => wit.cmx = (bp + wit.rcmNew.2 • B.noteCommitR).x)
    (hashToPointB G.S B.noteQ
      (noteScalars wit.gdNew wit.pkdNew wit.vNew wit.nfOld wit.psiNew).chunks) ∧
  -- Merkle path validity, tied through the `q_orchard` anchor check. The strict-or-break
  -- refinement exhibits any Sinsemilla escape as data, as requested by zcash/ironwood#45.
  (∃ root : Fp,
    Sinsemilla.Merkle.MerkleRoot G B.merkleQ 0 wit.cmOld.x 32 root ∧
    (Sinsemilla.Merkle.MerkleRootStrict G B.merkleQ 0 wit.cmOld.x 32 root ∨
      Sinsemilla.Merkle.MerkleBreakAt G B.merkleQ 0 32) ∧
    wit.vOld * (root - wit.anchor) = 0) ∧
  -- the remaining `q_orchard` value checks
  wit.vOld - wit.vNew = wit.magnitude * wit.sign ∧
  wit.vOld * (1 - wit.enableSpend) = 0 ∧
  wit.vNew * (1 - wit.enableOutput) = 0

/-- The pre-ironwood bundle's contract: the base statement, plus the output cells
carrying the four witnessed address points (what the ironwood cross-address stage
consumes). -/
def Spec (G : Generators) (B : Bases)
    (_ : Value PrivateInputs Fp) (out : Value AddressPoints Fp) (wit : ActionData) :
    Prop :=
  SpecBase G B wit ∧ out.gdOld = wit.gdOld ∧ out.pkdOld = wit.pkdOld ∧
  out.gdNew = wit.gdNew ∧ out.pkdNew = wit.pkdNew

/-- The generator table holds *exactly* the `load` contents (block + default fill) —
the completeness-side strengthening of `GeneratorTableLoaded` (the honest env is one
that ran the load). Stated as the load's own constraint set (place-independent). -/
def GeneratorTableExact (G : Generators) (cfg : Sinsemilla.GeneratorTableConfig)
    (env : Environment Fp) : Prop :=
  Halo2.Constraints (fun _ => 0) env
    ((Sinsemilla.load G cfg).operations 0) 0

private theorem generatorTableExact_constraints (G : Generators)
    (cfg : Sinsemilla.GeneratorTableConfig) (env : Environment Fp)
    (h : GeneratorTableExact G cfg env) (place : RegionIndex → ℕ) (i : RegionIndex) :
    Halo2.Constraints place env ((Sinsemilla.load G cfg).operations i) i := by
  simp only [GeneratorTableExact, Sinsemilla.load, circuit_norm] at h ⊢
  exact h

/-- Env preconditions: the loaded tables and selector-distinctness every child asserts. -/
def EnvAssumptions (G : Generators) (cfg : Config)
    (env : Placed Environment Fp) : Prop :=
  GeneratorTableExact G cfg.sinsemilla1.generatorTable env.env ∧
  Sinsemilla.GeneratorTableLoaded G cfg.sinsemilla1.generatorTable env.env ∧
  Sinsemilla.GeneratorTableLoaded G cfg.sinsemilla2.generatorTable env.env ∧
  Sinsemilla.GeneratorTableLoaded G cfg.merkle1.sinsemilla.generatorTable env.env ∧
  Sinsemilla.GeneratorTableLoaded G cfg.merkle2.sinsemilla.generatorTable env.env ∧
  Ecc.MulFixed.FullWidth.EnvAssumptions cfg.eccConfig.mulFixedFull env ∧
  Ecc.MulFixed.Short.EnvAssumptions cfg.eccConfig.mulFixedShort env ∧
  Ecc.MulFixed.BaseFieldElem.EnvAssumptions cfg.eccConfig.mulFixedBaseField env ∧
  Ecc.Mul.EnvAssumptions cfg.eccConfig.mul env ∧
  LookupRangeCheck.TableLoaded 10 cfg.lookupConfig env.env ∧
  cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index

/-- Witness-consistency bridge: the honest prover's evaluated point hint equals the point
read from the witnessed output cells. From the region's `ExtendsWitnesses` alone (no gate
constraints), so it is available to discharge the value-level `ProverAssumptions` of the
`WitnessPoint` children against the Action bundle's extract-level facts. -/
private theorem wpoint_eval_eq_cells
    (c : Ecc.WitnessPoint.Config) (p : Var (Unconstrained Point) Fp)
    (i : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (hw : Halo2.ExtendsWitnesses place env
      ((Ecc.WitnessPoint.pointFormal.call c p).operations i) i) :
    eval (⟨place, env⟩ : Placed ProverEnvironment Fp) p
      = (⟨eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (AssignedCell.of i 0 c.x : Var field Fp),
          eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (AssignedCell.of i 0 c.y : Var field Fp)⟩ : Point Fp) := by
  rw [FormalCircuit.call_operations] at hw
  simp only [Ecc.WitnessPoint.pointFormal, Ecc.WitnessPoint.point, FormalRegionCircuit.toFormal, circuit_norm,
    RegionOperation.extendsWitness_assignAdvice] at hw
  apply Point.ext_coords
  have hx : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
      (AssignedCell.of i 0 c.x : Var field Fp) : Fp) = env.advice c.x ↑(place i) := by
    simp only [circuit_norm, explicit_provable_type]
  have hy : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
      (AssignedCell.of i 0 c.y : Var field Fp) : Fp) = env.advice c.y ↑(place i) := by
    simp only [circuit_norm, explicit_provable_type]
  simp only [Point.coords, hx, hy, hw.1, hw.2]
  simp only [circuit_norm, explicit_provable_type]

private theorem wpointNonId_eval_eq_cells
    (c : Ecc.WitnessPoint.Config) (p : Var (Unconstrained Point) Fp)
    (i : RegionIndex) (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (hw : Halo2.ExtendsWitnesses place env
      ((Ecc.WitnessPoint.pointNonIdFormal.call c p).operations i) i) :
    eval (⟨place, env⟩ : Placed ProverEnvironment Fp) p
      = (⟨eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (AssignedCell.of i 0 c.x : Var field Fp),
          eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (AssignedCell.of i 0 c.y : Var field Fp)⟩ : Point Fp) := by
  rw [FormalCircuit.call_operations] at hw
  simp only [Ecc.WitnessPoint.pointNonIdFormal, Ecc.WitnessPoint.pointNonId, FormalRegionCircuit.toFormal, circuit_norm,
    RegionOperation.extendsWitness_assignAdvice] at hw
  apply Point.ext_coords
  have hx : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
      (AssignedCell.of i 0 c.x : Var field Fp) : Fp) = env.advice c.x ↑(place i) := by
    simp only [circuit_norm, explicit_provable_type]
  have hy : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
      (AssignedCell.of i 0 c.y : Var field Fp) : Fp) = env.advice c.y ↑(place i) := by
    simp only [circuit_norm, explicit_provable_type]
  simp only [Point.coords, hx, hy, hw.1, hw.2]
  simp only [circuit_norm, explicit_provable_type]

private theorem wpoint_output (c : Ecc.WitnessPoint.Config)
    (inp : Var (Unconstrained Point) Fp) (i : RegionIndex) :
    Ecc.WitnessPoint.pointFormal.output c inp i
      = ({ x := AssignedCell.of i 0 c.x, y := AssignedCell.of i 0 c.y }
        : Var Point Fp) := rfl

private theorem wpointNonId_output (c : Ecc.WitnessPoint.Config)
    (inp : Var (Unconstrained Point) Fp) (i : RegionIndex) :
    Ecc.WitnessPoint.pointNonIdFormal.output c inp i
      = ({ x := AssignedCell.of i 0 c.x, y := AssignedCell.of i 0 c.y }
        : Var Point Fp) := rfl

private theorem ai_output
    (c : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (inp : Var AddressIntegrity.Input Fp) (i : RegionIndex) :
    (AddressIntegrity.circuit).output c inp i
      = ({ x := AssignedCell.of (i + 4) 0 c.2.x, y := AssignedCell.of (i + 4) 0 c.2.y }
        : Var Point Fp) := by
  change ((do
    let derived ← Ecc.Mul.mul.call c.1 { alpha := inp.ivk, base := inp.gDOld }
    let pkDOld ← Ecc.WitnessPoint.pointNonIdFormal.call c.2 inp.pkDOld
    assignRegion "constrain equal" (do
      constrainEqual derived.x pkDOld.x
      constrainEqual derived.y pkDOld.y)
    pure pkDOld : Circuit Fp (Var Point Fp)).output i) = _
  simp only [Circuit.output_bind, Circuit.output_pure,
    FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call']
  rw [Ecc.Mul.mul_call_regionCount, wpointNonId_output]

private theorem ncInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c1 c2 c3 c4 c5 c6 c7 : AssignedCell Fp) (r : Var UnconstrainedNat Fp) :
    (eval (Var := Var NoteCommit.Main.Inputs Fp) (⟨place, env⟩ : Placed Environment Fp)
      { gdX := c1, gdY := c2, pkdX := c3, pkdY := c4, value := c5, rho := c6,
        psi := c7, rcm := r })
    = { gdX := eval (⟨place, env⟩ : Placed Environment Fp) (c1 : Var field Fp),
        gdY := eval (⟨place, env⟩ : Placed Environment Fp) (c2 : Var field Fp),
        pkdX := eval (⟨place, env⟩ : Placed Environment Fp) (c3 : Var field Fp),
        pkdY := eval (⟨place, env⟩ : Placed Environment Fp) (c4 : Var field Fp),
        value := eval (⟨place, env⟩ : Placed Environment Fp) (c5 : Var field Fp),
        rho := eval (⟨place, env⟩ : Placed Environment Fp) (c6 : Var field Fp),
        psi := eval (⟨place, env⟩ : Placed Environment Fp) (c7 : Var field Fp),
        rcm := () } := by
  simp only [circuit_norm, explicit_provable_type]

private theorem vcInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c1 c2 : AssignedCell Fp) (r : Var UnconstrainedNat Fp) :
    (eval (Var := Var ValueCommit.Inputs Fp) (⟨place, env⟩ : Placed Environment Fp)
      { rcv := r, magnitude := c1, sign := c2 })
    = { rcv := (), magnitude := eval (⟨place, env⟩ : Placed Environment Fp) (c1 : Var field Fp),
        sign := eval (⟨place, env⟩ : Placed Environment Fp) (c2 : Var field Fp) } := by
  simp only [circuit_norm, explicit_provable_type]

private theorem dnInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c1 c2 c3 : AssignedCell Fp) (p : Point (AssignedCell Fp)) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ({ nk := c1, rho := c2, psi := c3, cm := p } : Var DeriveNullifier.Input Fp))
    = { nk := eval (⟨place, env⟩ : Placed Environment Fp) (c1 : Var field Fp),
        rho := eval (⟨place, env⟩ : Placed Environment Fp) (c2 : Var field Fp),
        psi := eval (⟨place, env⟩ : Placed Environment Fp) (c3 : Var field Fp),
        cm := eval (⟨place, env⟩ : Placed Environment Fp) (p : Var Point Fp) } := by
  rw [eval_cells_eq_eval]
  simp only [circuit_norm, explicit_provable_type]

private theorem saInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (p : Point (AssignedCell Fp)) (a : Var UnconstrainedNat Fp) :
    (eval (Var := Var SpendAuthority.Input Fp) (⟨place, env⟩ : Placed Environment Fp)
      { alpha := a, akP := p })
    = { alpha := (), akP := eval (⟨place, env⟩ : Placed Environment Fp) (p : Var Point Fp) } := by
  simp only [circuit_norm, explicit_provable_type]

private theorem civkInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c1 c2 : AssignedCell Fp) (r : Var UnconstrainedNat Fp) :
    (eval (Var := Var CommitIvk.Main.Inputs Fp) (⟨place, env⟩ : Placed Environment Fp)
      { ak := c1, nk := c2, rivk := r })
    = { ak := eval (⟨place, env⟩ : Placed Environment Fp) (c1 : Var field Fp),
        nk := eval (⟨place, env⟩ : Placed Environment Fp) (c2 : Var field Fp),
        rivk := () } := by
  simp only [circuit_norm, explicit_provable_type]

private theorem aiInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c1 : AssignedCell Fp) (p : Point (AssignedCell Fp))
    (pk : Var (Unconstrained Point) Fp) :
    (eval (Var := Var AddressIntegrity.Input Fp) (⟨place, env⟩ : Placed Environment Fp)
      { ivk := c1, gDOld := p, pkDOld := pk })
    = { ivk := eval (⟨place, env⟩ : Placed Environment Fp) (c1 : Var field Fp),
        gDOld := eval (⟨place, env⟩ : Placed Environment Fp) (p : Var Point Fp),
        pkDOld := () } := by
  simp only [circuit_norm, explicit_provable_type]

private theorem layerInput_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c : AssignedCell Fp) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ({ node := c } : Var Sinsemilla.Merkle.Layer.Input Fp))
    = { node := eval (⟨place, env⟩ : Placed Environment Fp) (c : Var field Fp) } := by
  rw [eval_cells_eq_eval]
  simp only [circuit_norm, explicit_provable_type]

private theorem vcInputs_eval_eq_prover (place : RegionIndex → ℕ)
    (env : ProverEnvironment Fp) (c1 c2 : AssignedCell Fp)
    (r : Var UnconstrainedNat Fp) :
    (eval (Var := Var ValueCommit.Inputs Fp) (⟨place, env⟩ : Placed ProverEnvironment Fp)
      { rcv := r, magnitude := c1, sign := c2 })
    = { rcv := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (r : Var UnconstrainedNat Fp),
        magnitude := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (c1 : Var field Fp),
        sign := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (c2 : Var field Fp) } := by
  simp only [circuit_norm, explicit_provable_type]

private theorem civkInputs_eval_eq_prover (place : RegionIndex → ℕ)
    (env : ProverEnvironment Fp) (c1 c2 : AssignedCell Fp)
    (r : Var UnconstrainedNat Fp) :
    (eval (Var := Var CommitIvk.Main.Inputs Fp) (⟨place, env⟩ : Placed ProverEnvironment Fp)
      { ak := c1, nk := c2, rivk := r })
    = { ak := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c1 : Var field Fp),
        nk := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (c2 : Var field Fp),
        rivk := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (r : Var UnconstrainedNat Fp) } := by
  simp only [circuit_norm, explicit_provable_type]

private theorem aiInputs_eval_eq_prover (place : RegionIndex → ℕ)
    (env : ProverEnvironment Fp) (c1 : AssignedCell Fp) (p : Point (AssignedCell Fp))
    (pk : Var (Unconstrained Point) Fp) :
    (eval (Var := Var AddressIntegrity.Input Fp) (⟨place, env⟩ : Placed ProverEnvironment Fp)
      { ivk := c1, gDOld := p, pkDOld := pk })
    = { ivk := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c1 : Var field Fp),
        gDOld := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (p : Var Point Fp),
        pkDOld := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (pk : Var (Unconstrained Point) Fp) } := by
  simp only [circuit_norm, explicit_provable_type]

private theorem ncInputs_eval_eq_prover (place : RegionIndex → ℕ)
    (env : ProverEnvironment Fp) (c1 c2 c3 c4 c5 c6 c7 : AssignedCell Fp)
    (r : Var UnconstrainedNat Fp) :
    (eval (Var := Var NoteCommit.Main.Inputs Fp) (⟨place, env⟩ : Placed ProverEnvironment Fp)
      { gdX := c1, gdY := c2, pkdX := c3, pkdY := c4, value := c5, rho := c6,
        psi := c7, rcm := r })
    = { gdX := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c1 : Var field Fp),
        gdY := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c2 : Var field Fp),
        pkdX := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c3 : Var field Fp),
        pkdY := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c4 : Var field Fp),
        value := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c5 : Var field Fp),
        rho := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c6 : Var field Fp),
        psi := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (c7 : Var field Fp),
        rcm := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (r : Var UnconstrainedNat Fp) } := by
  simp only [circuit_norm, explicit_provable_type]

/-! ## Stage outputs and offsets -/

private theorem nextRegionIndex_constrainInstance (cell : AssignedCell Fp)
    (col : Column .instance) (row : ℕ) (i : RegionIndex) :
    (constrainInstance cell col row).nextRegionIndex i = i := rfl

theorem synthWitness_nextRegionIndex (G : Generators) (W : Witnesses Fp) (cfg : Config)
    (i : RegionIndex) :
    (synthWitness G W cfg).nextRegionIndex i = i + 8 := by
  simp only [synthWitness, Sinsemilla.load, loadPrivate, circuit_norm,
    Circuit.nextRegionIndex_bind, Circuit.nextRegionIndex_pure,
    nextRegionIndex_loadTable, nextRegionIndex_assignRegion,
    FormalCircuit.nextRegionIndex_call']

theorem synthWitness_output (G : Generators) (W : Witnesses Fp) (cfg : Config)
    (i : RegionIndex) :
    (synthWitness G W cfg).output i
      = { psiOld := .of i 0 (cfg.advices 0),
          rhoOld := .of (i + 1) 0 (cfg.advices 0),
          cmOld := { x := AssignedCell.of (i + 2) 0 cfg.eccConfig.witnessPoint.x,
                     y := AssignedCell.of (i + 2) 0 cfg.eccConfig.witnessPoint.y },
          gdOld := { x := AssignedCell.of (i + 3) 0 cfg.eccConfig.witnessPoint.x,
                     y := AssignedCell.of (i + 3) 0 cfg.eccConfig.witnessPoint.y },
          akP := { x := AssignedCell.of (i + 4) 0 cfg.eccConfig.witnessPoint.x,
                   y := AssignedCell.of (i + 4) 0 cfg.eccConfig.witnessPoint.y },
          nk := .of (i + 5) 0 (cfg.advices 0),
          vOld := .of (i + 6) 0 (cfg.advices 0),
          vNew := .of (i + 7) 0 (cfg.advices 0) } := by
  simp only [synthWitness, Sinsemilla.load, loadPrivate,
    Circuit.output_bind, Circuit.output_pure, Circuit.nextRegionIndex_bind,
    nextRegionIndex_loadTable, output_assignRegion, nextRegionIndex_assignRegion,
    output_assignAdvice, FormalCircuit.output_call',
    FormalCircuit.nextRegionIndex_call']
  rw [wpointNonId_output, Ecc.WitnessPoint.pointNonIdFormal_call_regionCount,
    wpointNonId_output, Ecc.WitnessPoint.pointNonIdFormal_call_regionCount,
    wpoint_output, Ecc.WitnessPoint.pointFormal_call_regionCount]

theorem synthChecks_nextRegionIndex (G : Generators) (B : Bases) (W : Witnesses Fp)
    (cfg : Config) (wc : WitnessCells) (i : RegionIndex) :
    (synthChecks G B W cfg wc).nextRegionIndex i = i + 295 := by
  -- Compose the per-call advances across the bind chain with `nextRegionIndex_advance_bind`,
  -- whose statement is over opaque `x`/`f`; applying it never unfolds `synthChecks` in the
  -- kernel term, so the enlarged children are never reduced (the previous timeout).
  suffices h : ∀ j, (synthChecks G B W cfg wc).nextRegionIndex j = j + 295 from h i
  simp only [synthChecks, loadPrivate]
  refine nextRegionIndex_advance_bind (n := 128) (m := 167) (by norm_num)
    (merkle_call_nextRegionIndex _ _ _ _ _ _ _ _ _) ?_; intro half
  refine nextRegionIndex_advance_bind (n := 128) (m := 39) (by norm_num)
    (merkle_call_nextRegionIndex _ _ _ _ _ _ _ _ _) ?_; intro root
  refine nextRegionIndex_advance_bind (n := 1) (m := 38) (by norm_num)
    (nextRegionIndex_advance_assignRegion _ _) ?_; intro magnitude
  refine nextRegionIndex_advance_bind (n := 1) (m := 37) (by norm_num)
    (nextRegionIndex_advance_assignRegion _ _) ?_; intro sign
  refine nextRegionIndex_advance_bind (n := 5) (m := 32) (by norm_num)
    (vc_call_nextRegionIndex _ _ _ _) ?_; intro cvNet
  refine nextRegionIndex_advance_bind (n := 0) (m := 32) (by norm_num)
    (nextRegionIndex_advance_constrainInstance _ _ _) ?_; intro _
  refine nextRegionIndex_advance_bind (n := 0) (m := 32) (by norm_num)
    (nextRegionIndex_advance_constrainInstance _ _ _) ?_; intro _
  refine nextRegionIndex_advance_bind (n := 9) (m := 23) (by norm_num)
    (dn_call_nextRegionIndex _ _ _) ?_; intro nfOld
  refine nextRegionIndex_advance_bind (n := 0) (m := 23) (by norm_num)
    (nextRegionIndex_advance_constrainInstance _ _ _) ?_; intro _
  refine nextRegionIndex_advance_bind (n := 3) (m := 20) (by norm_num)
    (sa_call_nextRegionIndex _ _ _) ?_; intro rk
  refine nextRegionIndex_advance_bind (n := 0) (m := 20) (by norm_num)
    (nextRegionIndex_advance_constrainInstance _ _ _) ?_; intro _
  refine nextRegionIndex_advance_bind (n := 0) (m := 20) (by norm_num)
    (nextRegionIndex_advance_constrainInstance _ _ _) ?_; intro _
  refine nextRegionIndex_advance_bind (n := 14) (m := 6) (by norm_num)
    (civk_call_nextRegionIndex _ _ _ _ _ _) ?_; intro ivk
  refine nextRegionIndex_advance_bind (n := 6) (m := 0) (by norm_num)
    (ai_call_nextRegionIndex _ _) ?_; intro pkdOld
  exact nextRegionIndex_advance_pure _

theorem synthChecks_output (G : Generators) (B : Bases) (W : Witnesses Fp)
    (cfg : Config) (wc : WitnessCells) (i : RegionIndex) :
    (synthChecks G B W cfg wc).output i
      = { root := (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ
            B.merkleQ_onCurve 16 16 (by norm_num) (fun j => W.merkleSib (16 + j))
            (fun j => W.merkleSwap (16 + j))).output
            (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig)
            { node := (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ
                B.merkleQ_onCurve 0 16 (by norm_num) W.merkleSib W.merkleSwap).output
                (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig)
                { node := wc.cmOld.x } i }
            (i + 128),
          magnitude := .of (i + 256) 0 (cfg.advices 9),
          sign := .of (i + 257) 0 (cfg.advices 9),
          nfOld := (DeriveNullifier.circuit B.nullifierK).output
            (cfg.poseidonConfig, cfg.addChipConfig, cfg.eccConfig.mulFixedBaseField,
             cfg.eccConfig.add)
            { nk := wc.nk, rho := wc.rhoOld, psi := wc.psiOld, cm := wc.cmOld }
            (i + 263),
          pkdOld := { x := AssignedCell.of (i + 293) 0 cfg.eccConfig.witnessPoint.x,
                      y := AssignedCell.of (i + 293) 0 cfg.eccConfig.witnessPoint.y } }
      := by
  -- Thread the output through the bind chain with `output_advance_bind` (opaque `x`/`f`, so
  -- the kernel never unfolds `synthChecks`), then reduce the child outputs to their stated
  -- spellings and fold the offset towers.
  simp only [synthChecks, loadPrivate]
  rw [output_advance_bind (merkle_call_nextRegionIndex _ _ _ _ _ _ _ _ _),
    output_advance_bind (merkle_call_nextRegionIndex _ _ _ _ _ _ _ _ _),
    output_advance_bind (nextRegionIndex_advance_assignRegion _ _),
    output_advance_bind (nextRegionIndex_advance_assignRegion _ _),
    output_advance_bind (vc_call_nextRegionIndex _ _ _ _),
    output_advance_bind (nextRegionIndex_advance_constrainInstance _ _ _),
    output_advance_bind (nextRegionIndex_advance_constrainInstance _ _ _),
    output_advance_bind (dn_call_nextRegionIndex _ _ _),
    output_advance_bind (nextRegionIndex_advance_constrainInstance _ _ _),
    output_advance_bind (sa_call_nextRegionIndex _ _ _),
    output_advance_bind (nextRegionIndex_advance_constrainInstance _ _ _),
    output_advance_bind (nextRegionIndex_advance_constrainInstance _ _ _),
    output_advance_bind (civk_call_nextRegionIndex _ _ _ _ _ _),
    output_advance_bind (ai_call_nextRegionIndex _ _),
    Circuit.output_pure]
  simp only [output_assignRegion, output_assignAdvice, FormalCircuit.output_call',
    ai_output, Nat.add_assoc, Nat.reduceAdd]

theorem synthNotes_output (G : Generators) (B : Bases) (W : Witnesses Fp)
    (cfg : Config) (wc : WitnessCells) (cc : CheckCells) (i : RegionIndex) :
    (synthNotes G B W cfg wc cc).output i
      = { gdNew := { x := AssignedCell.of (i + 44) 0 cfg.eccConfig.witnessPoint.x,
                     y := AssignedCell.of (i + 44) 0 cfg.eccConfig.witnessPoint.y },
          pkdNew := { x := AssignedCell.of (i + 45) 0 cfg.eccConfig.witnessPoint.x,
                      y := AssignedCell.of (i + 45) 0 cfg.eccConfig.witnessPoint.y } } := by
  simp only [synthNotes, loadPrivate, Circuit.output_bind, Circuit.output_pure,
    output_assignRegion, nextRegionIndex_assignRegion,
    nextRegionIndex_constrainInstance, output_assignAdvice, FormalCircuit.output_call',
    FormalCircuit.nextRegionIndex_call']
  rw [NoteCommit.Main.circuit_call_regionCount, Ecc.WitnessPoint.pointNonIdFormal_call_regionCount,
    wpointNonId_output, wpointNonId_output]

instance elaborated (G : Generators) (B : Bases) (cfg : Config) :
    ElaboratedCircuit Fp PrivateInputs AddressPoints (main G B cfg) where
  output _ i₀ :=
    { gdOld := { x := AssignedCell.of (i₀ + 3) 0 cfg.eccConfig.witnessPoint.x,
                 y := AssignedCell.of (i₀ + 3) 0 cfg.eccConfig.witnessPoint.y },
      pkdOld := { x := AssignedCell.of (i₀ + 301) 0 cfg.eccConfig.witnessPoint.x,
                  y := AssignedCell.of (i₀ + 301) 0 cfg.eccConfig.witnessPoint.y },
      gdNew := { x := AssignedCell.of (i₀ + 347) 0 cfg.eccConfig.witnessPoint.x,
                 y := AssignedCell.of (i₀ + 347) 0 cfg.eccConfig.witnessPoint.y },
      pkdNew := { x := AssignedCell.of (i₀ + 348) 0 cfg.eccConfig.witnessPoint.x,
                  y := AssignedCell.of (i₀ + 348) 0 cfg.eccConfig.witnessPoint.y } }
  regionCount _ := 394
  output_eq := by
    intro W i₀
    simp only [main, CircuitPreIronwood.synthesize, synthesizeBase,
      Circuit.output_bind, Circuit.output_pure,
      synthWitness_output, synthWitness_nextRegionIndex, synthChecks_output,
      synthChecks_nextRegionIndex, synthNotes_output]
  regionCount_eq := fun W i => (main_regionCount G B cfg W i).symm

/-! ## Soundness -/

open Sinsemilla.Merkle (MerkleRoot)

theorem soundness (G : Generators) (B : Bases) (cfg : Config) :
    FormalCircuit.Soundness (Witness := fun _ => ActionData)
      (main G B cfg) (extract cfg) (EnvAssumptions G cfg) (fun _ => True)
      (Spec G B) := by
  circuit_proof_start
  obtain ⟨hTE, hT1, hT2, hTM1, hTM2, hFw, hSh, hBf, hMulE, hTL, hDist⟩ := _hE
  simp only [CircuitPreIronwood.synthesize, synthesizeBase, circuit_norm] at hc
  have hW := hc.1
  have hCk := hc.2.1
  have hN := hc.2.2
  clear hc
  -- ── stage A: the witness regions ──
  simp only [synthWitness, loadPrivate, Sinsemilla.load, circuit_norm] at hW
  have hCm := hW.2.2.2.2.2.2.1
  have hGd := hW.2.2.2.2.2.2.2.1
  have hAk := hW.2.2.2.2.2.2.2.2
  clear hW
  simp only [Nat.add_assoc, Nat.reduceAdd] at hGd hAk
  subcircuit_rw at hCm
  subcircuit_rw at hGd
  subcircuit_rw at hAk
  have hCmS := hCm (by rw [Ecc.WitnessPoint.pointFormal_envAssumptions_eq]; trivial)
    (by rw [Ecc.WitnessPoint.pointFormal_assumptions_eq]; trivial)
  rw [Ecc.WitnessPoint.pointFormal_spec_eq, wpoint_output] at hCmS
  have hGdS := hGd (by rw [Ecc.WitnessPoint.pointNonIdFormal_envAssumptions_eq]; trivial)
    (by rw [Ecc.WitnessPoint.pointNonIdFormal_assumptions_eq]; trivial)
  rw [Ecc.WitnessPoint.pointNonIdFormal_spec_eq, wpointNonId_output] at hGdS
  have hAkS := hAk (by rw [Ecc.WitnessPoint.pointNonIdFormal_envAssumptions_eq]; trivial)
    (by rw [Ecc.WitnessPoint.pointNonIdFormal_assumptions_eq]; trivial)
  rw [Ecc.WitnessPoint.pointNonIdFormal_spec_eq, wpointNonId_output] at hAkS
  clear hCm hGd hAk
  simp only [Point.eval_eq, circuit_norm,
    Nat.add_zero] at hCmS hGdS hAkS
  -- ── stage B: the integrity checks ──
  simp only [synthWitness_output, synthWitness_nextRegionIndex, synthWitness_regionCount,
    Nat.add_assoc] at hCk hN
  simp only [synthChecks, loadPrivate, circuit_norm] at hCk
  have hM1 := hCk.1
  have hM2 := hCk.2.1
  have hVC := hCk.2.2.1
  have hIcvx := hCk.2.2.2.1
  have hIcvy := hCk.2.2.2.2.1
  have hDN := hCk.2.2.2.2.2.1
  have hInf := hCk.2.2.2.2.2.2.1
  have hSA := hCk.2.2.2.2.2.2.2.1
  have hIrkx := hCk.2.2.2.2.2.2.2.2.1
  have hIrky := hCk.2.2.2.2.2.2.2.2.2.1
  have hCI := hCk.2.2.2.2.2.2.2.2.2.2.1
  have hAI := hCk.2.2.2.2.2.2.2.2.2.2.2
  clear hCk
  try simp only [Nat.add_assoc] at hM2
  try simp only [Nat.add_assoc] at hVC
  try simp only [Nat.add_assoc] at hIcvx
  try simp only [Nat.add_assoc] at hIcvy
  try simp only [Nat.add_assoc] at hDN
  try simp only [Nat.add_assoc] at hInf
  try simp only [Nat.add_assoc] at hSA
  try simp only [Nat.add_assoc] at hIrkx
  try simp only [Nat.add_assoc] at hIrky
  try simp only [Nat.add_assoc] at hCI
  try simp only [Nat.add_assoc] at hAI
  subcircuit_rw at hM1
  subcircuit_rw at hM2
  subcircuit_rw at hVC
  subcircuit_rw at hDN
  subcircuit_rw at hSA
  subcircuit_rw at hCI
  subcircuit_rw at hAI
  have hM1S := hM1 (by rw [Sinsemilla.Merkle.CalculateRoot.circuit_envAssumptions_eq]; exact ⟨hTM1, hTL, hDist⟩)
    (by rw [Sinsemilla.Merkle.CalculateRoot.circuit_assumptions_eq]; trivial)
  rw [Sinsemilla.Merkle.CalculateRoot.circuit_spec_eq] at hM1S
  rw [layerInput_eval_eq] at hM1S
  have hM2S := hM2 (by rw [Sinsemilla.Merkle.CalculateRoot.circuit_envAssumptions_eq]; exact ⟨hTM2, hTL, hDist⟩)
    (by rw [Sinsemilla.Merkle.CalculateRoot.circuit_assumptions_eq]; trivial)
  rw [Sinsemilla.Merkle.CalculateRoot.circuit_spec_eq] at hM2S
  try rw [layerInput_eval_eq] at hM2S
  have hVCS := hVC (by exact ⟨hSh, hFw⟩) (by trivial)
  rw [ValueCommit.circuit_spec_eq, ValueCommit.circuit_extract_eq] at hVCS
  rw [vcInputs_eval_eq] at hVCS
  have hDNS := hDN (by exact hBf) (by
    show Point.Valid _
    simp only [circuit_norm, Point.eval_eq]
    exact hCmS)
  rw [DeriveNullifier.circuit_spec_eq] at hDNS
  rw [dnInputs_eval_eq] at hDNS
  have hSAS := hSA (by exact hFw) (by
    show Point.Valid _
    simp only [circuit_norm, Point.eval_eq]
    exact Or.inl hAkS)
  rw [SpendAuthority.circuit_spec_eq, SpendAuthority.circuit_extract_eq] at hSAS
  rw [saInputs_eval_eq] at hSAS
  have hCIS := hCI (by exact ⟨hT1, hFw, hTL, hDist⟩) (by trivial)
  rw [CommitIvk.Main.circuit_spec_eq, CommitIvk.Main.circuit_extract_eq] at hCIS
  rw [civkInputs_eval_eq] at hCIS
  have hAIS := hAI (by exact hMulE) (by
    show Point.OnCurve _
    simp only [circuit_norm, Point.eval_eq]
    exact hGdS)
  rw [AddressIntegrity.circuit_spec_eq, ai_output] at hAIS
  rw [aiInputs_eval_eq] at hAIS
  simp only [Point.eval_eq, circuit_norm, Nat.add_zero,
    Nat.add_assoc, Nat.reduceAdd] at hAIS
  clear hM1 hM2 hVC hDN hSA hCI hAI
  -- ── stage C: the note commitments and the final checks ──
  simp only [synthChecks_output, synthChecks_nextRegionIndex,
    synthChecks_regionCount, Nat.add_assoc, Nat.reduceAdd] at hN
  simp only [synthNotes, loadPrivate, circuit_norm] at hN
  have hNCo := hN.1
  have hEqR := hN.2.1
  have hGdN := hN.2.2.1
  have hPkN := hN.2.2.2.1
  have hNCn := hN.2.2.2.2.1
  have hIcmx := hN.2.2.2.2.2.1
  have hOrch := hN.2.2.2.2.2.2
  clear hN
  try simp only [Nat.add_assoc] at hGdN
  try simp only [Nat.add_assoc] at hPkN
  try simp only [Nat.add_assoc] at hNCn
  try simp only [circuit_norm, Nat.add_assoc, Nat.reduceAdd] at hIcmx
  try simp only [nextRegionIndex_constrainInstance, circuit_norm, Nat.add_assoc,
    Nat.reduceAdd] at hOrch
  rw [wpointNonId_output] at hNCn
  rw [wpointNonId_output] at hNCn
  try rw [wpointNonId_output] at hIcmx
  try rw [wpointNonId_output] at hIcmx
  simp only [] at hNCn hIcmx
  subcircuit_rw at hNCo
  subcircuit_rw at hGdN
  subcircuit_rw at hPkN
  subcircuit_rw at hNCn
  have hNCoS := hNCo (by exact ⟨hT1, hFw, hTL, hDist⟩)
    (by rw [NoteCommit.Main.circuit_assumptions_eq, ncInputs_eval_eq]
        refine ⟨?_, ?_⟩
        · show Point.OnCurve _
          simp only [circuit_norm, explicit_provable_type]; exact hGdS
        · show Point.OnCurve _
          simp only [circuit_norm, explicit_provable_type]; exact hAIS.1)
  rw [NoteCommit.Main.circuit_spec_eq, NoteCommit.Main.circuit_extract_eq] at hNCoS
  rw [ncInputs_eval_eq] at hNCoS
  have hGdNS := hGdN (by rw [Ecc.WitnessPoint.pointNonIdFormal_envAssumptions_eq]; trivial)
    (by rw [Ecc.WitnessPoint.pointNonIdFormal_assumptions_eq]; trivial)
  rw [Ecc.WitnessPoint.pointNonIdFormal_spec_eq, wpointNonId_output] at hGdNS
  have hPkNS := hPkN (by rw [Ecc.WitnessPoint.pointNonIdFormal_envAssumptions_eq]; trivial)
    (by rw [Ecc.WitnessPoint.pointNonIdFormal_assumptions_eq]; trivial)
  rw [Ecc.WitnessPoint.pointNonIdFormal_spec_eq, wpointNonId_output] at hPkNS
  have hNCnS := hNCn (by exact ⟨hT2, hFw, hTL, hDist⟩)
    (by rw [NoteCommit.Main.circuit_assumptions_eq, ncInputs_eval_eq]
        refine ⟨?_, ?_⟩
        · show Point.OnCurve _
          with_unfolding_all exact hGdNS
        · show Point.OnCurve _
          with_unfolding_all exact hPkNS)
  rw [NoteCommit.Main.circuit_spec_eq, NoteCommit.Main.circuit_extract_eq] at hNCnS
  rw [ncInputs_eval_eq] at hNCnS
  clear hNCo hGdN hPkN hNCn
  simp only [Point.eval_eq, circuit_norm,
    Nat.add_zero] at hGdNS hPkNS
  -- the "constrain equal" region: derived cm_old = witnessed cm_old
  try simp only [circuit_norm] at hEqR
  try simp only [circuit_norm] at hOrch
  -- ── assemble the statement ──
  simp only [Spec, SpecBase, extract, cellRead, circuit_norm,
    Nat.add_zero, Nat.add_assoc]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · exact hCmS
  · exact hGdS
  · exact hAkS
  · exact hAIS.1
  · exact hGdNS
  · exact hPkNS
  · -- `v_old < 2^64` (old NoteCommit's value decomposition)
    with_unfolding_all exact hNCoS.1
  · -- `v_new < 2^64` (new NoteCommit's value decomposition)
    with_unfolding_all exact hNCnS.1
  · -- value-commitment integrity
    obtain ⟨hm, hdisj⟩ := hVCS
    have hP : ({ x := env.inst cfg.primary ((CV_NET_X : ℕ) : ℤ),
                 y := env.inst cfg.primary ((CV_NET_Y : ℕ) : ℤ) } : Point Fp)
        = eval (⟨place, env⟩ : Placed Environment Fp)
            ((ValueCommit.circuit B.valueCommitV B.valueCommitR).output
              (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull,
               cfg.eccConfig.add)
              { rcv := input_var_rcv,
                magnitude := AssignedCell.of (i₀ + 264) 0 (cfg.advices 9),
                sign := AssignedCell.of (i₀ + 265) 0 (cfg.advices 9) }
              (i₀ + 266)) := by
      apply Point.ext_coords
      show (env.inst cfg.primary ((CV_NET_X : ℕ) : ℤ),
            env.inst cfg.primary ((CV_NET_Y : ℕ) : ℤ)) = _
      rw [← hIcvx, ← hIcvy]
      with_unfolding_all rfl
    refine ⟨by with_unfolding_all exact hm, ?_⟩
    rcases hdisj with ⟨hs, he⟩ | ⟨hs, he⟩
    · with_unfolding_all exact Or.inl ⟨by exact hs, by rw [hP]; exact he⟩
    · with_unfolding_all exact Or.inr ⟨by exact hs, by rw [hP]; exact he⟩
  · -- nullifier integrity
    with_unfolding_all exact hInf.symm.trans (by exact hDNS)
  · -- spend authority
    have hP : ({ x := env.inst cfg.primary ((RK_X : ℕ) : ℤ),
                 y := env.inst cfg.primary ((RK_Y : ℕ) : ℤ) } : Point Fp)
        = eval (⟨place, env⟩ : Placed Environment Fp)
            ((SpendAuthority.circuit B.spendAuthG).output
              (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
              { alpha := input_var_alpha,
                akP := { x := AssignedCell.of (i₀ + 4) 0 cfg.eccConfig.witnessPoint.x,
                         y := AssignedCell.of (i₀ + 4) 0 cfg.eccConfig.witnessPoint.y } }
              (i₀ + 280)) := by
      apply Point.ext_coords
      show (env.inst cfg.primary ((RK_X : ℕ) : ℤ),
            env.inst cfg.primary ((RK_Y : ℕ) : ℤ)) = _
      rw [← hIrkx, ← hIrky]
      with_unfolding_all rfl
    rw [hP, hSAS]
    with_unfolding_all rfl
  · -- diversified-address integrity
    with_unfolding_all exact ⟨_, by exact hCIS, by exact hAIS.2⟩
  · -- old note-commitment integrity
    refine Specs.Sinsemilla.SpecOrBreak.mono ?_
      (by with_unfolding_all exact hNCoS.2)
    intro bp hbp
    have hcmP : ({ x := env.advice cfg.eccConfig.witnessPoint.x ((place (i₀ + 2) : ℕ) : ℤ),
                   y := env.advice cfg.eccConfig.witnessPoint.y ((place (i₀ + 2) : ℕ) : ℤ) }
                : Point Fp)
        = eval (⟨place, env⟩ : Placed Environment Fp)
            ((NoteCommit.Main.circuit G B.noteCommitR B.noteQ
              B.noteQ_onCurve).output
              { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
                lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
                addConfig := cfg.eccConfig.add }
              { gdX := AssignedCell.of (i₀ + 3) 0 cfg.eccConfig.witnessPoint.x,
                gdY := AssignedCell.of (i₀ + 3) 0 cfg.eccConfig.witnessPoint.y,
                pkdX := AssignedCell.of (i₀ + 301) 0 cfg.eccConfig.witnessPoint.x,
                pkdY := AssignedCell.of (i₀ + 301) 0 cfg.eccConfig.witnessPoint.y,
                value := AssignedCell.of (i₀ + 6) 0 (cfg.advices 0),
                rho := AssignedCell.of (i₀ + 1) 0 (cfg.advices 0),
                psi := AssignedCell.of i₀ 0 (cfg.advices 0),
                rcm := input_var_rcmOld }
              (i₀ + 303)) := by
      apply Point.ext_coords
      simp only [Point.coords]
      rw [← hEqR.1, ← hEqR.2]
      simp only [circuit_norm, explicit_provable_type]
    rw [hcmP]
    exact hbp
  · -- new note-commitment integrity
    rw [← hInf]
    refine Specs.Sinsemilla.SpecOrBreak.mono ?_
      (by with_unfolding_all exact hNCnS.2)
    intro bp hbp
    rw [← hIcmx]
    with_unfolding_all exact congrArg Point.x hbp
  · -- Merkle path validity + the anchor check
    obtain ⟨hOv, hOn, hOm, hOs, hOr, hOa, hOes, hOeo, hGate⟩ := hOrch
    have hRoot := Sinsemilla.Merkle.MerkleRoot.trans G B.merkleQ hM1S.1 hM2S.1
    simp only [orchardGate, Gate.withSelector, circuit_norm, List.Forall] at hGate
    have h := hGate.2.1
    rw [hOv, hOr, hOa] at h
    refine ⟨_, by with_unfolding_all exact hRoot, ?_, by with_unfolding_all exact h⟩
    rcases hM1S.2 with hM1Strict | hM1Break
    · rcases hM2S.2 with hM2Strict | hM2Break
      · with_unfolding_all exact Or.inl (Sinsemilla.Merkle.MerkleRootStrict.trans G B.merkleQ hM1Strict hM2Strict)
      · exact Or.inr (Sinsemilla.Merkle.MerkleBreakAt.shift G B.merkleQ (l := 0) (k := 16) (k' := 16) hM2Break)
    · exact Or.inr (Sinsemilla.Merkle.MerkleBreakAt.mono G B.merkleQ (by omega) hM1Break)
  · -- `v_old − v_new = magnitude · sign`
    obtain ⟨hOv, hOn, hOm, hOs, hOr, hOa, hOes, hOeo, hGate⟩ := hOrch
    simp only [orchardGate, Gate.withSelector, circuit_norm, List.Forall] at hGate
    have h := hGate.1
    rw [hOv, hOn, hOm, hOs] at h
    linear_combination h
  · -- the enable-flag checks
    obtain ⟨hOv, hOn, hOm, hOs, hOr, hOa, hOes, hOeo, hGate⟩ := hOrch
    simp only [orchardGate, Gate.withSelector, circuit_norm, List.Forall] at hGate
    refine ⟨?_, ?_⟩
    · have h := hGate.2.2.1
      rw [hOv, hOes] at h
      linear_combination h
    · have h := hGate.2.2.2
      rw [hOn, hOeo] at h
      linear_combination h
  -- output ties: the four witnessed address points — the canonical `elaborated` unfold
  -- lands h_output destructured to exactly these advice-atom pairs
  · exact ⟨h_output.1.1.symm, h_output.1.2.symm⟩
  · exact ⟨h_output.2.1.1.symm, h_output.2.1.2.symm⟩
  · exact ⟨h_output.2.2.1.1.symm, h_output.2.2.1.2.symm⟩
  · exact ⟨h_output.2.2.2.1.symm, h_output.2.2.2.2.symm⟩

open Sinsemilla.Merkle.CalculateRoot (pathNode) in
/-- Honest-prover preconditions: well-formed witness points, 3-bit windows for the five
fixed-base scalars, a fully-defined Merkle path, defined Sinsemilla hashes for the three
commitment legs (with the honest commitment equations for the copies/instance rows),
and the `q_orchard` value checks at the honest values. -/
def ProverAssumptions (G : Generators) (B : Bases)
    (_ : WitnessData Fp) (wit : ActionData) (_ : ProverHint Fp) : Prop :=
  wit.cmOld.Valid ∧ wit.gdOld.OnCurve ∧ wit.akP.OnCurve ∧ wit.pkdOld.OnCurve ∧
  wit.gdNew.OnCurve ∧ wit.pkdNew.OnCurve ∧
  (∀ w : Fin 85, (wit.rcv.1[w.val]).val < 8) ∧
  (∀ w : Fin 85, (wit.alpha.1[w.val]).val < 8) ∧
  (∀ w : Fin 85, (wit.rivk.1[w.val]).val < 8) ∧
  (∀ w : Fin 85, (wit.rcmOld.1[w.val]).val < 8) ∧
  (∀ w : Fin 85, (wit.rcmNew.1[w.val]).val < 8) ∧
  wit.magnitude.val < 2 ^ 64 ∧ (wit.sign = 1 ∨ wit.sign = -1) ∧
  (show Fp from wit.vOld).val < 2 ^ 64 ∧ (show Fp from wit.vNew).val < 2 ^ 64 ∧
  -- the Merkle path is fully defined, split at the chip boundary
  (∃ mid, pathNode G B.merkleQ 0 wit.merklePath wit.cmOld.x 16 = some mid ∧
    ∃ root, pathNode G B.merkleQ 16 (fun j => wit.merklePath (16 + j)) mid 16
      = some root ∧
    -- NOT `anchor = root`: an honest dummy spend has `v_old = 0` with an arbitrary
    -- path, so only the product form holds (§4.17.4 "either v_old = 0 or …").
    wit.vOld * (root - wit.anchor) = 0) ∧
  -- the three Sinsemilla legs are defined, with the honest commitment equations
  (∃ Bi, hashToPoint G.S B.ivkQ
      (commitIvkChunks wit.akP.x.val wit.nk.val) = some Bi ∧
    wit.pkdOld = ((Bi + wit.rivk.2 • B.commitIvkR).x).val • wit.gdOld) ∧
  (∃ Bo, hashToPoint G.S B.noteQ
      (NoteCommit.noteScalars wit.gdOld wit.pkdOld wit.vOld
        wit.rhoOld wit.psiOld).chunks = some Bo ∧
    wit.cmOld = Bo + wit.rcmOld.2 • B.noteCommitR) ∧
  (∃ Bn, hashToPoint G.S B.noteQ
      (NoteCommit.noteScalars wit.gdNew wit.pkdNew wit.vNew
        wit.nfOld wit.psiNew).chunks = some Bn ∧
    wit.cmx = (Bn + wit.rcmNew.2 • B.noteCommitR).x) ∧
  -- the public-input rows are the honestly computed values
  ((wit.sign = 1 →
      (⟨wit.cvX, wit.cvY⟩ : Point Fp)
        = (wit.magnitude.val : Fq) • B.valueCommitV
          + wit.rcv.2 • B.valueCommitR) ∧
   (wit.sign = -1 →
      (⟨wit.cvX, wit.cvY⟩ : Point Fp)
        = -(wit.magnitude.val : Fq) • B.valueCommitV
          + wit.rcv.2 • B.valueCommitR)) ∧
  wit.nfOld = (wit.cmOld +
    ((Poseidon.Hash.ConstantLength.value #v[wit.nk, wit.rhoOld]
      + wit.psiOld).val : Fq) • B.nullifierK).x ∧
  (⟨wit.rkX, wit.rkY⟩ : Point Fp)
    = wit.alpha.2 • B.spendAuthG + wit.akP ∧
  -- the remaining `q_orchard` value checks at the honest values
  wit.vOld - wit.vNew = wit.magnitude * wit.sign ∧
  wit.vOld * (1 - wit.enableSpend) = 0 ∧
  wit.vNew * (1 - wit.enableOutput) = 0

/-! ## Completeness -/

private theorem buildWitness (G : Generators) (W : Witnesses Fp) (cfg : Config)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : Environment Fp)
    (hT : Halo2.Constraints place env
      ((Sinsemilla.load G cfg.sinsemilla1.generatorTable).operations i₀) i₀)
    (h1 : Constraints place env
      ((Ecc.WitnessPoint.pointFormal.call
        cfg.eccConfig.witnessPoint W.cmOld).operations (i₀ + 2)) (i₀ + 2))
    (h2 : Constraints place env
      ((Ecc.WitnessPoint.pointNonIdFormal.call
        cfg.eccConfig.witnessPoint W.gdOld).operations (i₀ + 3)) (i₀ + 3))
    (h3 : Constraints place env
      ((Ecc.WitnessPoint.pointNonIdFormal.call
        cfg.eccConfig.witnessPoint W.akP).operations (i₀ + 4)) (i₀ + 4)) :
    Constraints place env ((synthWitness G W cfg).operations i₀) i₀ := by
  simp only [Sinsemilla.load, circuit_norm] at hT
  simp only [synthWitness, loadPrivate, Sinsemilla.load, circuit_norm,
    Nat.add_assoc, Nat.reduceAdd]
  exact ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.1, hT.2.2.2.2.1, hT.2.2.2.2.2,
    h1, h2, h3⟩

theorem completeness (G : Generators) (B : Bases) (cfg : Config) :
    FormalCircuit.Completeness (Witness := fun _ => ActionData)
      (main G B cfg) (extract cfg) (EnvAssumptions G cfg) (fun _ => True)
      (ProverAssumptions G B) (fun _ _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨hTE, hT1, hT2, hTM1, hTM2, hFw, hSh, hBf, hMulE, hTL, hDist⟩ := _hE
  obtain ⟨hVcm, hVgd, hVak, hVpk, hVgdn, hVpkn, hWrcv, hWal, hWri, hWro, hWrn,
    hMag, hSign, hV64o, hV64n, ⟨mid, hMid, root, hRootP, hVanch⟩,
    ⟨Bi, hBi, hPkd⟩, ⟨Bo, hBo, hCmo⟩, ⟨Bn, hBn, hCmx⟩,
    ⟨hCv1, hCv2⟩, hNf, hRk, hVms, hVes, hVeo⟩ := hPA
  -- `circuit_proof_start` destructures the formal input into its `input_var_*` fields;
  -- re-bind the whole record as `input_var` (folding the copies the hypotheses carry)
  -- so the `extract cfg input_var i₀ …` spellings below resolve. `extract` ignores this
  -- argument, so the reconstruction is definitionally the framework's input var.
  set input_var : Var PrivateInputs Fp :=
    { psiOld := input_var_psiOld, rhoOld := input_var_rhoOld, nk := input_var_nk,
      vOld := input_var_vOld, vNew := input_var_vNew, psiNew := input_var_psiNew,
      magnitude := input_var_magnitude, sign := input_var_sign, cmOld := input_var_cmOld,
      gdOld := input_var_gdOld, akP := input_var_akP, pkDOld := input_var_pkDOld,
      gdNew := input_var_gdNew, pkdNew := input_var_pkdNew, rcv := input_var_rcv,
      alpha := input_var_alpha, rivk := input_var_rivk, rcmOld := input_var_rcmOld,
      rcmNew := input_var_rcmNew, merkleSib := input_var_merkleSib,
      merkleSwap := input_var_merkleSwap } with hInputVarDef
  simp only [CircuitPreIronwood.synthesize, synthesizeBase,
    circuit_norm] at hwit ⊢
  have hWw := hwit.1
  have hWc := hwit.2.1
  have hWn := hwit.2.2
  clear hwit
  -- ── stage A witnesses: the shared cells are the programs' honest values ──
  simp only [synthWitness, loadPrivate, Sinsemilla.load, circuit_norm] at hWw
  obtain ⟨-, -, -, -, -, -, hwPsi, hwRho, hWcm, hWgd, hWak, hwNk, hwVo, hwVn⟩ := hWw
  simp only [Nat.add_assoc, Nat.reduceAdd] at hWgd hWak
  refine ⟨buildWitness G ⟨input_var_psiOld, input_var_rhoOld, input_var_nk, input_var_vOld,
      input_var_vNew, input_var_psiNew, input_var_magnitude, input_var_sign,
      input_var_cmOld, input_var_gdOld, input_var_akP, input_var_pkDOld,
      input_var_gdNew, input_var_pkdNew, input_var_rcv, input_var_alpha,
      input_var_rivk, input_var_rcmOld, input_var_rcmNew,
      input_var_merkleSib, input_var_merkleSwap⟩ cfg i₀ place _
    (generatorTableExact_constraints G _ _ hTE place i₀) ?_ ?_ ?_, ?_⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      Ecc.WitnessPoint.pointFormal
      cfg.eccConfig.witnessPoint (i₀ + 2) place env _ hWcm
      ⟨(by rw [Ecc.WitnessPoint.pointFormal_envAssumptions_eq]; trivial),
       (by rw [Ecc.WitnessPoint.pointFormal_assumptions_eq]; trivial),
       (by rw [Ecc.WitnessPoint.pointFormal_proverAssumptions_eq]
           show Point.Valid _
           rw [wpoint_eval_eq_cells _ _ _ _ _ hWcm]
           exact hVcm)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      Ecc.WitnessPoint.pointNonIdFormal
      cfg.eccConfig.witnessPoint (i₀ + 3) place env _ hWgd
      ⟨(by rw [Ecc.WitnessPoint.pointNonIdFormal_envAssumptions_eq]; trivial),
       (by rw [Ecc.WitnessPoint.pointNonIdFormal_assumptions_eq]; trivial),
       (by rw [Ecc.WitnessPoint.pointNonIdFormal_proverAssumptions_eq]
           show Point.OnCurve _
           rw [wpointNonId_eval_eq_cells _ _ _ _ _ hWgd]
           exact hVgd)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      Ecc.WitnessPoint.pointNonIdFormal
      cfg.eccConfig.witnessPoint (i₀ + 4) place env _ hWak
      ⟨(by rw [Ecc.WitnessPoint.pointNonIdFormal_envAssumptions_eq]; trivial),
       (by rw [Ecc.WitnessPoint.pointNonIdFormal_assumptions_eq]; trivial),
       (by rw [Ecc.WitnessPoint.pointNonIdFormal_proverAssumptions_eq]
           show Point.OnCurve _
           rw [wpointNonId_eval_eq_cells _ _ _ _ _ hWak]
           exact hVak)⟩
  · -- ── stages B and C ──
    simp only [synthWitness_output, synthWitness_nextRegionIndex,
      synthWitness_regionCount, Nat.add_assoc] at hWc hWn
    simp only [synthChecks, loadPrivate, circuit_norm] at hWc
    obtain ⟨hWm1, hWm2, hwMag, hwSign, hWvc, hWdn, hWsa, hWci, hWai⟩ := hWc
    -- offsets are already folded (`circuit_norm` region-count bridges)
    simp only [Nat.add_assoc, Nat.reduceAdd] at hWm2 hWvc hWdn hWsa hWci hWai
    -- ── the fold contracts: honest mid/root landings ──
    have hM1der := Halo2.SubcircuitRw.layouter_completeness_derived
      (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
        0 16 (by norm_num) input_var_merkleSib input_var_merkleSwap)
      (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig) (i₀ + 8) place env _ hWm1
      (by rw [Sinsemilla.Merkle.CalculateRoot.circuit_envAssumptions_eq]; exact ⟨hTM1, hTL, hDist⟩)
      (by rw [Sinsemilla.Merkle.CalculateRoot.circuit_assumptions_eq]; trivial)
      (by show ((Sinsemilla.Merkle.CalculateRoot.pathNode G B.merkleQ 0 _ _ 16).isSome)
          rw [Sinsemilla.Merkle.CalculateRoot.pathNode_congr G B.merkleQ 0 _ 16
            (w' := fun j => (extract cfg input_var i₀
              (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).merklePath j)
            (h := by
              intro j hj
              simp only [extract, cellRead, if_pos hj]
              with_unfolding_all rfl)]
          rw [show ((Sinsemilla.Merkle.CalculateRoot.pathNode G B.merkleQ 0
              (fun j => (extract cfg input_var i₀
                (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).merklePath j) _ 16))
            = (Sinsemilla.Merkle.CalculateRoot.pathNode G B.merkleQ 0
              (extract cfg input_var i₀
                (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).merklePath
              (extract cfg input_var i₀
                (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).cmOld.x 16)
            from by with_unfolding_all rfl]
          rw [hMid]
          rfl)
    -- fold 1 lands on `mid`
    have hM1mid : (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
        ((Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
          0 16 (by norm_num) input_var_merkleSib input_var_merkleSwap).output
          (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig)
          { node := AssignedCell.of (i₀ + 2) 0 cfg.eccConfig.witnessPoint.x }
          (i₀ + 8)) : Fp) = mid := by
      refine hM1der.2 mid ?_
      rw [show ((Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
          0 16 (by norm_num) input_var_merkleSib input_var_merkleSwap).extract
          (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig) _ (i₀ + 8)
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp))
        = fun j => ((eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (AssignedCell.of (i₀ + 8 + 8 * j) 0 cfg.merkle1.condSwap.b
              : Var field Fp) : Fp),
          (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (AssignedCell.of (i₀ + 8 + 8 * j) 0 cfg.merkle1.condSwap.swap
              : Var field Fp) : Fp)) from by
        funext j
        with_unfolding_all rfl]
      rw [Sinsemilla.Merkle.CalculateRoot.pathNode_congr G B.merkleQ 0 _ 16
        (w' := fun j => (extract cfg input_var i₀
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).merklePath j)
        (h := by
          intro j hj
          simp only [extract, cellRead, if_pos hj]
          try simp only [circuit_norm, explicit_provable_type])]
      rw [show ((Sinsemilla.Merkle.CalculateRoot.pathNode G B.merkleQ 0
          (fun j => (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).merklePath j) _ 16))
        = (Sinsemilla.Merkle.CalculateRoot.pathNode G B.merkleQ 0
          (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).merklePath
          (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).cmOld.x 16)
        from by with_unfolding_all rfl]
      exact hMid
    have hM2der := Halo2.SubcircuitRw.layouter_completeness_derived
      (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
        16 16 (by norm_num) (fun i => input_var_merkleSib (16 + i))
        (fun i => input_var_merkleSwap (16 + i)))
      (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig) (i₀ + 136) place env _
      hWm2
      (by rw [Sinsemilla.Merkle.CalculateRoot.circuit_envAssumptions_eq]; exact ⟨hTM2, hTL, hDist⟩)
      (by rw [Sinsemilla.Merkle.CalculateRoot.circuit_assumptions_eq]; trivial)
      (by show ((Sinsemilla.Merkle.CalculateRoot.pathNode G B.merkleQ 16
            _ _ 16).isSome)
          rw [Sinsemilla.Merkle.CalculateRoot.pathNode_congr₂ G B.merkleQ 16 16
            (w' := fun j => (extract cfg input_var i₀
              (⟨place, env.toEnvironment⟩
                : Placed Environment Fp)).merklePath (16 + j))
            (node' := mid)
            (hw := by
              intro j hj
              simp only [extract, cellRead,
                show ¬(16 + j < 16) from by omega, if_false,
                show 16 + j - 16 = j from by omega]
              try with_unfolding_all rfl)
            (hn := by with_unfolding_all exact hM1mid)]
          rw [hRootP]
          rfl)
    -- fold 2 lands on `root`
    have hM2root : (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
        ((Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
          16 16 (by norm_num) (fun i => input_var_merkleSib (16 + i))
          (fun i => input_var_merkleSwap (16 + i))).output
          (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig)
          { node := (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ
              B.merkleQ_onCurve 0 16 (by norm_num) input_var_merkleSib input_var_merkleSwap).output
              (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig)
              { node := AssignedCell.of (i₀ + 2) 0 cfg.eccConfig.witnessPoint.x }
              (i₀ + 8) }
          (i₀ + 136)) : Fp) = root := by
      refine hM2der.2 root ?_
      rw [show ((Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
          16 16 (by norm_num) (fun i => input_var_merkleSib (16 + i))
          (fun i => input_var_merkleSwap (16 + i))).extract
          (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig) _ (i₀ + 136)
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp))
        = fun j => ((eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (AssignedCell.of (i₀ + 136 + 8 * j) 0 cfg.merkle2.condSwap.b
              : Var field Fp) : Fp),
          (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (AssignedCell.of (i₀ + 136 + 8 * j) 0 cfg.merkle2.condSwap.swap
              : Var field Fp) : Fp)) from by
        funext j
        with_unfolding_all rfl]
      rw [Sinsemilla.Merkle.CalculateRoot.pathNode_congr₂ G B.merkleQ 16 16
        (w' := fun j => (extract cfg input_var i₀
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).merklePath (16 + j))
        (node' := mid)
        (hw := by
          intro j hj
          simp only [extract, cellRead,
            show ¬(16 + j < 16) from by omega, if_false,
            show 16 + j - 16 = j from by omega]
          try with_unfolding_all rfl)
        (hn := by with_unfolding_all exact hM1mid)]
      exact hRootP
    -- ── the remaining child contracts (for the instance rows and the gate) ──
    have hVCder := (Halo2.SubcircuitRw.layouter_completeness_derived
      (ValueCommit.circuit B.valueCommitV B.valueCommitR)
      (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
      (i₀ + 266) place env _ hWvc (by exact ⟨hSh, hFw⟩) (by trivial)
      (by rw [ValueCommit.circuit_proverAssumptions_eq, vcInputs_eval_eq_prover]
          refine ⟨?_, ?_⟩
          · with_unfolding_all exact hMag
          · with_unfolding_all exact hSign)).1
    have hDNder := (Halo2.SubcircuitRw.layouter_completeness_derived
      (DeriveNullifier.circuit B.nullifierK)
      (cfg.poseidonConfig, cfg.addChipConfig, cfg.eccConfig.mulFixedBaseField,
       cfg.eccConfig.add) (i₀ + 271) place env _ hWdn (by exact hBf)
      (by rw [DeriveNullifier.circuit_assumptions_eq, dnInputs_eval_eq]
          show Point.Valid _
          simp only [Point.eval_eq]
          exact hVcm)
      (by trivial)).1
    have hSAder := (Halo2.SubcircuitRw.layouter_completeness_derived
      (SpendAuthority.circuit B.spendAuthG)
      (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add) (i₀ + 280) place env _ hWsa
      (by exact hFw)
      (by rw [SpendAuthority.circuit_assumptions_eq, saInputs_eval_eq]
          show Point.Valid _
          simp only [Point.eval_eq]
          exact Or.inl hVak)
      (by trivial)).1
    have hCIder := (Halo2.SubcircuitRw.layouter_completeness_derived
      (CommitIvk.Main.circuit G B.commitIvkR B.ivkQ B.ivkQ_onCurve)
      { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
        lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
        addConfig := cfg.eccConfig.add } (i₀ + 283) place env _ hWci
      (by exact ⟨hT1, hFw, hTL, hDist⟩) (by trivial)
      (by rw [CommitIvk.Main.circuit_proverAssumptions_eq]
          rw [civkInputs_eval_eq_prover]
          with_unfolding_all exact ⟨Bi, by exact hBi⟩)).1
    -- the ivk output cell carries the honest commitment value
    have hIvkVal : (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
        ((CommitIvk.Main.circuit G B.commitIvkR B.ivkQ
          B.ivkQ_onCurve).output
          { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
            lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add }
          { ak := AssignedCell.of (i₀ + 4) 0 cfg.eccConfig.witnessPoint.x,
            nk := AssignedCell.of (i₀ + 5) 0 (cfg.advices 0),
            rivk := input_var_rivk }
          (i₀ + 283)) : Fp)
        = (Bi + (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rivk.2
              • B.commitIvkR).x := by
      rw [CommitIvk.Main.circuit_spec_eq, CommitIvk.Main.circuit_extract_eq] at hCIder
      rw [civkInputs_eval_eq] at hCIder
      simp only [circuit_norm,
        Nat.add_zero] at hCIder
      rw [Specs.Sinsemilla.hashToPointB_inl_of_some
        (show hashToPoint G.S B.ivkQ _ = some Bi from by
          with_unfolding_all exact hBi)] at hCIder
      simp only [circuit_norm, explicit_provable_type]; exact hCIder
    -- ── stage C witnesses and contracts ──
    simp only [synthChecks_output, synthChecks_nextRegionIndex,
      synthChecks_regionCount, Nat.add_assoc, Nat.reduceAdd] at hWn
    simp only [synthNotes, loadPrivate, circuit_norm] at hWn
    obtain ⟨hWnco, hWgdn, hWpkn, hwPsiN, hWncn, hWorch⟩ := hWn
    simp only [Nat.add_assoc, Nat.reduceAdd] at hWgdn hWpkn hWncn hWorch
    have hNCoDer := (Halo2.SubcircuitRw.layouter_completeness_derived
      (NoteCommit.Main.circuit G B.noteCommitR B.noteQ
        B.noteQ_onCurve)
      { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
        lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
        addConfig := cfg.eccConfig.add } (i₀ + 303) place env _ hWnco
      (by exact ⟨hT1, hFw, hTL, hDist⟩)
      (by rw [NoteCommit.Main.circuit_assumptions_eq, ncInputs_eval_eq]
          refine ⟨?_, ?_⟩
          · show Point.OnCurve _
            exact hVgd
          · show Point.OnCurve _
            exact hVpk)
      (by rw [NoteCommit.Main.circuit_proverAssumptions_eq]
          rw [ncInputs_eval_eq_prover]
          refine ⟨?_, ?_, ?_, ?_⟩
          · with_unfolding_all exact hVgd
          · with_unfolding_all exact hVpk
          · with_unfolding_all exact hV64o
          · refine ⟨Bo, ?_⟩
            with_unfolding_all exact hBo)).1
    -- the nullifier output cell carries the honest `nf_old` (= the NF_OLD row)
    have hDNval : (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
        ((DeriveNullifier.circuit B.nullifierK).output
          (cfg.poseidonConfig, cfg.addChipConfig, cfg.eccConfig.mulFixedBaseField,
           cfg.eccConfig.add)
          { nk := AssignedCell.of (i₀ + 5) 0 (cfg.advices 0),
            rho := AssignedCell.of (i₀ + 1) 0 (cfg.advices 0),
            psi := AssignedCell.of i₀ 0 (cfg.advices 0),
            cm := { x := AssignedCell.of (i₀ + 2) 0 cfg.eccConfig.witnessPoint.x,
                    y := AssignedCell.of (i₀ + 2) 0 cfg.eccConfig.witnessPoint.y } }
          (i₀ + 271)) : Fp)
        = (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).nfOld := by
      rw [DeriveNullifier.circuit_spec_eq, dnInputs_eval_eq] at hDNder
      rw [hNf]
      with_unfolding_all exact hDNder
    have hNCnDer := (Halo2.SubcircuitRw.layouter_completeness_derived
      (NoteCommit.Main.circuit G B.noteCommitR B.noteQ
        B.noteQ_onCurve)
      { gates := cfg.noteCommitNew, hashConfig := cfg.sinsemilla2,
        lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
        addConfig := cfg.eccConfig.add } (i₀ + 350) place env _ hWncn
      (by exact ⟨hT2, hFw, hTL, hDist⟩)
      (by rw [NoteCommit.Main.circuit_assumptions_eq, ncInputs_eval_eq]
          refine ⟨?_, ?_⟩
          · show Point.OnCurve _
            exact hVgdn
          · show Point.OnCurve _
            exact hVpkn)
      (by rw [NoteCommit.Main.circuit_proverAssumptions_eq]
          rw [ncInputs_eval_eq_prover]
          refine ⟨?_, ?_, ?_, ?_⟩
          · with_unfolding_all exact hVgdn
          · with_unfolding_all exact hVpkn
          · with_unfolding_all exact hV64n
          · refine ⟨Bn, ?_⟩
            rw [show (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
                ((DeriveNullifier.circuit B.nullifierK).output
                  (cfg.poseidonConfig, cfg.addChipConfig,
                   cfg.eccConfig.mulFixedBaseField, cfg.eccConfig.add)
                  { nk := AssignedCell.of (i₀ + 5) 0 (cfg.advices 0),
                    rho := AssignedCell.of (i₀ + 1) 0 (cfg.advices 0),
                    psi := AssignedCell.of i₀ 0 (cfg.advices 0),
                    cm := { x := AssignedCell.of (i₀ + 2) 0
                              cfg.eccConfig.witnessPoint.x,
                            y := AssignedCell.of (i₀ + 2) 0
                              cfg.eccConfig.witnessPoint.y } }
                  (i₀ + 271)) : Fp)
              = (extract cfg input_var i₀
                  (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).nfOld
              from hDNval]
            with_unfolding_all exact hBn)).1
    -- the honest instance-row values of the child outputs
    have hCVval : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
        ((ValueCommit.circuit B.valueCommitV B.valueCommitR).output
          (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull,
           cfg.eccConfig.add)
          { rcv := input_var_rcv,
            magnitude := AssignedCell.of (i₀ + 264) 0 (cfg.advices 9),
            sign := AssignedCell.of (i₀ + 265) 0 (cfg.advices 9) }
          (i₀ + 266)) : Point Fp)
        = ⟨(extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).cvX,
           (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).cvY⟩ := by
      rw [ValueCommit.circuit_spec_eq, ValueCommit.circuit_extract_eq, vcInputs_eval_eq] at hVCder
      obtain ⟨hm, hdisj⟩ := hVCder
      rcases hdisj with ⟨hs, he⟩ | ⟨hs, he⟩
      · rw [he]
        with_unfolding_all exact (hCv1 (by exact hs)).symm
      · rw [he]
        with_unfolding_all exact (hCv2 (by exact hs)).symm
    have hSAval : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
        ((SpendAuthority.circuit B.spendAuthG).output
          (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
          { alpha := input_var_alpha,
            akP := { x := AssignedCell.of (i₀ + 4) 0 cfg.eccConfig.witnessPoint.x,
                     y := AssignedCell.of (i₀ + 4) 0 cfg.eccConfig.witnessPoint.y } }
          (i₀ + 280)) : Point Fp)
        = ⟨(extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rkX,
           (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rkY⟩ := by
      rw [SpendAuthority.circuit_spec_eq, SpendAuthority.circuit_extract_eq, saInputs_eval_eq] at hSAder
      rw [hSAder]
      rw [show ((⟨(extract cfg input_var i₀
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rkX,
          (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rkY⟩ : Point Fp))
        = (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).alpha.2
              • B.spendAuthG
          + (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).akP from hRk]
      with_unfolding_all rfl
    have hNCoval : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
        ((NoteCommit.Main.circuit G B.noteCommitR B.noteQ
          B.noteQ_onCurve).output
          { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
            lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add }
          { gdX := AssignedCell.of (i₀ + 3) 0 cfg.eccConfig.witnessPoint.x,
            gdY := AssignedCell.of (i₀ + 3) 0 cfg.eccConfig.witnessPoint.y,
            pkdX := AssignedCell.of (i₀ + 301) 0 cfg.eccConfig.witnessPoint.x,
            pkdY := AssignedCell.of (i₀ + 301) 0 cfg.eccConfig.witnessPoint.y,
            value := AssignedCell.of (i₀ + 6) 0 (cfg.advices 0),
            rho := AssignedCell.of (i₀ + 1) 0 (cfg.advices 0),
            psi := AssignedCell.of i₀ 0 (cfg.advices 0),
            rcm := input_var_rcmOld }
          (i₀ + 303)) : Point Fp)
        = (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).cmOld := by
      rw [NoteCommit.Main.circuit_spec_eq, NoteCommit.Main.circuit_extract_eq] at hNCoDer
      rw [ncInputs_eval_eq] at hNCoDer
      rw [Specs.Sinsemilla.hashToPointB_inl_of_some
        (show hashToPoint G.S B.noteQ _ = some Bo from by
          exact hBo)] at hNCoDer
      rw [hCmo]
      exact hNCoDer.2
    have hNCnval : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
        ((NoteCommit.Main.circuit G B.noteCommitR B.noteQ
          B.noteQ_onCurve).output
          { gates := cfg.noteCommitNew, hashConfig := cfg.sinsemilla2,
            lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add }
          { gdX := AssignedCell.of (i₀ + 347) 0 cfg.eccConfig.witnessPoint.x,
            gdY := AssignedCell.of (i₀ + 347) 0 cfg.eccConfig.witnessPoint.y,
            pkdX := AssignedCell.of (i₀ + 348) 0 cfg.eccConfig.witnessPoint.x,
            pkdY := AssignedCell.of (i₀ + 348) 0 cfg.eccConfig.witnessPoint.y,
            value := AssignedCell.of (i₀ + 7) 0 (cfg.advices 0),
            rho := (DeriveNullifier.circuit B.nullifierK).output
              (cfg.poseidonConfig, cfg.addChipConfig,
               cfg.eccConfig.mulFixedBaseField, cfg.eccConfig.add)
              { nk := AssignedCell.of (i₀ + 5) 0 (cfg.advices 0),
                rho := AssignedCell.of (i₀ + 1) 0 (cfg.advices 0),
                psi := AssignedCell.of i₀ 0 (cfg.advices 0),
                cm := { x := AssignedCell.of (i₀ + 2) 0 cfg.eccConfig.witnessPoint.x,
                        y := AssignedCell.of (i₀ + 2) 0
                          cfg.eccConfig.witnessPoint.y } }
              (i₀ + 271),
            psi := AssignedCell.of (i₀ + 349) 0 (cfg.advices 0),
            rcm := input_var_rcmNew }
          (i₀ + 350)) : Point Fp)
        = Bn + (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rcmNew.2
              • B.noteCommitR := by
      rw [NoteCommit.Main.circuit_spec_eq, NoteCommit.Main.circuit_extract_eq] at hNCnDer
      rw [ncInputs_eval_eq] at hNCnDer
      rw [show ((eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
          ((DeriveNullifier.circuit B.nullifierK).output
            (cfg.poseidonConfig, cfg.addChipConfig,
             cfg.eccConfig.mulFixedBaseField, cfg.eccConfig.add)
            { nk := AssignedCell.of (i₀ + 5) 0 (cfg.advices 0),
              rho := AssignedCell.of (i₀ + 1) 0 (cfg.advices 0),
              psi := AssignedCell.of i₀ 0 (cfg.advices 0),
              cm := { x := AssignedCell.of (i₀ + 2) 0 cfg.eccConfig.witnessPoint.x,
                      y := AssignedCell.of (i₀ + 2) 0
                        cfg.eccConfig.witnessPoint.y } }
            (i₀ + 271) : Var field Fp) : Fp))
          = (extract cfg input_var i₀
              (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).nfOld
          from by with_unfolding_all exact hDNval] at hNCnDer
      rw [Specs.Sinsemilla.hashToPointB_inl_of_some
        (show hashToPoint G.S B.noteQ _ = some Bn from by
          exact hBn)] at hNCnDer
      exact hNCnDer.2
    -- ── assemble the stage-B and stage-C constraints ──
    simp only [synthWitness_output, synthWitness_nextRegionIndex,
      synthWitness_regionCount, synthChecks_output, synthChecks_nextRegionIndex,
      synthChecks_regionCount, Nat.add_assoc, Nat.reduceAdd]
    refine ⟨?_, ?_⟩
    · simp only [synthChecks, loadPrivate, circuit_norm, Nat.add_assoc, Nat.reduceAdd]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          _ _ (i₀ + 8) place env _ hWm1
          ⟨(by rw [Sinsemilla.Merkle.CalculateRoot.circuit_envAssumptions_eq]; exact ⟨hTM1, hTL, hDist⟩),
           (by rw [Sinsemilla.Merkle.CalculateRoot.circuit_assumptions_eq]; trivial),
           (by show ((Sinsemilla.Merkle.CalculateRoot.pathNode G B.merkleQ 0
                 _ _ 16).isSome)
               rw [Sinsemilla.Merkle.CalculateRoot.pathNode_congr G B.merkleQ 0 _ 16
                 (w' := fun j => (extract cfg input_var i₀
                   (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).merklePath j)
                 (h := by
                   intro j hj
                   simp only [extract, cellRead, if_pos hj]
                   try with_unfolding_all rfl)]
               rw [show ((Sinsemilla.Merkle.CalculateRoot.pathNode G B.merkleQ 0
                   (fun j => (extract cfg input_var i₀
                     (⟨place, env.toEnvironment⟩
                       : Placed Environment Fp)).merklePath j) _ 16))
                 = (Sinsemilla.Merkle.CalculateRoot.pathNode G B.merkleQ 0
                   (extract cfg input_var i₀
                     (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).merklePath
                   (extract cfg input_var i₀
                     (⟨place, env.toEnvironment⟩
                       : Placed Environment Fp)).cmOld.x 16)
                 from by with_unfolding_all rfl]
               rw [hMid]
               rfl)⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          _ _ (i₀ + 136) place env _ hWm2
          ⟨(by rw [Sinsemilla.Merkle.CalculateRoot.circuit_envAssumptions_eq]; exact ⟨hTM2, hTL, hDist⟩),
           (by rw [Sinsemilla.Merkle.CalculateRoot.circuit_assumptions_eq]; trivial),
           (by show ((Sinsemilla.Merkle.CalculateRoot.pathNode G B.merkleQ 16
                 _ _ 16).isSome)
               rw [Sinsemilla.Merkle.CalculateRoot.pathNode_congr₂ G B.merkleQ 16 16
                 (w' := fun j => (extract cfg input_var i₀
                   (⟨place, env.toEnvironment⟩
                     : Placed Environment Fp)).merklePath (16 + j))
                 (node' := mid)
                 (hw := by
                   intro j hj
                   simp only [extract, cellRead,
                     show ¬(16 + j < 16) from by omega, if_false,
                     show 16 + j - 16 = j from by omega]
                   try with_unfolding_all rfl)
                 (hn := by with_unfolding_all exact hM1mid)]
               rw [hRootP]
               rfl)⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (ValueCommit.circuit B.valueCommitV B.valueCommitR)
          (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull,
           cfg.eccConfig.add) (i₀ + 266) place env _ hWvc
          ⟨(by exact ⟨hSh, hFw⟩), (by trivial),
           (by rw [ValueCommit.circuit_proverAssumptions_eq, vcInputs_eval_eq_prover]
               refine ⟨?_, ?_⟩
               · with_unfolding_all exact hMag
               · with_unfolding_all exact hSign)⟩
      · with_unfolding_all exact congrArg Point.x hCVval
      · with_unfolding_all exact congrArg Point.y hCVval
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (DeriveNullifier.circuit B.nullifierK)
          (cfg.poseidonConfig, cfg.addChipConfig, cfg.eccConfig.mulFixedBaseField,
           cfg.eccConfig.add) (i₀ + 271) place env _ hWdn
          ⟨(by exact hBf),
           (by rw [DeriveNullifier.circuit_assumptions_eq, dnInputs_eval_eq]
               show Point.Valid _
               simp only [Point.eval_eq]
               exact hVcm),
           (by trivial)⟩
      · with_unfolding_all exact hDNval
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (SpendAuthority.circuit B.spendAuthG)
          (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add) (i₀ + 280) place env _ hWsa
          ⟨(by exact hFw),
           (by rw [SpendAuthority.circuit_assumptions_eq, saInputs_eval_eq]
               show Point.Valid _
               simp only [Point.eval_eq]
               exact Or.inl hVak),
           (by trivial)⟩
      · with_unfolding_all exact congrArg Point.x hSAval
      · with_unfolding_all exact congrArg Point.y hSAval
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (CommitIvk.Main.circuit G B.commitIvkR B.ivkQ
            B.ivkQ_onCurve)
          { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
            lookupConfig := cfg.lookupConfig,
            mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add } (i₀ + 283) place env _ hWci
          ⟨(by exact ⟨hT1, hFw, hTL, hDist⟩), (by trivial),
           (by rw [CommitIvk.Main.circuit_proverAssumptions_eq]
               rw [civkInputs_eval_eq_prover]
               with_unfolding_all exact ⟨Bi, by exact hBi⟩)⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (AddressIntegrity.circuit)
          (cfg.eccConfig.mul, cfg.eccConfig.witnessPoint) (i₀ + 297) place env _
          hWai
          ⟨(by exact hMulE),
           (by rw [AddressIntegrity.circuit_assumptions_eq, aiInputs_eval_eq]
               show Point.OnCurve _
               simp only [Point.eval_eq]
               exact hVgd),
           (by rw [AddressIntegrity.circuit_proverAssumptions_eq, aiInputs_eval_eq_prover]
               -- the honest `pk_d_old` hint equals the cells the AddressIntegrity witness
               -- point assigns (region `i₀+301`), bridging it to the extract-level facts
               have hAiPkW : Halo2.ExtendsWitnesses place env
                   ((Ecc.WitnessPoint.pointNonIdFormal.call
                     cfg.eccConfig.witnessPoint input_var.pkDOld).operations (i₀ + 301))
                     (i₀ + 301) := by
                 have h := hWai
                 rw [FormalCircuit.call_operations] at h
                 simp only [AddressIntegrity.circuit, Circuit.operations_bind,
                   Circuit.operations_pure, operations_assignRegion,
                   Halo2.extendsWitnesses_append, Halo2.extendsWitnesses_nil,
                   FormalCircuit.nextRegionIndex_call,
                   Ecc.Mul.mul_call_regionCount, Nat.add_assoc, Nat.reduceAdd,
                   and_true] at h
                 exact h.2.1
               rw [wpointNonId_eval_eq_cells _ _ _ _ _ hAiPkW]
               refine ⟨?_, ?_⟩
               · exact hVpk
               · have h := hPkd
                 rw [← hIvkVal] at h
                 with_unfolding_all exact h)⟩
    · simp only [synthNotes, loadPrivate, circuit_norm, Nat.add_assoc, Nat.reduceAdd]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (NoteCommit.Main.circuit G B.noteCommitR B.noteQ
            B.noteQ_onCurve)
          { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
            lookupConfig := cfg.lookupConfig,
            mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add } (i₀ + 303) place env _ hWnco
          ⟨(by exact ⟨hT1, hFw, hTL, hDist⟩),
           (by rw [NoteCommit.Main.circuit_assumptions_eq, ncInputs_eval_eq]
               refine ⟨?_, ?_⟩
               · show Point.OnCurve _
                 exact hVgd
               · show Point.OnCurve _
                 exact hVpk),
           (by rw [NoteCommit.Main.circuit_proverAssumptions_eq]
               rw [ncInputs_eval_eq_prover]
               refine ⟨?_, ?_, ?_, ?_⟩
               · with_unfolding_all exact hVgd
               · with_unfolding_all exact hVpk
               · with_unfolding_all exact hV64o
               · refine ⟨Bo, ?_⟩
                 with_unfolding_all exact hBo)⟩
      · refine ⟨?_, ?_⟩
        · with_unfolding_all exact congrArg Point.x hNCoval
        · with_unfolding_all exact congrArg Point.y hNCoval
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          Ecc.WitnessPoint.pointNonIdFormal
          cfg.eccConfig.witnessPoint (i₀ + 347) place env _ hWgdn
          ⟨(by rw [Ecc.WitnessPoint.pointNonIdFormal_envAssumptions_eq]; trivial),
           (by rw [Ecc.WitnessPoint.pointNonIdFormal_assumptions_eq]; trivial),
           (by rw [Ecc.WitnessPoint.pointNonIdFormal_proverAssumptions_eq]
               show Point.OnCurve _
               rw [wpointNonId_eval_eq_cells _ _ _ _ _ hWgdn]
               exact hVgdn)⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          Ecc.WitnessPoint.pointNonIdFormal
          cfg.eccConfig.witnessPoint (i₀ + 348) place env _ hWpkn
          ⟨(by rw [Ecc.WitnessPoint.pointNonIdFormal_envAssumptions_eq]; trivial),
           (by rw [Ecc.WitnessPoint.pointNonIdFormal_assumptions_eq]; trivial),
           (by rw [Ecc.WitnessPoint.pointNonIdFormal_proverAssumptions_eq]
               show Point.OnCurve _
               rw [wpointNonId_eval_eq_cells _ _ _ _ _ hWpkn]
               exact hVpkn)⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (NoteCommit.Main.circuit G B.noteCommitR B.noteQ
            B.noteQ_onCurve)
          { gates := cfg.noteCommitNew, hashConfig := cfg.sinsemilla2,
            lookupConfig := cfg.lookupConfig,
            mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add } (i₀ + 350) place env _ hWncn
          ⟨(by exact ⟨hT2, hFw, hTL, hDist⟩),
           (by rw [NoteCommit.Main.circuit_assumptions_eq, ncInputs_eval_eq]
               refine ⟨?_, ?_⟩
               · show Point.OnCurve _
                 exact hVgdn
               · show Point.OnCurve _
                 exact hVpkn),
           (by rw [NoteCommit.Main.circuit_proverAssumptions_eq]
               rw [ncInputs_eval_eq_prover]
               refine ⟨?_, ?_, ?_, ?_⟩
               · with_unfolding_all exact hVgdn
               · with_unfolding_all exact hVpkn
               · with_unfolding_all exact hV64n
               · refine ⟨Bn, ?_⟩
                 rw [show ((eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
                     ((DeriveNullifier.circuit B.nullifierK).output
                       (cfg.poseidonConfig, cfg.addChipConfig,
                        cfg.eccConfig.mulFixedBaseField, cfg.eccConfig.add)
                       { nk := AssignedCell.of (i₀ + 5) 0 (cfg.advices 0),
                         rho := AssignedCell.of (i₀ + 1) 0 (cfg.advices 0),
                         psi := AssignedCell.of i₀ 0 (cfg.advices 0),
                         cm := { x := AssignedCell.of (i₀ + 2) 0
                                   cfg.eccConfig.witnessPoint.x,
                                 y := AssignedCell.of (i₀ + 2) 0
                                   cfg.eccConfig.witnessPoint.y } }
                       (i₀ + 271)) : Fp))
                   = (extract cfg input_var i₀
                       (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).nfOld
                   from by exact hDNval]
                 with_unfolding_all exact hBn)⟩
      · with_unfolding_all exact (congrArg Point.x hNCnval).trans hCmx.symm
      · -- the final `"Orchard circuit checks"` region
        simp only [nextRegionIndex_constrainInstance]
        obtain ⟨hOv, hOn, hOm, hOs, hOr, hOa, hOes, hOeo⟩ := hWorch
        have hOr' : env.advice (cfg.advices 4) ((place (i₀ + 393) : ℕ) : ℤ)
            = root := hOr.trans (by with_unfolding_all exact hM2root)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hOv
        · exact hOn
        · exact hOm
        · exact hOs
        · exact hOr
        · exact hOa
        · exact hOes
        · exact hOeo
        · simp only [orchardGate, Gate.withSelector, circuit_norm,
            List.Forall]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hOv, hOn, hOm, hOs]
            have h : env.advice (cfg.advices 0) ((place (i₀ + 6) : ℕ) : ℤ)
                - env.advice (cfg.advices 0) ((place (i₀ + 7) : ℕ) : ℤ)
                = env.advice (cfg.advices 9) ((place (i₀ + 264) : ℕ) : ℤ)
                  * env.advice (cfg.advices 9) ((place (i₀ + 265) : ℕ) : ℤ) := by
              with_unfolding_all exact hVms
            linear_combination h
          · rw [hOv, hOr', hOa]
            have h : env.advice (cfg.advices 0) ((place (i₀ + 6) : ℕ) : ℤ)
                * (root - env.inst cfg.primary ((ANCHOR : ℕ) : ℤ)) = 0 := by
              with_unfolding_all exact hVanch
            linear_combination h
          · rw [hOv, hOes]
            have h : env.advice (cfg.advices 0) ((place (i₀ + 6) : ℕ) : ℤ)
                * (1 - env.inst cfg.primary ((ENABLE_SPEND : ℕ) : ℤ)) = 0 := by
              with_unfolding_all exact hVes
            linear_combination h
          · rw [hOn, hOeo]
            have h : env.advice (cfg.advices 0) ((place (i₀ + 7) : ℕ) : ℤ)
                * (1 - env.inst cfg.primary ((ENABLE_OUTPUT : ℕ) : ℤ)) = 0 := by
              with_unfolding_all exact hVeo
            linear_combination h

/-- Rust `impl Circuit for Circuit` at `FixedPostNu6_2` (`synthesize_base`,
`circuit.rs:271-828`) as a proof-carrying bundle: the base §4.17.4 statement
(breaks-as-data) over the extracted primary-instance rows and witness data,
outputting the four witnessed address points. -/
def baseCircuit (G : Generators) (B : Bases) :
    FormalCircuit Fp Unit Config PrivateInputs AddressPoints where
  name := "OrchardActionBase"
  configure := fun _ => configure G
  synthesize := main G B
  elaborated := fun cfg => elaborated G B cfg
  Witness := fun _ => ActionData
  extract := extract
  EnvAssumptions := EnvAssumptions G
  Assumptions := fun _ => True
  Spec := Spec G B
  ProverAssumptions := ProverAssumptions G B
  ProverSpec := fun _ _ _ _ => True
  soundness := soundness G B
  completeness := completeness G B

/-! ## The ironwood (post-NU 6.3) circuit bundle

The main circuit: the proven base circuit called as a subcircuit, then the
`"post-NU 6.3 cross-address checks"` region on its output cells. -/

private theorem aafi_output (instCol : Column .instance) (r : ℕ)
    (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    ((assignAdviceFromInstance (F := Fp) instCol r col row).output self)
      = AssignedCell.of self row col := rfl

derive_contract_bridges base (G : Generators) (B : Bases) := baseCircuit G B

/-- The ironwood `FormalCircuit` entry: base subcircuit + cross-address region,
the private witness programs flowing through as the input. -/
def mainPost (G : Generators) (B : Bases) (cfg : Config) :
    Var PrivateInputs Fp → Circuit Fp (Var unit Fp) := fun W => do
  let pts ← (baseCircuit G B).call cfg W
  synthCrossAddressChecks cfg pts
  pure ()

theorem mainPost_regionCount (G : Generators) (B : Bases) (cfg : Config)
    (W : Witnesses Fp) (i : RegionIndex) :
    Operations.regionCount ((mainPost G B cfg W).operations i) = 395 := by
  simp only [mainPost, synthCrossAddressChecks, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, Operations.regionCount_append, Operations.regionCount]

instance elaboratedPost (G : Generators) (B : Bases) (cfg : Config) :
    ElaboratedCircuit Fp PrivateInputs unit (mainPost G B cfg) where
  output _ _ := ()
  regionCount _ := 395
  output_eq := by intro _ _; rfl
  regionCount_eq := fun W i => (mainPost_regionCount G B cfg W i).symm

/-- The ironwood Action statement: the base §4.17.4 statement, plus the post-NU 6.3
cross-address binding — a nonzero `DISABLE_CROSS_ADDRESS` instance row forces the new
note's diversified address to equal the old note's. -/
def SpecPost (G : Generators) (B : Bases)
    (_ : Value PrivateInputs Fp) (_ : Value unit Fp) (wit : ActionData) : Prop :=
  SpecBase G B wit ∧
  (wit.disableCrossAddress ≠ 0 → wit.gdOld = wit.gdNew ∧ wit.pkdOld = wit.pkdNew)

/-- Honest-prover preconditions for the ironwood circuit: the base preconditions, and
the cross-address rows hold at the honest values (the flag is off, or the addresses
coincide). -/
def ProverAssumptionsPost (G : Generators) (B : Bases)
    (input : WitnessData Fp) (wit : ActionData) (hint : ProverHint Fp) : Prop :=
  ProverAssumptions G B input wit hint ∧
  (wit.disableCrossAddress = 0 ∨ (wit.gdOld = wit.gdNew ∧ wit.pkdOld = wit.pkdNew))

theorem soundnessPost (G : Generators) (B : Bases) (cfg : Config) :
    FormalCircuit.Soundness (Witness := fun _ => ActionData)
      (mainPost G B cfg) (extract cfg) (EnvAssumptions G cfg) (fun _ => True)
      (SpecPost G B) := by
  circuit_proof_start
  -- re-bind the destructured formal input as `input_var` (see `completeness`); `extract`
  -- ignores this argument, so the reconstruction is the framework's input var.
  set input_var : Var PrivateInputs Fp :=
    { psiOld := input_var_psiOld, rhoOld := input_var_rhoOld, nk := input_var_nk,
      vOld := input_var_vOld, vNew := input_var_vNew, psiNew := input_var_psiNew,
      magnitude := input_var_magnitude, sign := input_var_sign, cmOld := input_var_cmOld,
      gdOld := input_var_gdOld, akP := input_var_akP, pkDOld := input_var_pkDOld,
      gdNew := input_var_gdNew, pkdNew := input_var_pkdNew, rcv := input_var_rcv,
      alpha := input_var_alpha, rivk := input_var_rivk, rcmOld := input_var_rcmOld,
      rcmNew := input_var_rcmNew, merkleSib := input_var_merkleSib,
      merkleSwap := input_var_merkleSwap } with hInputVarDef
  -- restore the concrete base-child output (abstracted to `x_gen_out_0` by the prefix) so the
  -- `base_output` bridge rewrites below fire.
  subst x_gen_out_0
  try simp only [mainPost, circuit_norm] at hc
  have hPre := hc.1
  have hX := hc.2
  clear hc
  -- the base chunk was consumed by circuit_proof_start; `hPre` is its EnvA → A → Spec implication
  have hS := hPre (by rw [base_envAssumptions_eq]; exact _hE)
    (by rw [base_assumptions_eq]; trivial)
  rw [base_spec_eq, base_extract_eq, base_output] at hS
  obtain ⟨hSB, -, -, -, -⟩ := hS
  -- ── the cross-address region: four `dca · (old − new) = 0` rows ──
  rw [base_output] at hX
  simp only [synthCrossAddressChecks, circuit_norm] at hX
  have h0 := hX 0
  have h1 := hX 1
  have h2 := hX 2
  have h3 := hX 3
  clear hX
  simp only [circuit_norm, aafi_output, List.get!Internal, Fin.isValue,
    Fin.val_zero, Fin.val_one, Nat.reduceMod, Nat.mul_one,
    Nat.add_zero] at h0 h1 h2 h3
  obtain ⟨ha00, -, -, -, ha04, ha05, -, -, -, -, hG0⟩ := h0
  obtain ⟨ha10, -, -, -, ha14, ha15, -, -, -, -, hG1⟩ := h1
  obtain ⟨ha20, -, -, -, ha24, ha25, -, -, -, -, hG2⟩ := h2
  obtain ⟨ha30, -, -, -, ha34, ha35, -, -, -, -, hG3⟩ := h3
  simp only [orchardGate, Gate.withSelector, circuit_norm,
    List.Forall] at hG0 hG1 hG2 hG3
  have e0 := hG0.2.1
  have e1 := hG1.2.1
  have e2 := hG2.2.1
  have e3 := hG3.2.1
  rw [ha00, ha04, ha05] at e0
  rw [ha10, ha14, ha15] at e1
  rw [ha20, ha24, ha25] at e2
  rw [ha30, ha34, ha35] at e3
  -- ── assemble ──
  simp only [SpecPost]
  refine ⟨hSB, ?_⟩
  intro hdca
  have hgx : (extract cfg input_var i₀
        (⟨place, env⟩ : Placed Environment Fp)).gdOld.x
      = (extract cfg input_var i₀ (⟨place, env⟩ : Placed Environment Fp)).gdNew.x :=
    sub_eq_zero.mp ((mul_eq_zero.mp (by simp only [circuit_norm, explicit_provable_type, extract, cellRead]; exact e0)).resolve_left hdca)
  have hgy : (extract cfg input_var i₀
        (⟨place, env⟩ : Placed Environment Fp)).gdOld.y
      = (extract cfg input_var i₀ (⟨place, env⟩ : Placed Environment Fp)).gdNew.y :=
    sub_eq_zero.mp ((mul_eq_zero.mp (by simp only [circuit_norm, explicit_provable_type, extract, cellRead]; exact e1)).resolve_left hdca)
  have hpx : (extract cfg input_var i₀
        (⟨place, env⟩ : Placed Environment Fp)).pkdOld.x
      = (extract cfg input_var i₀ (⟨place, env⟩ : Placed Environment Fp)).pkdNew.x :=
    sub_eq_zero.mp ((mul_eq_zero.mp (by simp only [circuit_norm, explicit_provable_type, extract, cellRead]; exact e2)).resolve_left hdca)
  have hpy : (extract cfg input_var i₀
        (⟨place, env⟩ : Placed Environment Fp)).pkdOld.y
      = (extract cfg input_var i₀ (⟨place, env⟩ : Placed Environment Fp)).pkdNew.y :=
    sub_eq_zero.mp ((mul_eq_zero.mp (by simp only [circuit_norm, explicit_provable_type, extract, cellRead]; exact e3)).resolve_left hdca)
  constructor
  · apply Point.ext_coords
    show (_, _) = _
    rw [hgx, hgy]
    rfl
  · apply Point.ext_coords
    show (_, _) = _
    rw [hpx, hpy]
    rfl

theorem completenessPost (G : Generators) (B : Bases) (cfg : Config) :
    FormalCircuit.Completeness (Witness := fun _ => ActionData)
      (mainPost G B cfg) (extract cfg) (EnvAssumptions G cfg) (fun _ => True)
      (ProverAssumptionsPost G B) (fun _ _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨hPA, hDca⟩ := hPA
  -- restore the concrete base-child output (abstracted to `x_gen_out_0` by the prefix) so the
  -- `base_output` bridge rewrites below fire.
  subst x_gen_out_0
  try simp only [mainPost, circuit_norm] at hwit ⊢
  obtain ⟨-, hWx⟩ := hwit
  -- the base chunk was consumed by circuit_proof_start (completeness mode), so the goal opens
  -- with the base child's preconditions rather than its witness constraints.
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [base_envAssumptions_eq]; exact _hE
  · rw [base_assumptions_eq]; trivial
  · rw [base_proverAssumptions_eq, base_extract_eq]; exact hPA
  · -- the cross-address region at the honest values
    rw [base_output]
    rw [base_output] at hWx
    simp only [synthCrossAddressChecks, circuit_norm] at hWx ⊢
    have hw0 := hWx 0
    have hw1 := hWx 1
    have hw2 := hWx 2
    have hw3 := hWx 3
    clear hWx
    simp only [circuit_norm, aafi_output, List.get!Internal, Fin.isValue,
      Fin.val_zero, Nat.mul_one, Nat.add_zero] at hw0 hw1 hw2 hw3
    -- the four honest `dca · (old − new) = 0` products
    have hdx : (env.inst cfg.primary ((DISABLE_CROSS_ADDRESS : ℕ) : ℤ) : Fp)
        * (env.advice cfg.eccConfig.witnessPoint.x ((place (i₀ + 3) : ℕ) : ℤ)
           - env.advice cfg.eccConfig.witnessPoint.x ((place (i₀ + 347) : ℕ) : ℤ))
        = 0 := by
      rcases hDca with hz | ⟨hg, -⟩
      · rw [show (env.inst cfg.primary ((DISABLE_CROSS_ADDRESS : ℕ) : ℤ) : Fp) = 0
            from by exact hz]
        ring
      · rw [show (env.advice cfg.eccConfig.witnessPoint.x
              ((place (i₀ + 3) : ℕ) : ℤ) : Fp)
            = env.advice cfg.eccConfig.witnessPoint.x ((place (i₀ + 347) : ℕ) : ℤ)
            from by with_unfolding_all exact congrArg Point.x hg]
        ring
    have hdy : (env.inst cfg.primary ((DISABLE_CROSS_ADDRESS : ℕ) : ℤ) : Fp)
        * (env.advice cfg.eccConfig.witnessPoint.y ((place (i₀ + 3) : ℕ) : ℤ)
           - env.advice cfg.eccConfig.witnessPoint.y ((place (i₀ + 347) : ℕ) : ℤ))
        = 0 := by
      rcases hDca with hz | ⟨hg, -⟩
      · rw [show (env.inst cfg.primary ((DISABLE_CROSS_ADDRESS : ℕ) : ℤ) : Fp) = 0
            from by exact hz]
        ring
      · rw [show (env.advice cfg.eccConfig.witnessPoint.y
              ((place (i₀ + 3) : ℕ) : ℤ) : Fp)
            = env.advice cfg.eccConfig.witnessPoint.y ((place (i₀ + 347) : ℕ) : ℤ)
            from by with_unfolding_all exact congrArg Point.y hg]
        ring
    have hpx : (env.inst cfg.primary ((DISABLE_CROSS_ADDRESS : ℕ) : ℤ) : Fp)
        * (env.advice cfg.eccConfig.witnessPoint.x ((place (i₀ + 301) : ℕ) : ℤ)
           - env.advice cfg.eccConfig.witnessPoint.x ((place (i₀ + 348) : ℕ) : ℤ))
        = 0 := by
      rcases hDca with hz | ⟨-, hp⟩
      · rw [show (env.inst cfg.primary ((DISABLE_CROSS_ADDRESS : ℕ) : ℤ) : Fp) = 0
            from by exact hz]
        ring
      · rw [show (env.advice cfg.eccConfig.witnessPoint.x
              ((place (i₀ + 301) : ℕ) : ℤ) : Fp)
            = env.advice cfg.eccConfig.witnessPoint.x ((place (i₀ + 348) : ℕ) : ℤ)
            from by with_unfolding_all exact congrArg Point.x hp]
        ring
    have hpy : (env.inst cfg.primary ((DISABLE_CROSS_ADDRESS : ℕ) : ℤ) : Fp)
        * (env.advice cfg.eccConfig.witnessPoint.y ((place (i₀ + 301) : ℕ) : ℤ)
           - env.advice cfg.eccConfig.witnessPoint.y ((place (i₀ + 348) : ℕ) : ℤ))
        = 0 := by
      rcases hDca with hz | ⟨-, hp⟩
      · rw [show (env.inst cfg.primary ((DISABLE_CROSS_ADDRESS : ℕ) : ℤ) : Fp) = 0
            from by exact hz]
        ring
      · rw [show (env.advice cfg.eccConfig.witnessPoint.y
              ((place (i₀ + 301) : ℕ) : ℤ) : Fp)
            = env.advice cfg.eccConfig.witnessPoint.y ((place (i₀ + 348) : ℕ) : ℤ)
            from by with_unfolding_all exact congrArg Point.y hp]
        ring
    intro i
    fin_cases i
    all_goals simp only [circuit_norm, aafi_output, List.get!Internal, Fin.isValue,
      Nat.mul_one, Nat.add_zero]
    · obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hw0
      refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, ?_⟩
      simp only [orchardGate, Gate.withSelector, circuit_norm, List.Forall]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [w2, w3, w1, w0]
        ring
      · rw [w4, w5, w0]
        linear_combination hdx
      · rw [w6, w0]
        ring
      · rw [w7, w1]
        ring
    · obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hw1
      refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, ?_⟩
      simp only [orchardGate, Gate.withSelector, circuit_norm, List.Forall]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [w2, w3, w1, w0]
        ring
      · rw [w4, w5, w0]
        linear_combination hdy
      · rw [w6, w0]
        ring
      · rw [w7, w1]
        ring
    · obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hw2
      refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, ?_⟩
      simp only [orchardGate, Gate.withSelector, circuit_norm, List.Forall]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [w2, w3, w1, w0]
        ring
      · rw [w4, w5, w0]
        linear_combination hpx
      · rw [w6, w0]
        ring
      · rw [w7, w1]
        ring
    · obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hw3
      refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, ?_⟩
      simp only [orchardGate, Gate.withSelector, circuit_norm, List.Forall]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [w2, w3, w1, w0]
        ring
      · rw [w4, w5, w0]
        linear_combination hpy
      · rw [w6, w0]
        ring
      · rw [w7, w1]
        ring

/-- Rust `impl Circuit for Circuit` on the ironwood branch (post-NU 6.3) as a
proof-carrying bundle: the e2e Orchard Action statement (§4.17.4 + cross-address
binding, breaks-as-data) over the extracted primary-instance rows and witness data. -/
def circuit (G : Generators) (B : Bases) :
    FormalCircuit Fp Unit Config PrivateInputs unit where
  name := "OrchardAction"
  configure := fun _ => configure G
  synthesize := mainPost G B
  elaborated := fun cfg => elaboratedPost G B cfg
  Witness := fun _ => ActionData
  extract := extract
  EnvAssumptions := EnvAssumptions G
  Assumptions := fun _ => True
  Spec := SpecPost G B
  ProverAssumptions := ProverAssumptionsPost G B
  ProverSpec := fun _ _ _ _ => True
  soundness := soundnessPost G B
  completeness := completenessPost G B

end Zcash.Circuits.Action.Circuit
