import Clean.Ironwood.Action.Circuit

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

namespace Halo2.Ironwood.Action.Circuit

open Halo2.Ironwood (Fp)
open Orchard (Point)
open Orchard.Ecc.MulFixed (FixedBase)
open Orchard.Specs.Sinsemilla (Generators hashToPoint hashToPointB SpecOrBreak
  commitIvkChunks)
open CompElliptic.Fields.Pasta (Fq)

/-! ## Region counts -/

private theorem toFormal_call_regionCount {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) (cfg : Cfg)
    (inp : Var In Fp) (j : RegionIndex) :
    Operations.regionCount (((b.toFormal name).call cfg inp).operations j) = 1 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem wpoint_call_regionCount (name : String)
    (c : Ecc.WitnessPoint.Config) (inp : Point (FExpr Fp)) (j : RegionIndex) :
    Operations.regionCount
      (((Ecc.WitnessPoint.point.toFormal name).call c inp).operations j) = 1 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem wpointNonId_call_regionCount (name : String)
    (c : Ecc.WitnessPoint.Config) (inp : Point (FExpr Fp)) (j : RegionIndex) :
    Operations.regionCount
      (((Ecc.WitnessPoint.pointNonId.toFormal name).call c inp).operations j) = 1 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem merkle_call_regionCount (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l₀ : ℕ) (hld : l₀ + 16 ≤ 2 ^ 10)
    (wsib : ℕ → WitgenIR Fp 1) (wswap : ℕ → Placed ProverEnvironment Fp → Bool)
    (c : CondSwap.Config × Sinsemilla.Merkle.Config ×
      LookupRangeCheck.Config 10)
    (inp : Var Sinsemilla.Merkle.Layer.Input Fp) (j : RegionIndex) :
    Operations.regionCount
      (((Sinsemilla.Merkle.CalculateRoot.circuit G Q hQ l₀ 16 hld wsib wswap).call
        c inp).operations j) = 128 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem vc_call_regionCount (V : Orchard.Ecc.MulFixed.Short.FixedBase)
    (R : FixedBase) (w : Vector (FExpr Fp) 85)
    (c : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (inp : Var Ecc.MulFixed.Short.Inputs Fp) (j : RegionIndex) :
    Operations.regionCount
      (((ValueCommit.circuit V R w).call c inp).operations j) = 5 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem dn_call_regionCount (K : FixedBase)
    (c : Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config ×
      Ecc.Add.Config)
    (inp : Var DeriveNullifier.Input Fp) (j : RegionIndex) :
    Operations.regionCount
      (((DeriveNullifier.circuit K).call c inp).operations j) = 9 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem sa_call_regionCount (G : FixedBase) (w : Vector (FExpr Fp) 85)
    (c : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (inp : Var SpendAuthority.Input Fp) (j : RegionIndex) :
    Operations.regionCount
      (((SpendAuthority.circuit G w).call c inp).operations j) = 3 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem civk_call_regionCount (G : Generators) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : CommitIvk.Main.Config) (inp : Var CommitIvk.Main.Inputs Fp)
    (j : RegionIndex) :
    Operations.regionCount
      (((CommitIvk.Main.circuit G R w Q hQ).call c inp).operations j) = 14 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem ai_call_regionCount (pkD : Point (FExpr Fp))
    (c : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (inp : Var AddressIntegrity.Input Fp) (j : RegionIndex) :
    Operations.regionCount
      (((AddressIntegrity.circuit pkD).call c inp).operations j) = 6 := by
  rw [FormalCircuit.call_regionCount]
  rfl

private theorem nc_call_regionCount (G : Generators) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : NoteCommit.Main.Config) (inp : Var NoteCommit.Main.Inputs Fp)
    (j : RegionIndex) :
    Operations.regionCount
      (((NoteCommit.Main.circuit G R w Q hQ).call c inp).operations j) = 43 := by
  rw [FormalCircuit.call_regionCount]
  rfl

set_option linter.unusedSimpArgs false in
theorem synthWitness_regionCount (G : Generators) (W : Witnesses) (cfg : Config)
    (i : RegionIndex) :
    Operations.regionCount ((synthWitness G W cfg).operations i) = 8 := by
  simp only [synthWitness, loadPrivate, Sinsemilla.load, circuit_norm,
    Circuit.operations_bind, Circuit.operations_pure, operations_assignRegion,
    operations_loadTable, Operations.regionCount_append, Operations.regionCount]
  rw [wpoint_call_regionCount, wpointNonId_call_regionCount,
    wpointNonId_call_regionCount]

set_option linter.unusedSimpArgs false in
theorem synthChecks_regionCount (G : Generators) (B : Bases) (W : Witnesses)
    (cfg : Config) (wc : WitnessCells) (i : RegionIndex) :
    Operations.regionCount ((synthChecks G B W cfg wc).operations i) = 295 := by
  simp only [synthChecks, loadPrivate, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, operations_assignRegion, operations_constrainInstance,
    Operations.regionCount_append, Operations.regionCount]
  rw [merkle_call_regionCount, merkle_call_regionCount, vc_call_regionCount,
    dn_call_regionCount, sa_call_regionCount, civk_call_regionCount,
    ai_call_regionCount]

set_option linter.unusedSimpArgs false in
theorem synthNotes_regionCount (G : Generators) (B : Bases) (W : Witnesses)
    (cfg : Config) (wc : WitnessCells) (cc : CheckCells) (i : RegionIndex) :
    Operations.regionCount ((synthNotes G B W cfg wc cc).operations i) = 91 := by
  simp only [synthNotes, loadPrivate, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, operations_assignRegion, operations_constrainInstance,
    Operations.regionCount_append, Operations.regionCount]
  rw [nc_call_regionCount, wpointNonId_call_regionCount,
    wpointNonId_call_regionCount, nc_call_regionCount]

set_option linter.unusedSimpArgs false in
/-- The Action circuit's region count: the 8 witness regions, the 295-region check
stage, the 91-region note stage — 394. -/
theorem synthesize_regionCount (G : Generators) (B : Bases) (W : Witnesses)
    (cfg : Config) (i : RegionIndex) :
    Operations.regionCount ((synthesize G B W cfg).operations i) = 394 := by
  simp only [synthesize, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, Operations.regionCount_append, Operations.regionCount]
  rw [synthWitness_regionCount, synthChecks_regionCount, synthNotes_regionCount]

/-- The `FormalCircuit` entry: `unit → unit`, everything through the extraction. -/
def main (G : Generators) (B : Bases) (W : Witnesses) (cfg : Config) :
    Var unit Fp → Circuit Fp (Var unit Fp) := fun _ => do
  synthesize G B W cfg
  pure ()

set_option linter.unusedSimpArgs false in
theorem main_regionCount (G : Generators) (B : Bases) (W : Witnesses)
    (cfg : Config) (inp : Var unit Fp) (i : RegionIndex) :
    Operations.regionCount ((main G B W cfg inp).operations i) = 394 := by
  simp only [main, Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount]
  rw [synthesize_regionCount]

instance elaborated (G : Generators) (B : Bases) (W : Witnesses) (cfg : Config) :
    ElaboratedCircuit Fp unit unit (main G B W cfg) where
  output _ _ := ()
  regionCount _ := 394
  output_eq := by intro _ _; rfl
  regionCount_eq := fun input i => (main_regionCount G B W cfg input i).symm

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
  rcv : Vector Fp 85 × Fq
  alpha : Vector Fp 85 × Fq
  rivk : Vector Fp 85 × Fq
  rcmOld : Vector Fp 85 × Fq
  rcmNew : Vector Fp 85 × Fq

/-- One advice cell read. -/
private def cellRead (env : Placed Environment Fp) (i : RegionIndex) (row : ℕ)
    (col : Column .advice) : Fp :=
  eval env (AssignedCell.of i row col : Var field Fp)

/-- The extraction: instance rows off `primary`, witness cells at their regions,
the witnessed points, and the five `fwExtract` window readings (region map in
`synthesize_regionCount`'s docstring). -/
def extract (cfg : Config) (_ : Var unit Fp) (i₀ : RegionIndex)
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
  rcv := Ecc.MulFixed.FullWidth.fwExtract cfg.eccConfig.mulFixedFull (i₀ + 268) env
  alpha := Ecc.MulFixed.FullWidth.fwExtract cfg.eccConfig.mulFixedFull (i₀ + 280) env
  rivk := Ecc.MulFixed.FullWidth.fwExtract cfg.eccConfig.mulFixedFull (i₀ + 290) env
  rcmOld := Ecc.MulFixed.FullWidth.fwExtract cfg.eccConfig.mulFixedFull (i₀ + 328) env
  rcmNew := Ecc.MulFixed.FullWidth.fwExtract cfg.eccConfig.mulFixedFull (i₀ + 375) env

/-! ## The statement (§4.17.4, knowledge-sound, breaks-as-data) -/

open Orchard.Action.NoteCommit (noteScalars)

/-- The Orchard Action statement over the extracted data: every §4.17.4 clause, with
the Sinsemilla escapes exhibited as data and the fixed-base scalars knowledge-sound at
the extracted window readings. -/
def Spec (G : Generators) (B : Bases)
    (_ : Value unit Fp) (_ : Value unit Fp) (wit : ActionData) : Prop :=
  -- the witnessed points are well-formed
  wit.cmOld.Valid ∧ wit.gdOld.OnCurve ∧ wit.akP.OnCurve ∧ wit.pkdOld.OnCurve ∧
  wit.gdNew.OnCurve ∧ wit.pkdNew.OnCurve ∧
  -- value-commitment integrity: `cv_net = [v_old − v_new] V + [rcv] R`
  (∃ m : ℕ, m < 2 ^ 64 ∧ wit.magnitude = (m : Fp) ∧
    ((wit.sign = 1 ∧ (⟨wit.cvX, wit.cvY⟩ : Point Fp)
        = ((m : Fq) • B.valueCommitV : Point Fp) + (wit.rcv.2 • B.valueCommitR : Point Fp)) ∨
     (wit.sign = -1 ∧ (⟨wit.cvX, wit.cvY⟩ : Point Fp)
        = (((-(m : Fq)) : Fq) • B.valueCommitV : Point Fp)
          + (wit.rcv.2 • B.valueCommitR : Point Fp)))) ∧
  -- nullifier integrity: `nf_old = Extract([PRF(nk, ρ) + ψ] K + cm_old)`
  wit.nfOld = ((wit.cmOld +
    ((Orchard.Poseidon.Hash.ConstantLength.value #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq)
      • B.nullifierK : Point Fp)).x ∧
  -- spend authority: `rk = [α] SpendAuthG + ak_P`
  (⟨wit.rkX, wit.rkY⟩ : Point Fp)
    = (wit.alpha.2 • B.spendAuthG : Point Fp) + wit.akP ∧
  -- diversified-address integrity: `ivk ∈ {Commit^ivk, ⊥}` (break exhibited) and
  -- `pk_d_old = [ivk] g_d_old`
  (∃ ivk : Fp,
    SpecOrBreak G.S B.ivkQ
      (fun bp => ivk = (bp + (wit.rivk.2 • B.commitIvkR : Point Fp)).x)
      (hashToPointB G.S B.ivkQ (commitIvkChunks wit.akP.x.val wit.nk.val)) ∧
    wit.pkdOld = (ivk.val • wit.gdOld : Point Fp)) ∧
  -- old note-commitment integrity: `NoteCommit(…) ∈ {cm_old, ⊥}` (break exhibited)
  SpecOrBreak G.S B.noteQ
    (fun bp => wit.cmOld = bp + (wit.rcmOld.2 • B.noteCommitR : Point Fp))
    (hashToPointB G.S B.noteQ
      (noteScalars wit.gdOld wit.pkdOld wit.vOld wit.rhoOld wit.psiOld).chunks) ∧
  -- new note-commitment integrity, `ρ_new = nf_old`:
  -- `Extract(NoteCommit(…)) ∈ {cmx, ⊥}` (break exhibited)
  SpecOrBreak G.S B.noteQ
    (fun bp => wit.cmx = (bp + (wit.rcmNew.2 • B.noteCommitR : Point Fp)).x)
    (hashToPointB G.S B.noteQ
      (noteScalars wit.gdNew wit.pkdNew wit.vNew wit.nfOld wit.psiNew).chunks) ∧
  -- Merkle path validity, tied through the `q_orchard` anchor check
  (∃ root : Fp,
    Sinsemilla.Merkle.MerkleRoot G B.merkleQ 0 wit.cmOld.x 32 root ∧
    wit.vOld * (root - wit.anchor) = 0) ∧
  -- the remaining `q_orchard` value checks
  wit.vOld - wit.vNew = wit.magnitude * wit.sign ∧
  wit.vOld * (1 - wit.enableSpend) = 0 ∧
  wit.vNew * (1 - wit.enableOutput) = 0

/-- Env preconditions: the loaded tables and selector-distinctness every child asserts. -/
def EnvAssumptions (G : Generators) (cfg : Config)
    (env : Placed Environment Fp) : Prop :=
  Sinsemilla.GeneratorTableLoaded G cfg.sinsemilla1.generatorTable env.env ∧
  Sinsemilla.GeneratorTableLoaded G cfg.sinsemilla2.generatorTable env.env ∧
  Ecc.MulFixed.FullWidth.EnvAssumptions cfg.eccConfig.mulFixedFull env ∧
  Ecc.MulFixed.Short.EnvAssumptions cfg.eccConfig.mulFixedShort env ∧
  Ecc.MulFixed.BaseFieldElem.EnvAssumptions cfg.eccConfig.mulFixedBaseField env ∧
  Ecc.Mul.EnvAssumptions cfg.eccConfig.mul env ∧
  LookupRangeCheck.TableLoaded 10 cfg.lookupConfig env.env ∧
  cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index

end Halo2.Ironwood.Action.Circuit
