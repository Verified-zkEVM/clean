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

theorem synthWitness_regionCount (G : Generators) (W : Witnesses) (cfg : Config)
    (i : RegionIndex) :
    Operations.regionCount ((synthWitness G W cfg).operations i) = 8 := by
  simp only [synthWitness, loadPrivate, Sinsemilla.load, circuit_norm,
    Circuit.operations_bind, Circuit.operations_pure, operations_assignRegion,
    operations_loadTable, Operations.regionCount_append, Operations.regionCount]
  rw [wpoint_call_regionCount, wpointNonId_call_regionCount,
    wpointNonId_call_regionCount]

theorem synthChecks_regionCount (G : Generators) (B : Bases) (W : Witnesses)
    (cfg : Config) (wc : WitnessCells) (i : RegionIndex) :
    Operations.regionCount ((synthChecks G B W cfg wc).operations i) = 295 := by
  simp only [synthChecks, loadPrivate, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, operations_assignRegion, operations_constrainInstance,
    Operations.regionCount_append, Operations.regionCount]
  rw [merkle_call_regionCount, merkle_call_regionCount, vc_call_regionCount,
    dn_call_regionCount, sa_call_regionCount, civk_call_regionCount,
    ai_call_regionCount]

theorem synthNotes_regionCount (G : Generators) (B : Bases) (W : Witnesses)
    (cfg : Config) (wc : WitnessCells) (cc : CheckCells) (i : RegionIndex) :
    Operations.regionCount ((synthNotes G B W cfg wc cc).operations i) = 91 := by
  simp only [synthNotes, loadPrivate, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, operations_assignRegion, operations_constrainInstance,
    Operations.regionCount_append, Operations.regionCount]
  rw [nc_call_regionCount, wpointNonId_call_regionCount,
    wpointNonId_call_regionCount, nc_call_regionCount]

/-- The Action circuit's region count: the 8 witness regions, the 295-region check
stage, the 91-region note stage — 394. -/
theorem synthesize_regionCount (G : Generators) (B : Bases) (W : Witnesses)
    (cfg : Config) (i : RegionIndex) :
    Operations.regionCount ((CircuitPreIronwood.synthesize G B W cfg).operations i)
      = 394 := by
  simp only [CircuitPreIronwood.synthesize, circuit_norm, Circuit.operations_bind,
    Operations.regionCount_append]
  rw [synthWitness_regionCount, synthChecks_regionCount, synthNotes_regionCount]

/-- The `FormalCircuit` entry: `unit → unit`, everything through the extraction. -/
def main (G : Generators) (B : Bases) (W : Witnesses) (cfg : Config) :
    Var unit Fp → Circuit Fp (Var unit Fp) := fun _ => do
  let _ ← CircuitPreIronwood.synthesize G B W cfg
  pure ()

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

/-! ## Child contract bridges (`rfl`, children stay folded) -/

private theorem toFormal_spec_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) :
    (b.toFormal name).Spec = b.Spec := rfl

private theorem toFormal_assumptions_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) :
    (b.toFormal name).Assumptions = b.Assumptions := rfl

private theorem toFormal_envAssumptions_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) (cfg : Cfg)
    (env : Placed Environment Fp) :
    (b.toFormal name).EnvAssumptions cfg env = b.EnvAssumptions cfg env := rfl

private theorem wpoint_envAssumptions_eq (name : String)
    (c : Ecc.WitnessPoint.Config) (env : Placed Environment Fp) :
    (Ecc.WitnessPoint.point.toFormal name).EnvAssumptions c env = True := rfl

private theorem wpointNonId_envAssumptions_eq (name : String)
    (c : Ecc.WitnessPoint.Config) (env : Placed Environment Fp) :
    (Ecc.WitnessPoint.pointNonId.toFormal name).EnvAssumptions c env = True := rfl

private theorem wpoint_assumptions_eq (name : String) :
    (Ecc.WitnessPoint.point.toFormal name).Assumptions = fun _ => True := rfl

private theorem wpointNonId_assumptions_eq (name : String) :
    (Ecc.WitnessPoint.pointNonId.toFormal name).Assumptions = fun _ => True := rfl

private theorem wpoint_proverAssumptions_eq (name : String) :
    (Ecc.WitnessPoint.point.toFormal name).ProverAssumptions
      = Ecc.WitnessPoint.point.ProverAssumptions := rfl

private theorem wpointNonId_proverAssumptions_eq (name : String) :
    (Ecc.WitnessPoint.pointNonId.toFormal name).ProverAssumptions
      = Ecc.WitnessPoint.pointNonId.ProverAssumptions := rfl

private theorem wpoint_spec_eq (name : String) :
    (Ecc.WitnessPoint.point.toFormal name).Spec
      = fun _ (output : Value Point Fp) _ => output.Valid := rfl

private theorem wpointNonId_spec_eq (name : String) :
    (Ecc.WitnessPoint.pointNonId.toFormal name).Spec
      = fun _ (output : Value Point Fp) _ => output.OnCurve := rfl

private theorem wpoint_output (name : String) (c : Ecc.WitnessPoint.Config)
    (inp : Point (FExpr Fp)) (i : RegionIndex) :
    (Ecc.WitnessPoint.point.toFormal name).output c inp i
      = ({ x := AssignedCell.of i 0 c.x, y := AssignedCell.of i 0 c.y }
        : Var Point Fp) := rfl

private theorem wpointNonId_output (name : String) (c : Ecc.WitnessPoint.Config)
    (inp : Point (FExpr Fp)) (i : RegionIndex) :
    (Ecc.WitnessPoint.pointNonId.toFormal name).output c inp i
      = ({ x := AssignedCell.of i 0 c.x, y := AssignedCell.of i 0 c.y }
        : Var Point Fp) := rfl

private theorem merkle_spec_eq (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l₀ : ℕ) (hld : l₀ + 16 ≤ 2 ^ 10) (wsib : ℕ → WitgenIR Fp 1)
    (wswap : ℕ → Placed ProverEnvironment Fp → Bool) :
    (Sinsemilla.Merkle.CalculateRoot.circuit G Q hQ l₀ 16 hld wsib wswap).Spec
      = fun input (output : Value field Fp) _ =>
          Sinsemilla.Merkle.MerkleRoot G Q l₀ (input.node : Fp) 16 output := rfl

private theorem merkle_assumptions_eq (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l₀ : ℕ) (hld : l₀ + 16 ≤ 2 ^ 10) (wsib : ℕ → WitgenIR Fp 1)
    (wswap : ℕ → Placed ProverEnvironment Fp → Bool) :
    (Sinsemilla.Merkle.CalculateRoot.circuit G Q hQ l₀ 16 hld wsib wswap).Assumptions
      = fun _ => True := rfl

private theorem merkle_envAssumptions_eq (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l₀ : ℕ) (hld : l₀ + 16 ≤ 2 ^ 10) (wsib : ℕ → WitgenIR Fp 1)
    (wswap : ℕ → Placed ProverEnvironment Fp → Bool)
    (c : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (env : Placed Environment Fp) :
    (Sinsemilla.Merkle.CalculateRoot.circuit G Q hQ l₀ 16 hld wsib
        wswap).EnvAssumptions c env
      = (Sinsemilla.GeneratorTableLoaded G c.2.1.sinsemilla.generatorTable env.env ∧
          LookupRangeCheck.TableLoaded 10 c.2.2 env.env ∧
          c.2.2.qLookup.index ≠ c.2.2.qRunning.index) := rfl

private theorem vc_spec_eq (V : Orchard.Ecc.MulFixed.Short.FixedBase) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) :
    (ValueCommit.circuit V R w).Spec
      = fun (input : Value Ecc.MulFixed.Short.Inputs Fp) (output : Value Point Fp)
          (wit : Vector Fp 85 × Fq) =>
          ∃ m : ℕ, m < 2 ^ 64 ∧ input.magnitude = (m : Fp) ∧
            ((input.sign = 1 ∧
                output = ((m : Fq) • V : Point Fp) + (wit.2 • R : Point Fp)) ∨
              (input.sign = -1 ∧
                output = (((-(m : Fq)) : Fq) • V : Point Fp)
                  + (wit.2 • R : Point Fp))) := rfl

private theorem vc_extract_eq (V : Orchard.Ecc.MulFixed.Short.FixedBase)
    (R : FixedBase) (w : Vector (FExpr Fp) 85)
    (c : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (inp : Var Ecc.MulFixed.Short.Inputs Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (ValueCommit.circuit V R w).extract c inp i env
      = Ecc.MulFixed.FullWidth.fwExtract c.2.1 (i + 2) env := rfl

private theorem dn_spec_eq (K : FixedBase) :
    (DeriveNullifier.circuit K).Spec
      = fun (input : Value DeriveNullifier.Input Fp) (output : Value field Fp) _ =>
          (output : Fp) = ((input.cm +
            ((Orchard.Poseidon.Hash.ConstantLength.value #v[input.nk, input.rho]
              + input.psi).val : Fq) • K : Point Fp)).x := rfl

private theorem sa_spec_eq (G : FixedBase) (w : Vector (FExpr Fp) 85) :
    (SpendAuthority.circuit G w).Spec
      = fun (input : Value SpendAuthority.Input Fp) (output : Value Point Fp)
          (wit : Vector Fp 85 × Fq) =>
          output = (wit.2 • G : Point Fp) + input.akP := rfl

private theorem sa_extract_eq (G : FixedBase) (w : Vector (FExpr Fp) 85)
    (c : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (inp : Var SpendAuthority.Input Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (SpendAuthority.circuit G w).extract c inp i env
      = Ecc.MulFixed.FullWidth.fwExtract c.1 i env := rfl

private theorem civk_spec_eq (G : Generators) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) :
    (CommitIvk.Main.circuit G R w Q hQ).Spec
      = CommitIvk.Main.Spec G Q R := rfl

private theorem civk_extract_eq (G : Generators) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : CommitIvk.Main.Config) (inp : Var CommitIvk.Main.Inputs Fp)
    (i : RegionIndex) (env : Placed Environment Fp) :
    (CommitIvk.Main.circuit G R w Q hQ).extract c inp i env
      = Ecc.MulFixed.FullWidth.fwExtract c.mulConfig (i + 7) env := rfl

private theorem ai_spec_eq (pkD : Point (FExpr Fp)) :
    (AddressIntegrity.circuit pkD).Spec
      = fun (input : Value AddressIntegrity.Input Fp) (output : Value Point Fp) _ =>
          output.OnCurve ∧ output = (input.ivk.val • input.gDOld : Point Fp) := rfl

private theorem ai_output (pkD : Point (FExpr Fp))
    (c : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (inp : Var AddressIntegrity.Input Fp) (i : RegionIndex) :
    (AddressIntegrity.circuit pkD).output c inp i
      = ({ x := AssignedCell.of (i + 4) 0 c.2.x, y := AssignedCell.of (i + 4) 0 c.2.y }
        : Var Point Fp) := rfl

private theorem nc_spec_eq (G : Generators) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) :
    (NoteCommit.Main.circuit G R w Q hQ).Spec
      = NoteCommit.Main.Spec G Q R := rfl

private theorem nc_assumptions_eq (G : Generators) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) :
    (NoteCommit.Main.circuit G R w Q hQ).Assumptions
      = fun (input : Value NoteCommit.Main.Inputs Fp) =>
          Orchard.Point.OnCurve ⟨input.gdX, input.gdY⟩ ∧
          Orchard.Point.OnCurve ⟨input.pkdX, input.pkdY⟩ := rfl

private theorem ncInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c1 c2 c3 c4 c5 c6 c7 : AssignedCell Fp) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ({ gdX := c1, gdY := c2, pkdX := c3, pkdY := c4, value := c5, rho := c6,
         psi := c7 } : Var NoteCommit.Main.Inputs Fp))
    = { gdX := eval (⟨place, env⟩ : Placed Environment Fp) (c1 : Var field Fp),
        gdY := eval (⟨place, env⟩ : Placed Environment Fp) (c2 : Var field Fp),
        pkdX := eval (⟨place, env⟩ : Placed Environment Fp) (c3 : Var field Fp),
        pkdY := eval (⟨place, env⟩ : Placed Environment Fp) (c4 : Var field Fp),
        value := eval (⟨place, env⟩ : Placed Environment Fp) (c5 : Var field Fp),
        rho := eval (⟨place, env⟩ : Placed Environment Fp) (c6 : Var field Fp),
        psi := eval (⟨place, env⟩ : Placed Environment Fp) (c7 : Var field Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval]
  with_unfolding_all rfl

private theorem vcInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c1 c2 : AssignedCell Fp) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ({ magnitude := c1, sign := c2 } : Var Ecc.MulFixed.Short.Inputs Fp))
    = { magnitude := eval (⟨place, env⟩ : Placed Environment Fp) (c1 : Var field Fp),
        sign := eval (⟨place, env⟩ : Placed Environment Fp) (c2 : Var field Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval]
  with_unfolding_all rfl

private theorem dnInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c1 c2 c3 : AssignedCell Fp) (p : Point (AssignedCell Fp)) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ({ nk := c1, rho := c2, psi := c3, cm := p } : Var DeriveNullifier.Input Fp))
    = { nk := eval (⟨place, env⟩ : Placed Environment Fp) (c1 : Var field Fp),
        rho := eval (⟨place, env⟩ : Placed Environment Fp) (c2 : Var field Fp),
        psi := eval (⟨place, env⟩ : Placed Environment Fp) (c3 : Var field Fp),
        cm := eval (⟨place, env⟩ : Placed Environment Fp) (p : Var Point Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval]
  with_unfolding_all rfl

private theorem saInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (p : Point (AssignedCell Fp)) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ({ akP := p } : Var SpendAuthority.Input Fp))
    = { akP := eval (⟨place, env⟩ : Placed Environment Fp) (p : Var Point Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval]
  with_unfolding_all rfl

private theorem civkInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c1 c2 : AssignedCell Fp) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ({ ak := c1, nk := c2 } : Var CommitIvk.Main.Inputs Fp))
    = { ak := eval (⟨place, env⟩ : Placed Environment Fp) (c1 : Var field Fp),
        nk := eval (⟨place, env⟩ : Placed Environment Fp) (c2 : Var field Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval]
  with_unfolding_all rfl

private theorem aiInputs_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c1 : AssignedCell Fp) (p : Point (AssignedCell Fp)) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ({ ivk := c1, gDOld := p } : Var AddressIntegrity.Input Fp))
    = { ivk := eval (⟨place, env⟩ : Placed Environment Fp) (c1 : Var field Fp),
        gDOld := eval (⟨place, env⟩ : Placed Environment Fp) (p : Var Point Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval]
  with_unfolding_all rfl

private theorem layerInput_eval_eq (place : RegionIndex → ℕ) (env : Environment Fp)
    (c : AssignedCell Fp) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
      ({ node := c } : Var Sinsemilla.Merkle.Layer.Input Fp))
    = { node := eval (⟨place, env⟩ : Placed Environment Fp) (c : Var field Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval]
  with_unfolding_all rfl

private theorem vcInputs_eval_eq_prover (place : RegionIndex → ℕ)
    (env : ProverEnvironment Fp) (c1 c2 : AssignedCell Fp) :
    (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
      ({ magnitude := c1, sign := c2 } : Var Ecc.MulFixed.Short.Inputs Fp))
    = { magnitude := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (c1 : Var field Fp),
        sign := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (c2 : Var field Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval_prover]
  with_unfolding_all rfl

private theorem civkInputs_eval_eq_prover (place : RegionIndex → ℕ)
    (env : ProverEnvironment Fp) (c1 c2 : AssignedCell Fp) :
    (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
      ({ ak := c1, nk := c2 } : Var CommitIvk.Main.Inputs Fp))
    = { ak := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c1 : Var field Fp),
        nk := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (c2 : Var field Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval_prover]
  with_unfolding_all rfl

private theorem dn_assumptions_eq (K : FixedBase) :
    (DeriveNullifier.circuit K).Assumptions
      = fun (input : Value DeriveNullifier.Input Fp) =>
          Orchard.Point.Valid input.cm := rfl

private theorem sa_assumptions_eq (G : FixedBase) (w : Vector (FExpr Fp) 85) :
    (SpendAuthority.circuit G w).Assumptions
      = fun (input : Value SpendAuthority.Input Fp) =>
          Orchard.Point.Valid input.akP := rfl

private theorem ai_assumptions_eq (pkD : Point (FExpr Fp)) :
    (AddressIntegrity.circuit pkD).Assumptions
      = fun (input : Value AddressIntegrity.Input Fp) =>
          Orchard.Point.OnCurve input.gDOld := rfl

private theorem ai_pa_eq (pkD : Point (FExpr Fp)) :
    (AddressIntegrity.circuit pkD).ProverAssumptions
      = fun (input : ProverValue AddressIntegrity.Input Fp) (wit : Point Fp) _ =>
          wit.OnCurve ∧ wit = (input.ivk.val • input.gDOld : Point Fp) := rfl

private theorem aiInputs_eval_eq_prover (place : RegionIndex → ℕ)
    (env : ProverEnvironment Fp) (c1 : AssignedCell Fp) (p : Point (AssignedCell Fp)) :
    (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
      ({ ivk := c1, gDOld := p } : Var AddressIntegrity.Input Fp))
    = { ivk := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c1 : Var field Fp),
        gDOld := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (p : Var Point Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval_prover]
  with_unfolding_all rfl

private theorem vc_pa_eq (V : Orchard.Ecc.MulFixed.Short.FixedBase) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) :
    (ValueCommit.circuit V R w).ProverAssumptions
      = fun (input : ProverValue Ecc.MulFixed.Short.Inputs Fp)
          (wit : Vector Fp 85 × Fq) _ =>
          input.magnitude.val < 2 ^ 64 ∧ (input.sign = 1 ∨ input.sign = -1) ∧
          ∀ w : Fin 85, (wit.1[w.val]).val < 8 := rfl

private theorem civk_pa_eq (G : Generators) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) :
    (CommitIvk.Main.circuit G R w Q hQ).ProverAssumptions
      = CommitIvk.Main.ProverAssumptions G Q := rfl

private theorem nc_pa_eq (G : Generators) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve) :
    (NoteCommit.Main.circuit G R w Q hQ).ProverAssumptions
      = NoteCommit.Main.ProverAssumptions G Q := rfl

private theorem ncInputs_eval_eq_prover (place : RegionIndex → ℕ)
    (env : ProverEnvironment Fp) (c1 c2 c3 c4 c5 c6 c7 : AssignedCell Fp) :
    (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
      ({ gdX := c1, gdY := c2, pkdX := c3, pkdY := c4, value := c5, rho := c6,
         psi := c7 } : Var NoteCommit.Main.Inputs Fp))
    = { gdX := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c1 : Var field Fp),
        gdY := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c2 : Var field Fp),
        pkdX := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c3 : Var field Fp),
        pkdY := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c4 : Var field Fp),
        value := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c5 : Var field Fp),
        rho := eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (c6 : Var field Fp),
        psi := eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (c7 : Var field Fp) } := by
  rw [ProvableStruct.eval_cells_eq_eval_prover]
  with_unfolding_all rfl

private theorem nc_extract_eq (G : Generators) (R : FixedBase)
    (w : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : NoteCommit.Main.Config) (inp : Var NoteCommit.Main.Inputs Fp)
    (i : RegionIndex) (env : Placed Environment Fp) :
    (NoteCommit.Main.circuit G R w Q hQ).extract c inp i env
      = Ecc.MulFixed.FullWidth.fwExtract c.mulConfig (i + 25) env := rfl

/-! ## Stage outputs and offsets -/

private theorem nextRegionIndex_constrainInstance (cell : AssignedCell Fp)
    (col : Column .instance) (row : ℕ) (i : RegionIndex) :
    (constrainInstance cell col row).nextRegionIndex i = i := rfl

theorem synthWitness_nextRegionIndex (G : Generators) (W : Witnesses) (cfg : Config)
    (i : RegionIndex) :
    (synthWitness G W cfg).nextRegionIndex i = i + 8 := by
  with_unfolding_all rfl

theorem synthWitness_output (G : Generators) (W : Witnesses) (cfg : Config)
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
  with_unfolding_all rfl

theorem synthChecks_nextRegionIndex (G : Generators) (B : Bases) (W : Witnesses)
    (cfg : Config) (wc : WitnessCells) (i : RegionIndex) :
    (synthChecks G B W cfg wc).nextRegionIndex i = i + 295 := by
  with_unfolding_all rfl

theorem synthChecks_output (G : Generators) (B : Bases) (W : Witnesses)
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
  with_unfolding_all rfl

/-! ## Soundness -/

open Halo2.Ironwood.Sinsemilla.Merkle (MerkleRoot)

set_option maxRecDepth 8192 in
theorem soundness (G : Generators) (B : Bases) (W : Witnesses) (cfg : Config) :
    FormalCircuit.Soundness (Witness := fun _ => ActionData)
      (main G B W cfg) (extract cfg) (EnvAssumptions G cfg) (fun _ => True)
      (Spec G B) := by
  circuit_proof_start
  obtain ⟨hTE, hT1, hT2, hTM1, hTM2, hFw, hSh, hBf, hMulE, hTL, hDist⟩ := _hE
  simp only [main, CircuitPreIronwood.synthesize, circuit_norm] at hc
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
  rw [wpoint_call_regionCount] at hGd hAk
  rw [wpointNonId_call_regionCount] at hAk
  simp only [Nat.add_assoc, Nat.reduceAdd] at hGd hAk
  subcircuit_rw at hCm
  subcircuit_rw at hGd
  subcircuit_rw at hAk
  have hCmS := hCm (by rw [wpoint_envAssumptions_eq]; trivial)
    (by rw [wpoint_assumptions_eq]; trivial)
  rw [wpoint_spec_eq, wpoint_output] at hCmS
  have hGdS := hGd (by rw [wpointNonId_envAssumptions_eq]; trivial)
    (by rw [wpointNonId_assumptions_eq]; trivial)
  rw [wpointNonId_spec_eq, wpointNonId_output] at hGdS
  have hAkS := hAk (by rw [wpointNonId_envAssumptions_eq]; trivial)
    (by rw [wpointNonId_assumptions_eq]; trivial)
  rw [wpointNonId_spec_eq, wpointNonId_output] at hAkS
  clear hCm hGd hAk
  simp only [Point.eval_eq, circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
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
  try rw [merkle_call_regionCount] at hM2
  try rw [merkle_call_regionCount] at hM2
  try rw [vc_call_regionCount] at hM2
  try rw [dn_call_regionCount] at hM2
  try rw [sa_call_regionCount] at hM2
  try rw [civk_call_regionCount] at hM2
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hM2
  try rw [merkle_call_regionCount] at hVC
  try rw [merkle_call_regionCount] at hVC
  try rw [vc_call_regionCount] at hVC
  try rw [dn_call_regionCount] at hVC
  try rw [sa_call_regionCount] at hVC
  try rw [civk_call_regionCount] at hVC
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hVC
  try rw [merkle_call_regionCount] at hIcvx
  try rw [merkle_call_regionCount] at hIcvx
  try rw [vc_call_regionCount] at hIcvx
  try rw [dn_call_regionCount] at hIcvx
  try rw [sa_call_regionCount] at hIcvx
  try rw [civk_call_regionCount] at hIcvx
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hIcvx
  try rw [merkle_call_regionCount] at hIcvy
  try rw [merkle_call_regionCount] at hIcvy
  try rw [vc_call_regionCount] at hIcvy
  try rw [dn_call_regionCount] at hIcvy
  try rw [sa_call_regionCount] at hIcvy
  try rw [civk_call_regionCount] at hIcvy
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hIcvy
  try rw [merkle_call_regionCount] at hDN
  try rw [merkle_call_regionCount] at hDN
  try rw [vc_call_regionCount] at hDN
  try rw [dn_call_regionCount] at hDN
  try rw [sa_call_regionCount] at hDN
  try rw [civk_call_regionCount] at hDN
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hDN
  try rw [merkle_call_regionCount] at hInf
  try rw [merkle_call_regionCount] at hInf
  try rw [vc_call_regionCount] at hInf
  try rw [dn_call_regionCount] at hInf
  try rw [sa_call_regionCount] at hInf
  try rw [civk_call_regionCount] at hInf
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hInf
  try rw [merkle_call_regionCount] at hSA
  try rw [merkle_call_regionCount] at hSA
  try rw [vc_call_regionCount] at hSA
  try rw [dn_call_regionCount] at hSA
  try rw [sa_call_regionCount] at hSA
  try rw [civk_call_regionCount] at hSA
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hSA
  try rw [merkle_call_regionCount] at hIrkx
  try rw [merkle_call_regionCount] at hIrkx
  try rw [vc_call_regionCount] at hIrkx
  try rw [dn_call_regionCount] at hIrkx
  try rw [sa_call_regionCount] at hIrkx
  try rw [civk_call_regionCount] at hIrkx
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hIrkx
  try rw [merkle_call_regionCount] at hIrky
  try rw [merkle_call_regionCount] at hIrky
  try rw [vc_call_regionCount] at hIrky
  try rw [dn_call_regionCount] at hIrky
  try rw [sa_call_regionCount] at hIrky
  try rw [civk_call_regionCount] at hIrky
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hIrky
  try rw [merkle_call_regionCount] at hCI
  try rw [merkle_call_regionCount] at hCI
  try rw [vc_call_regionCount] at hCI
  try rw [dn_call_regionCount] at hCI
  try rw [sa_call_regionCount] at hCI
  try rw [civk_call_regionCount] at hCI
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hCI
  try rw [merkle_call_regionCount] at hAI
  try rw [merkle_call_regionCount] at hAI
  try rw [vc_call_regionCount] at hAI
  try rw [dn_call_regionCount] at hAI
  try rw [sa_call_regionCount] at hAI
  try rw [civk_call_regionCount] at hAI
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hAI
  subcircuit_rw at hM1
  subcircuit_rw at hM2
  subcircuit_rw at hVC
  subcircuit_rw at hDN
  subcircuit_rw at hSA
  subcircuit_rw at hCI
  subcircuit_rw at hAI
  have hM1S := hM1 (by rw [merkle_envAssumptions_eq]; exact ⟨hTM1, hTL, hDist⟩)
    (by rw [merkle_assumptions_eq]; trivial)
  rw [merkle_spec_eq] at hM1S
  rw [layerInput_eval_eq] at hM1S
  have hM2S := hM2 (by rw [merkle_envAssumptions_eq]; exact ⟨hTM2, hTL, hDist⟩)
    (by rw [merkle_assumptions_eq]; trivial)
  rw [merkle_spec_eq] at hM2S
  try rw [layerInput_eval_eq] at hM2S
  have hVCS := hVC (by exact ⟨hSh, hFw⟩) (by trivial)
  rw [vc_spec_eq, vc_extract_eq] at hVCS
  rw [vcInputs_eval_eq] at hVCS
  have hDNS := hDN (by exact hBf) (by
    show Orchard.Point.Valid _
    simp only [circuit_norm, Point.eval_eq]
    exact hCmS)
  rw [dn_spec_eq] at hDNS
  rw [dnInputs_eval_eq] at hDNS
  have hSAS := hSA (by exact hFw) (by
    show Orchard.Point.Valid _
    simp only [circuit_norm, Point.eval_eq]
    exact Or.inl hAkS)
  rw [sa_spec_eq, sa_extract_eq] at hSAS
  rw [saInputs_eval_eq] at hSAS
  have hCIS := hCI (by exact ⟨hT1, hFw, hTL, hDist⟩) (by trivial)
  rw [civk_spec_eq, civk_extract_eq] at hCIS
  simp only [CommitIvk.Main.Spec] at hCIS
  rw [civkInputs_eval_eq] at hCIS
  have hAIS := hAI (by exact hMulE) (by
    show Orchard.Point.OnCurve _
    simp only [circuit_norm, Point.eval_eq]
    exact hGdS)
  rw [ai_spec_eq, ai_output] at hAIS
  rw [aiInputs_eval_eq] at hAIS
  simp only [Point.eval_eq, circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice, Nat.add_zero,
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
  try rw [nc_call_regionCount] at hEqR
  try rw [wpointNonId_call_regionCount] at hEqR
  try rw [wpointNonId_call_regionCount] at hEqR
  try rw [nc_call_regionCount] at hEqR
  try rw [nc_call_regionCount] at hGdN
  try rw [wpointNonId_call_regionCount] at hGdN
  try rw [wpointNonId_call_regionCount] at hGdN
  try rw [nc_call_regionCount] at hGdN
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hGdN
  try rw [nc_call_regionCount] at hPkN
  try rw [wpointNonId_call_regionCount] at hPkN
  try rw [wpointNonId_call_regionCount] at hPkN
  try rw [nc_call_regionCount] at hPkN
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hPkN
  try rw [nc_call_regionCount] at hNCn
  try rw [wpointNonId_call_regionCount] at hNCn
  try rw [wpointNonId_call_regionCount] at hNCn
  try rw [nc_call_regionCount] at hNCn
  try simp only [Nat.add_assoc, Nat.reduceAdd] at hNCn
  try rw [nc_call_regionCount] at hIcmx
  try rw [wpointNonId_call_regionCount] at hIcmx
  try rw [wpointNonId_call_regionCount] at hIcmx
  try rw [nc_call_regionCount] at hIcmx
  try simp only [circuit_norm, Nat.add_assoc, Nat.reduceAdd] at hIcmx
  try rw [nc_call_regionCount] at hOrch
  try rw [wpointNonId_call_regionCount] at hOrch
  try rw [wpointNonId_call_regionCount] at hOrch
  try rw [nc_call_regionCount] at hOrch
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
    (by rw [nc_assumptions_eq, ncInputs_eval_eq]
        refine ⟨?_, ?_⟩
        · show Orchard.Point.OnCurve _
          with_unfolding_all exact hGdS
        · show Orchard.Point.OnCurve _
          with_unfolding_all exact hAIS.1)
  rw [nc_spec_eq, nc_extract_eq] at hNCoS
  simp only [NoteCommit.Main.Spec] at hNCoS
  rw [ncInputs_eval_eq] at hNCoS
  have hGdNS := hGdN (by rw [wpointNonId_envAssumptions_eq]; trivial)
    (by rw [wpointNonId_assumptions_eq]; trivial)
  rw [wpointNonId_spec_eq, wpointNonId_output] at hGdNS
  have hPkNS := hPkN (by rw [wpointNonId_envAssumptions_eq]; trivial)
    (by rw [wpointNonId_assumptions_eq]; trivial)
  rw [wpointNonId_spec_eq, wpointNonId_output] at hPkNS
  have hNCnS := hNCn (by exact ⟨hT2, hFw, hTL, hDist⟩)
    (by rw [nc_assumptions_eq, ncInputs_eval_eq]
        refine ⟨?_, ?_⟩
        · show Orchard.Point.OnCurve _
          with_unfolding_all exact hGdNS
        · show Orchard.Point.OnCurve _
          with_unfolding_all exact hPkNS)
  rw [nc_spec_eq, nc_extract_eq] at hNCnS
  simp only [NoteCommit.Main.Spec] at hNCnS
  rw [ncInputs_eval_eq] at hNCnS
  clear hNCo hGdN hPkN hNCn
  simp only [Point.eval_eq, circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_zero] at hGdNS hPkNS
  -- the "constrain equal" region: derived cm_old = witnessed cm_old
  try simp only [circuit_norm] at hEqR
  try simp only [circuit_norm] at hOrch
  -- ── assemble the statement ──
  simp only [Spec, extract, cellRead, circuit_norm, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
    Nat.add_zero, Nat.add_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · with_unfolding_all exact hCmS
  · with_unfolding_all exact hGdS
  · with_unfolding_all exact hAkS
  · with_unfolding_all exact hAIS.1
  · with_unfolding_all exact hGdNS
  · with_unfolding_all exact hPkNS
  · -- value-commitment integrity
    obtain ⟨m, hm, hmag, hdisj⟩ := hVCS
    have hP : ({ x := env.inst cfg.primary ((CV_NET_X : ℕ) : ℤ),
                 y := env.inst cfg.primary ((CV_NET_Y : ℕ) : ℤ) } : Point Fp)
        = eval (⟨place, env⟩ : Placed Environment Fp)
            ((ValueCommit.circuit B.valueCommitV B.valueCommitR W.rcvWindows).output
              (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull,
               cfg.eccConfig.add)
              { magnitude := AssignedCell.of (i₀ + 264) 0 (cfg.advices 9),
                sign := AssignedCell.of (i₀ + 265) 0 (cfg.advices 9) }
              (i₀ + 266)) := by
      apply Point.ext_coords
      show (env.inst cfg.primary ((CV_NET_X : ℕ) : ℤ),
            env.inst cfg.primary ((CV_NET_Y : ℕ) : ℤ)) = _
      rw [← hIcvx, ← hIcvy]
      with_unfolding_all rfl
    refine ⟨m, hm, by with_unfolding_all exact hmag, ?_⟩
    rcases hdisj with ⟨hs, he⟩ | ⟨hs, he⟩
    · exact Or.inl ⟨by with_unfolding_all exact hs, by rw [hP]; exact he⟩
    · exact Or.inr ⟨by with_unfolding_all exact hs, by rw [hP]; exact he⟩
  · -- nullifier integrity
    exact hInf.symm.trans (by with_unfolding_all exact hDNS)
  · -- spend authority
    have hP : ({ x := env.inst cfg.primary ((RK_X : ℕ) : ℤ),
                 y := env.inst cfg.primary ((RK_Y : ℕ) : ℤ) } : Point Fp)
        = eval (⟨place, env⟩ : Placed Environment Fp)
            ((SpendAuthority.circuit B.spendAuthG W.alphaWindows).output
              (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
              { akP := { x := AssignedCell.of (i₀ + 4) 0 cfg.eccConfig.witnessPoint.x,
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
    exact ⟨_, by with_unfolding_all exact hCIS, by with_unfolding_all exact hAIS.2⟩
  · -- old note-commitment integrity
    refine Orchard.Specs.Sinsemilla.SpecOrBreak.mono ?_
      (by with_unfolding_all exact hNCoS)
    intro bp hbp
    have hcmP : ({ x := env.advice cfg.eccConfig.witnessPoint.x ((place (i₀ + 2) : ℕ) : ℤ),
                   y := env.advice cfg.eccConfig.witnessPoint.y ((place (i₀ + 2) : ℕ) : ℤ) }
                : Point Fp)
        = eval (⟨place, env⟩ : Placed Environment Fp)
            ((NoteCommit.Main.circuit G B.noteCommitR W.rcmOldWindows B.noteQ
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
                psi := AssignedCell.of i₀ 0 (cfg.advices 0) }
              (i₀ + 303)) := by
      apply Point.ext_coords
      simp only [Point.coords]
      rw [← hEqR.1, ← hEqR.2]
      with_unfolding_all rfl
    rw [hcmP]
    exact hbp
  · -- new note-commitment integrity
    rw [← hInf]
    refine Orchard.Specs.Sinsemilla.SpecOrBreak.mono ?_
      (by with_unfolding_all exact hNCnS)
    intro bp hbp
    rw [← hIcmx]
    with_unfolding_all exact congrArg Point.x hbp
  · -- Merkle path validity + the anchor check
    obtain ⟨hOv, hOn, hOm, hOs, hOr, hOa, hOes, hOeo, hGate⟩ := hOrch
    have hRoot := Sinsemilla.Merkle.MerkleRoot.trans G B.merkleQ hM1S hM2S
    simp only [orchardGate, Constraints.withSelector, circuit_norm, List.Forall] at hGate
    have h := hGate.2.1
    rw [hOv, hOr, hOa] at h
    exact ⟨_, by with_unfolding_all exact hRoot, by with_unfolding_all exact h⟩
  · -- `v_old − v_new = magnitude · sign`
    obtain ⟨hOv, hOn, hOm, hOs, hOr, hOa, hOes, hOeo, hGate⟩ := hOrch
    simp only [orchardGate, Constraints.withSelector, circuit_norm, List.Forall] at hGate
    have h := hGate.1
    rw [hOv, hOn, hOm, hOs] at h
    linear_combination h
  · -- the enable-flag checks
    obtain ⟨hOv, hOn, hOm, hOs, hOr, hOa, hOes, hOeo, hGate⟩ := hOrch
    simp only [orchardGate, Constraints.withSelector, circuit_norm, List.Forall] at hGate
    refine ⟨?_, ?_⟩
    · have h := hGate.2.2.1
      rw [hOv, hOes] at h
      linear_combination h
    · have h := hGate.2.2.2
      rw [hOn, hOeo] at h
      linear_combination h

open Sinsemilla.Merkle.CalculateRoot (pathNode) in
/-- Honest-prover preconditions: well-formed witness points, 3-bit windows for the five
fixed-base scalars, a fully-defined Merkle path, defined Sinsemilla hashes for the three
commitment legs (with the honest commitment equations for the copies/instance rows),
and the `q_orchard` value checks at the honest values. -/
def ProverAssumptions (G : Generators) (B : Bases)
    (_ : ProverValue unit Fp) (wit : ActionData) (_ : ProverHint Fp) : Prop :=
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
    wit.anchor = root ∧
    wit.vOld * (root - wit.anchor) = 0) ∧
  -- the three Sinsemilla legs are defined, with the honest commitment equations
  (∃ Bi, hashToPoint G.S B.ivkQ
      (commitIvkChunks wit.akP.x.val wit.nk.val) = some Bi ∧
    wit.pkdOld = (((Bi + (wit.rivk.2 • B.commitIvkR : Point Fp)).x).val
      • wit.gdOld : Point Fp)) ∧
  (∃ Bo, hashToPoint G.S B.noteQ
      (Orchard.Action.NoteCommit.noteScalars wit.gdOld wit.pkdOld wit.vOld
        wit.rhoOld wit.psiOld).chunks = some Bo ∧
    wit.cmOld = Bo + (wit.rcmOld.2 • B.noteCommitR : Point Fp)) ∧
  (∃ Bn, hashToPoint G.S B.noteQ
      (Orchard.Action.NoteCommit.noteScalars wit.gdNew wit.pkdNew wit.vNew
        wit.nfOld wit.psiNew).chunks = some Bn ∧
    wit.cmx = (Bn + (wit.rcmNew.2 • B.noteCommitR : Point Fp)).x) ∧
  -- the public-input rows are the honestly computed values
  ((wit.sign = 1 →
      (⟨wit.cvX, wit.cvY⟩ : Point Fp)
        = ((wit.magnitude.val : Fq) • B.valueCommitV : Point Fp)
          + (wit.rcv.2 • B.valueCommitR : Point Fp)) ∧
   (wit.sign = -1 →
      (⟨wit.cvX, wit.cvY⟩ : Point Fp)
        = (((-(wit.magnitude.val : Fq)) : Fq) • B.valueCommitV : Point Fp)
          + (wit.rcv.2 • B.valueCommitR : Point Fp))) ∧
  wit.nfOld = ((wit.cmOld +
    ((Orchard.Poseidon.Hash.ConstantLength.value #v[wit.nk, wit.rhoOld]
      + wit.psiOld).val : Fq) • B.nullifierK : Point Fp)).x ∧
  (⟨wit.rkX, wit.rkY⟩ : Point Fp)
    = (wit.alpha.2 • B.spendAuthG : Point Fp) + wit.akP ∧
  -- the remaining `q_orchard` value checks at the honest values
  wit.vOld - wit.vNew = wit.magnitude * wit.sign ∧
  wit.vOld * (1 - wit.enableSpend) = 0 ∧
  wit.vNew * (1 - wit.enableOutput) = 0

/-! ## Completeness -/

private theorem toFormal_call_witnesses {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) (cfg : Cfg)
    (inp : Var In Fp) (i : RegionIndex) (place : RegionIndex → ℕ)
    (env : ProverEnvironment Fp) :
    ExtendsWitnesses place env (((b.toFormal name).call cfg inp).operations i) i
      = RegionOperations.ExtendsWitnesses place i env
          ((b.synthesize cfg 0 inp).operations i) := by
  simp only [FormalRegionCircuit.toFormal, FormalCircuit.call, Circuit.operations,
    assignRegion, ExtendsWitnesses, and_true]
  rfl

private theorem wpoint_call_witnesses (name : String)
    (c : Ecc.WitnessPoint.Config) (inp : Point (FExpr Fp)) (i : RegionIndex)
    (place : RegionIndex → ℕ) (env : ProverEnvironment Fp) :
    ExtendsWitnesses place env
      (((Ecc.WitnessPoint.point.toFormal name).call c inp).operations i) i
      = RegionOperations.ExtendsWitnesses place i env
          ((Ecc.WitnessPoint.point.synthesize c 0 inp).operations i) := by
  simp only [FormalRegionCircuit.toFormal, FormalCircuit.call, Circuit.operations,
    assignRegion, ExtendsWitnesses, and_true]
  rfl

private theorem wpointNonId_call_witnesses (name : String)
    (c : Ecc.WitnessPoint.Config) (inp : Point (FExpr Fp)) (i : RegionIndex)
    (place : RegionIndex → ℕ) (env : ProverEnvironment Fp) :
    ExtendsWitnesses place env
      (((Ecc.WitnessPoint.pointNonId.toFormal name).call c inp).operations i) i
      = RegionOperations.ExtendsWitnesses place i env
          ((Ecc.WitnessPoint.pointNonId.synthesize c 0 inp).operations i) := by
  simp only [FormalRegionCircuit.toFormal, FormalCircuit.call, Circuit.operations,
    assignRegion, ExtendsWitnesses, and_true]
  rfl

private theorem buildWitness (G : Generators) (W : Witnesses) (cfg : Config)
    (i₀ : RegionIndex) (place : RegionIndex → ℕ) (env : Environment Fp)
    (hT : Halo2.Constraints place env
      ((Sinsemilla.load G cfg.sinsemilla1.generatorTable).operations i₀) i₀)
    (h1 : Constraints place env
      (((Ecc.WitnessPoint.point.toFormal "witness point").call
        cfg.eccConfig.witnessPoint W.cmOld).operations (i₀ + 2)) (i₀ + 2))
    (h2 : Constraints place env
      (((Ecc.WitnessPoint.pointNonId.toFormal "witness non-identity point").call
        cfg.eccConfig.witnessPoint W.gdOld).operations (i₀ + 3)) (i₀ + 3))
    (h3 : Constraints place env
      (((Ecc.WitnessPoint.pointNonId.toFormal "witness non-identity point").call
        cfg.eccConfig.witnessPoint W.akP).operations (i₀ + 4)) (i₀ + 4)) :
    Constraints place env ((synthWitness G W cfg).operations i₀) i₀ := by
  simp only [Sinsemilla.load, circuit_norm] at hT
  simp only [synthWitness, loadPrivate, Sinsemilla.load, circuit_norm,
    Nat.add_assoc, Nat.reduceAdd]
  rw [wpoint_call_regionCount, wpointNonId_call_regionCount]
  simp only [Nat.reduceAdd]
  exact ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.1, hT.2.2.2.2.1, hT.2.2.2.2.2,
    h1, h2, h3⟩

set_option maxRecDepth 8192 in
theorem completeness (G : Generators) (B : Bases) (W : Witnesses) (cfg : Config) :
    FormalCircuit.Completeness (Witness := fun _ => ActionData)
      (main G B W cfg) (extract cfg) (EnvAssumptions G cfg) (fun _ => True)
      (ProverAssumptions G B) (fun _ _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨hTE, hT1, hT2, hTM1, hTM2, hFw, hSh, hBf, hMulE, hTL, hDist⟩ := _hE
  obtain ⟨hVcm, hVgd, hVak, hVpk, hVgdn, hVpkn, hWrcv, hWal, hWri, hWro, hWrn,
    hMag, hSign, hV64o, hV64n, ⟨mid, hMid, root, hRootP, hAnch, hVanch⟩,
    ⟨Bi, hBi, hPkd⟩, ⟨Bo, hBo, hCmo⟩, ⟨Bn, hBn, hCmx⟩,
    ⟨hCv1, hCv2⟩, hNf, hRk, hVms, hVes, hVeo⟩ := hPA
  simp only [main, CircuitPreIronwood.synthesize, circuit_norm] at hwit ⊢
  have hWw := hwit.1
  have hWc := hwit.2.1
  have hWn := hwit.2.2
  clear hwit
  -- ── stage A witnesses: the shared cells are the programs' honest values ──
  simp only [synthWitness, loadPrivate, Sinsemilla.load, circuit_norm] at hWw
  obtain ⟨-, -, -, -, -, -, hwPsi, hwRho, hWcm, hWgd, hWak, hwNk, hwVo, hwVn⟩ := hWw
  rw [wpoint_call_regionCount] at hWgd hWak
  rw [wpointNonId_call_regionCount] at hWak
  simp only [Nat.add_assoc, Nat.reduceAdd] at hWgd hWak
  have hWcmE := hWcm
  have hWgdE := hWgd
  have hWakE := hWak
  rw [wpoint_call_witnesses] at hWcmE
  rw [wpointNonId_call_witnesses] at hWgdE hWakE
  simp only [Ecc.WitnessPoint.point, Ecc.WitnessPoint.pointNonId,
    circuit_norm] at hWcmE hWgdE hWakE
  refine ⟨buildWitness G W cfg i₀ place _
    (generatorTableExact_constraints G _ _ hTE place i₀) ?_ ?_ ?_, ?_⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (Ecc.WitnessPoint.point.toFormal "witness point")
      cfg.eccConfig.witnessPoint (i₀ + 2) place env _ hWcm
      ⟨(by rw [wpoint_envAssumptions_eq]; trivial),
       (by rw [wpoint_assumptions_eq]; trivial),
       (by rw [wpoint_proverAssumptions_eq]
           show Orchard.Point.Valid _
           have h : Orchard.Point.Valid
               (⟨(Witgen.FExprOver.eval
                   { env := (⟨place, env⟩ : Placed ProverEnvironment Fp) }
                   W.cmOld.x : Fp),
                 (Witgen.FExprOver.eval
                   { env := (⟨place, env⟩ : Placed ProverEnvironment Fp) }
                   W.cmOld.y : Fp)⟩ : Point Fp) := by
             rw [← hWcmE.1, ← hWcmE.2]
             with_unfolding_all exact hVcm
           with_unfolding_all exact h)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (Ecc.WitnessPoint.pointNonId.toFormal "witness non-identity point")
      cfg.eccConfig.witnessPoint (i₀ + 3) place env _ hWgd
      ⟨(by rw [wpointNonId_envAssumptions_eq]; trivial),
       (by rw [wpointNonId_assumptions_eq]; trivial),
       (by rw [wpointNonId_proverAssumptions_eq]
           show Orchard.Point.OnCurve _
           with_unfolding_all exact hVgd)⟩
  · exact Halo2.SubcircuitRw.layouter_completeness_leaf
      (Ecc.WitnessPoint.pointNonId.toFormal "witness non-identity point")
      cfg.eccConfig.witnessPoint (i₀ + 4) place env _ hWak
      ⟨(by rw [wpointNonId_envAssumptions_eq]; trivial),
       (by rw [wpointNonId_assumptions_eq]; trivial),
       (by rw [wpointNonId_proverAssumptions_eq]
           show Orchard.Point.OnCurve _
           with_unfolding_all exact hVak)⟩
  · -- ── stages B and C ──
    simp only [synthWitness_output, synthWitness_nextRegionIndex,
      synthWitness_regionCount, Nat.add_assoc] at hWc hWn
    simp only [synthChecks, loadPrivate, circuit_norm] at hWc
    obtain ⟨hWm1, hWm2, hwMag, hwSign, hWvc, hWdn, hWsa, hWci, hWai⟩ := hWc
    -- offset-normalize the stage-B witness chunks
    rw [merkle_call_regionCount] at hWm2 hWvc hWdn hWsa hWci hWai
    rw [merkle_call_regionCount] at hWvc hWdn hWsa hWci hWai
    rw [vc_call_regionCount] at hWdn hWsa hWci hWai
    rw [dn_call_regionCount] at hWsa hWci hWai
    rw [sa_call_regionCount] at hWci hWai
    rw [civk_call_regionCount] at hWai
    simp only [Nat.add_assoc, Nat.reduceAdd] at hWm2 hWvc hWdn hWsa hWci hWai
    -- ── the fold contracts: honest mid/root landings ──
    have hM1der := Halo2.SubcircuitRw.layouter_completeness_derived
      (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
        0 16 (by norm_num) W.merkleSib W.merkleSwap)
      (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig) (i₀ + 8) place env _ hWm1
      (by rw [merkle_envAssumptions_eq]; exact ⟨hTM1, hTL, hDist⟩)
      (by rw [merkle_assumptions_eq]; trivial)
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
          0 16 (by norm_num) W.merkleSib W.merkleSwap).output
          (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig)
          { node := AssignedCell.of (i₀ + 2) 0 cfg.eccConfig.witnessPoint.x }
          (i₀ + 8)) : Fp) = mid := by
      refine hM1der.2 mid ?_
      rw [show ((Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
          0 16 (by norm_num) W.merkleSib W.merkleSwap).extract
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
          try with_unfolding_all rfl)]
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
        16 16 (by norm_num) (fun i => W.merkleSib (16 + i))
        (fun i => W.merkleSwap (16 + i)))
      (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig) (i₀ + 136) place env _
      hWm2
      (by rw [merkle_envAssumptions_eq]; exact ⟨hTM2, hTL, hDist⟩)
      (by rw [merkle_assumptions_eq]; trivial)
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
          16 16 (by norm_num) (fun i => W.merkleSib (16 + i))
          (fun i => W.merkleSwap (16 + i))).output
          (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig)
          { node := (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ
              B.merkleQ_onCurve 0 16 (by norm_num) W.merkleSib W.merkleSwap).output
              (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig)
              { node := AssignedCell.of (i₀ + 2) 0 cfg.eccConfig.witnessPoint.x }
              (i₀ + 8) }
          (i₀ + 136)) : Fp) = root := by
      refine hM2der.2 root ?_
      rw [show ((Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
          16 16 (by norm_num) (fun i => W.merkleSib (16 + i))
          (fun i => W.merkleSwap (16 + i))).extract
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
      (ValueCommit.circuit B.valueCommitV B.valueCommitR W.rcvWindows)
      (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
      (i₀ + 266) place env _ hWvc (by exact ⟨hSh, hFw⟩) (by trivial)
      (by rw [vc_pa_eq, vcInputs_eval_eq_prover]
          refine ⟨?_, ?_, ?_⟩
          · with_unfolding_all exact hMag
          · with_unfolding_all exact hSign
          · with_unfolding_all exact hWrcv)).1
    have hDNder := (Halo2.SubcircuitRw.layouter_completeness_derived
      (DeriveNullifier.circuit B.nullifierK)
      (cfg.poseidonConfig, cfg.addChipConfig, cfg.eccConfig.mulFixedBaseField,
       cfg.eccConfig.add) (i₀ + 271) place env _ hWdn (by exact hBf)
      (by rw [dn_assumptions_eq, dnInputs_eval_eq]
          show Orchard.Point.Valid _
          simp only [Point.eval_eq]
          with_unfolding_all exact hVcm)
      (by trivial)).1
    have hSAder := (Halo2.SubcircuitRw.layouter_completeness_derived
      (SpendAuthority.circuit B.spendAuthG W.alphaWindows)
      (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add) (i₀ + 280) place env _ hWsa
      (by exact hFw)
      (by rw [sa_assumptions_eq, saInputs_eval_eq]
          show Orchard.Point.Valid _
          simp only [Point.eval_eq]
          with_unfolding_all exact Or.inl hVak)
      (by with_unfolding_all exact hWal)).1
    have hCIder := (Halo2.SubcircuitRw.layouter_completeness_derived
      (CommitIvk.Main.circuit G B.commitIvkR W.rivkWindows B.ivkQ B.ivkQ_onCurve)
      { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
        lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
        addConfig := cfg.eccConfig.add } (i₀ + 283) place env _ hWci
      (by exact ⟨hT1, hFw, hTL, hDist⟩) (by trivial)
      (by rw [civk_pa_eq]
          simp only [CommitIvk.Main.ProverAssumptions]
          rw [civkInputs_eval_eq_prover]
          refine ⟨?_, ?_⟩
          · with_unfolding_all exact hWri
          · refine ⟨Bi, ?_⟩
            with_unfolding_all exact hBi)).1
    -- the ivk output cell carries the honest commitment value
    have hIvkVal : (eval (⟨place, env⟩ : Placed ProverEnvironment Fp)
        ((CommitIvk.Main.circuit G B.commitIvkR W.rivkWindows B.ivkQ
          B.ivkQ_onCurve).output
          { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
            lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add }
          { ak := AssignedCell.of (i₀ + 4) 0 cfg.eccConfig.witnessPoint.x,
            nk := AssignedCell.of (i₀ + 5) 0 (cfg.advices 0) }
          (i₀ + 283)) : Fp)
        = (Bi + ((extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rivk.2
              • B.commitIvkR : Point Fp)).x := by
      rw [civk_spec_eq, civk_extract_eq] at hCIder
      simp only [CommitIvk.Main.Spec] at hCIder
      rw [civkInputs_eval_eq] at hCIder
      simp only [circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex,
        Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
        Nat.add_zero] at hCIder
      rw [Orchard.Specs.Sinsemilla.hashToPointB_inl_of_some
        (show hashToPoint G.S B.ivkQ _ = some Bi from by
          with_unfolding_all exact hBi)] at hCIder
      with_unfolding_all exact hCIder
    -- ── stage C witnesses and contracts ──
    simp only [synthChecks_output, synthChecks_nextRegionIndex,
      synthChecks_regionCount, Nat.add_assoc, Nat.reduceAdd] at hWn
    simp only [synthNotes, loadPrivate, circuit_norm] at hWn
    obtain ⟨hWnco, hWgdn, hWpkn, hwPsiN, hWncn, hWorch⟩ := hWn
    rw [nc_call_regionCount] at hWgdn hWpkn hWncn hWorch
    rw [wpointNonId_call_regionCount] at hWpkn hWncn hWorch
    rw [wpointNonId_call_regionCount] at hWncn hWorch
    rw [nc_call_regionCount] at hWorch
    simp only [Nat.add_assoc, Nat.reduceAdd] at hWgdn hWpkn hWncn hWorch
    have hNCoDer := (Halo2.SubcircuitRw.layouter_completeness_derived
      (NoteCommit.Main.circuit G B.noteCommitR W.rcmOldWindows B.noteQ
        B.noteQ_onCurve)
      { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
        lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
        addConfig := cfg.eccConfig.add } (i₀ + 303) place env _ hWnco
      (by exact ⟨hT1, hFw, hTL, hDist⟩)
      (by rw [nc_assumptions_eq, ncInputs_eval_eq]
          refine ⟨?_, ?_⟩
          · show Orchard.Point.OnCurve _
            with_unfolding_all exact hVgd
          · show Orchard.Point.OnCurve _
            with_unfolding_all exact hVpk)
      (by rw [nc_pa_eq]
          simp only [NoteCommit.Main.ProverAssumptions]
          rw [ncInputs_eval_eq_prover]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · with_unfolding_all exact hVgd
          · with_unfolding_all exact hVpk
          · with_unfolding_all exact hV64o
          · with_unfolding_all exact hWro
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
      rw [dn_spec_eq, dnInputs_eval_eq] at hDNder
      rw [hNf]
      with_unfolding_all exact hDNder
    have hNCnDer := (Halo2.SubcircuitRw.layouter_completeness_derived
      (NoteCommit.Main.circuit G B.noteCommitR W.rcmNewWindows B.noteQ
        B.noteQ_onCurve)
      { gates := cfg.noteCommitNew, hashConfig := cfg.sinsemilla2,
        lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
        addConfig := cfg.eccConfig.add } (i₀ + 350) place env _ hWncn
      (by exact ⟨hT2, hFw, hTL, hDist⟩)
      (by rw [nc_assumptions_eq, ncInputs_eval_eq]
          refine ⟨?_, ?_⟩
          · show Orchard.Point.OnCurve _
            with_unfolding_all exact hVgdn
          · show Orchard.Point.OnCurve _
            with_unfolding_all exact hVpkn)
      (by rw [nc_pa_eq]
          simp only [NoteCommit.Main.ProverAssumptions]
          rw [ncInputs_eval_eq_prover]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · with_unfolding_all exact hVgdn
          · with_unfolding_all exact hVpkn
          · with_unfolding_all exact hV64n
          · with_unfolding_all exact hWrn
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
        ((ValueCommit.circuit B.valueCommitV B.valueCommitR W.rcvWindows).output
          (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull,
           cfg.eccConfig.add)
          { magnitude := AssignedCell.of (i₀ + 264) 0 (cfg.advices 9),
            sign := AssignedCell.of (i₀ + 265) 0 (cfg.advices 9) }
          (i₀ + 266)) : Point Fp)
        = ⟨(extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).cvX,
           (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).cvY⟩ := by
      rw [vc_spec_eq, vc_extract_eq, vcInputs_eval_eq] at hVCder
      obtain ⟨m, hm, hmag, hdisj⟩ := hVCder
      have hmval : (extract cfg input_var i₀
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).magnitude.val = m := by
        rw [show (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).magnitude
          = ((m : ℕ) : Fp) from by with_unfolding_all exact hmag]
        exact ZMod.val_natCast_of_lt (lt_trans hm
          (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))
      rcases hdisj with ⟨hs, he⟩ | ⟨hs, he⟩
      · rw [he]
        have h2 := hCv1 (by with_unfolding_all exact hs)
        rw [hmval] at h2
        with_unfolding_all exact h2.symm
      · rw [he]
        have h2 := hCv2 (by with_unfolding_all exact hs)
        rw [hmval] at h2
        with_unfolding_all exact h2.symm
    have hSAval : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
        ((SpendAuthority.circuit B.spendAuthG W.alphaWindows).output
          (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
          { akP := { x := AssignedCell.of (i₀ + 4) 0 cfg.eccConfig.witnessPoint.x,
                     y := AssignedCell.of (i₀ + 4) 0 cfg.eccConfig.witnessPoint.y } }
          (i₀ + 280)) : Point Fp)
        = ⟨(extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rkX,
           (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rkY⟩ := by
      rw [sa_spec_eq, sa_extract_eq, saInputs_eval_eq] at hSAder
      rw [hSAder]
      rw [show ((⟨(extract cfg input_var i₀
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rkX,
          (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rkY⟩ : Point Fp))
        = ((extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).alpha.2
              • B.spendAuthG : Point Fp)
          + (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).akP from hRk]
      with_unfolding_all rfl
    have hNCoval : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
        ((NoteCommit.Main.circuit G B.noteCommitR W.rcmOldWindows B.noteQ
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
            psi := AssignedCell.of i₀ 0 (cfg.advices 0) }
          (i₀ + 303)) : Point Fp)
        = (extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).cmOld := by
      rw [nc_spec_eq, nc_extract_eq] at hNCoDer
      simp only [NoteCommit.Main.Spec] at hNCoDer
      rw [ncInputs_eval_eq] at hNCoDer
      rw [Orchard.Specs.Sinsemilla.hashToPointB_inl_of_some
        (show hashToPoint G.S B.noteQ _ = some Bo from by
          with_unfolding_all exact hBo)] at hNCoDer
      rw [hCmo]
      with_unfolding_all exact hNCoDer
    have hNCnval : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
        ((NoteCommit.Main.circuit G B.noteCommitR W.rcmNewWindows B.noteQ
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
            psi := AssignedCell.of (i₀ + 349) 0 (cfg.advices 0) }
          (i₀ + 350)) : Point Fp)
        = Bn + ((extract cfg input_var i₀
            (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).rcmNew.2
              • B.noteCommitR : Point Fp) := by
      rw [nc_spec_eq, nc_extract_eq] at hNCnDer
      simp only [NoteCommit.Main.Spec] at hNCnDer
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
      rw [Orchard.Specs.Sinsemilla.hashToPointB_inl_of_some
        (show hashToPoint G.S B.noteQ _ = some Bn from by
          with_unfolding_all exact hBn)] at hNCnDer
      with_unfolding_all exact hNCnDer
    -- ── assemble the stage-B and stage-C constraints ──
    simp only [synthWitness_output, synthWitness_nextRegionIndex,
      synthWitness_regionCount, synthChecks_output, synthChecks_nextRegionIndex,
      synthChecks_regionCount, Nat.add_assoc, Nat.reduceAdd]
    refine ⟨?_, ?_⟩
    · simp only [synthChecks, loadPrivate, circuit_norm, Nat.add_assoc]
      rw [merkle_call_regionCount, merkle_call_regionCount, vc_call_regionCount,
        dn_call_regionCount, sa_call_regionCount, civk_call_regionCount]
      simp only [Nat.reduceAdd]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          _ _ (i₀ + 8) place env _ hWm1
          ⟨(by rw [merkle_envAssumptions_eq]; exact ⟨hTM1, hTL, hDist⟩),
           (by rw [merkle_assumptions_eq]; trivial),
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
          ⟨(by rw [merkle_envAssumptions_eq]; exact ⟨hTM2, hTL, hDist⟩),
           (by rw [merkle_assumptions_eq]; trivial),
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
          (ValueCommit.circuit B.valueCommitV B.valueCommitR W.rcvWindows)
          (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull,
           cfg.eccConfig.add) (i₀ + 266) place env _ hWvc
          ⟨(by exact ⟨hSh, hFw⟩), (by trivial),
           (by rw [vc_pa_eq, vcInputs_eval_eq_prover]
               refine ⟨?_, ?_, ?_⟩
               · with_unfolding_all exact hMag
               · with_unfolding_all exact hSign
               · with_unfolding_all exact hWrcv)⟩
      · with_unfolding_all exact congrArg Point.x hCVval
      · with_unfolding_all exact congrArg Point.y hCVval
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (DeriveNullifier.circuit B.nullifierK)
          (cfg.poseidonConfig, cfg.addChipConfig, cfg.eccConfig.mulFixedBaseField,
           cfg.eccConfig.add) (i₀ + 271) place env _ hWdn
          ⟨(by exact hBf),
           (by rw [dn_assumptions_eq, dnInputs_eval_eq]
               show Orchard.Point.Valid _
               simp only [Point.eval_eq]
               with_unfolding_all exact hVcm),
           (by trivial)⟩
      · with_unfolding_all exact hDNval
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (SpendAuthority.circuit B.spendAuthG W.alphaWindows)
          (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add) (i₀ + 280) place env _ hWsa
          ⟨(by exact hFw),
           (by rw [sa_assumptions_eq, saInputs_eval_eq]
               show Orchard.Point.Valid _
               simp only [Point.eval_eq]
               with_unfolding_all exact Or.inl hVak),
           (by with_unfolding_all exact hWal)⟩
      · with_unfolding_all exact congrArg Point.x hSAval
      · with_unfolding_all exact congrArg Point.y hSAval
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (CommitIvk.Main.circuit G B.commitIvkR W.rivkWindows B.ivkQ
            B.ivkQ_onCurve)
          { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
            lookupConfig := cfg.lookupConfig,
            mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add } (i₀ + 283) place env _ hWci
          ⟨(by exact ⟨hT1, hFw, hTL, hDist⟩), (by trivial),
           (by rw [civk_pa_eq]
               simp only [CommitIvk.Main.ProverAssumptions]
               rw [civkInputs_eval_eq_prover]
               refine ⟨?_, ?_⟩
               · with_unfolding_all exact hWri
               · refine ⟨Bi, ?_⟩
                 with_unfolding_all exact hBi)⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (AddressIntegrity.circuit W.pkDOld)
          (cfg.eccConfig.mul, cfg.eccConfig.witnessPoint) (i₀ + 297) place env _
          hWai
          ⟨(by exact hMulE),
           (by rw [ai_assumptions_eq, aiInputs_eval_eq]
               show Orchard.Point.OnCurve _
               simp only [Point.eval_eq]
               with_unfolding_all exact hVgd),
           (by rw [ai_pa_eq, aiInputs_eval_eq_prover]
               refine ⟨?_, ?_⟩
               · with_unfolding_all exact hVpk
               · have h := hPkd
                 rw [← hIvkVal] at h
                 with_unfolding_all exact h)⟩
    · simp only [synthNotes, loadPrivate, circuit_norm, Nat.add_assoc]
      rw [nc_call_regionCount, wpointNonId_call_regionCount,
        wpointNonId_call_regionCount, nc_call_regionCount]
      simp only [Nat.reduceAdd]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (NoteCommit.Main.circuit G B.noteCommitR W.rcmOldWindows B.noteQ
            B.noteQ_onCurve)
          { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
            lookupConfig := cfg.lookupConfig,
            mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add } (i₀ + 303) place env _ hWnco
          ⟨(by exact ⟨hT1, hFw, hTL, hDist⟩),
           (by rw [nc_assumptions_eq, ncInputs_eval_eq]
               refine ⟨?_, ?_⟩
               · show Orchard.Point.OnCurve _
                 with_unfolding_all exact hVgd
               · show Orchard.Point.OnCurve _
                 with_unfolding_all exact hVpk),
           (by rw [nc_pa_eq]
               simp only [NoteCommit.Main.ProverAssumptions]
               rw [ncInputs_eval_eq_prover]
               refine ⟨?_, ?_, ?_, ?_, ?_⟩
               · with_unfolding_all exact hVgd
               · with_unfolding_all exact hVpk
               · with_unfolding_all exact hV64o
               · with_unfolding_all exact hWro
               · refine ⟨Bo, ?_⟩
                 with_unfolding_all exact hBo)⟩
      · refine ⟨?_, ?_⟩
        · with_unfolding_all exact congrArg Point.x hNCoval
        · with_unfolding_all exact congrArg Point.y hNCoval
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (Ecc.WitnessPoint.pointNonId.toFormal "witness non-identity point")
          cfg.eccConfig.witnessPoint (i₀ + 347) place env _ hWgdn
          ⟨(by rw [wpointNonId_envAssumptions_eq]; trivial),
           (by rw [wpointNonId_assumptions_eq]; trivial),
           (by rw [wpointNonId_proverAssumptions_eq]
               show Orchard.Point.OnCurve _
               with_unfolding_all exact hVgdn)⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (Ecc.WitnessPoint.pointNonId.toFormal "witness non-identity point")
          cfg.eccConfig.witnessPoint (i₀ + 348) place env _ hWpkn
          ⟨(by rw [wpointNonId_envAssumptions_eq]; trivial),
           (by rw [wpointNonId_assumptions_eq]; trivial),
           (by rw [wpointNonId_proverAssumptions_eq]
               show Orchard.Point.OnCurve _
               with_unfolding_all exact hVpkn)⟩
      · exact Halo2.SubcircuitRw.layouter_completeness_leaf
          (NoteCommit.Main.circuit G B.noteCommitR W.rcmNewWindows B.noteQ
            B.noteQ_onCurve)
          { gates := cfg.noteCommitNew, hashConfig := cfg.sinsemilla2,
            lookupConfig := cfg.lookupConfig,
            mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add } (i₀ + 350) place env _ hWncn
          ⟨(by exact ⟨hT2, hFw, hTL, hDist⟩),
           (by rw [nc_assumptions_eq, ncInputs_eval_eq]
               refine ⟨?_, ?_⟩
               · show Orchard.Point.OnCurve _
                 with_unfolding_all exact hVgdn
               · show Orchard.Point.OnCurve _
                 with_unfolding_all exact hVpkn),
           (by rw [nc_pa_eq]
               simp only [NoteCommit.Main.ProverAssumptions]
               rw [ncInputs_eval_eq_prover]
               refine ⟨?_, ?_, ?_, ?_, ?_⟩
               · with_unfolding_all exact hVgdn
               · with_unfolding_all exact hVpkn
               · with_unfolding_all exact hV64n
               · with_unfolding_all exact hWrn
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
                   from by with_unfolding_all exact hDNval]
                 with_unfolding_all exact hBn)⟩
      · with_unfolding_all exact (congrArg Point.x hNCnval).trans hCmx.symm
      · -- the final `"Orchard circuit checks"` region
        simp only [nextRegionIndex_constrainInstance]
        simp only [nextRegionIndex_constrainInstance] at hWorch
        obtain ⟨hOv, hOn, hOm, hOs, hOr, hOa, hOes, hOeo⟩ := hWorch
        have hOr' : env.advice (cfg.advices 4) ((place (i₀ + 393) : ℕ) : ℤ)
            = root := hOr.trans (by with_unfolding_all exact hM2root)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · with_unfolding_all exact hOv
        · with_unfolding_all exact hOn
        · with_unfolding_all exact hOm
        · with_unfolding_all exact hOs
        · with_unfolding_all exact hOr
        · with_unfolding_all exact hOa
        · with_unfolding_all exact hOes
        · with_unfolding_all exact hOeo
        · simp only [orchardGate, Constraints.withSelector, circuit_norm,
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

/-- Rust `impl Circuit for Circuit` (`circuit.rs:271-828`) as a proof-carrying bundle:
the e2e Orchard Action statement (§4.17.4, breaks-as-data) over the extracted
primary-instance rows and witness data. -/
def circuit (G : Generators) (B : Bases) (W : Witnesses) :
    FormalCircuit Fp Unit Config unit unit where
  name := "OrchardAction"
  configure := fun _ => configure G
  synthesize := main G B W
  elaborated := fun cfg => elaborated G B W cfg
  Witness := fun _ => ActionData
  extract := extract
  EnvAssumptions := EnvAssumptions G
  Assumptions := fun _ => True
  Spec := Spec G B
  ProverAssumptions := ProverAssumptions G B
  ProverSpec := fun _ _ _ _ => True
  soundness := soundness G B W
  completeness := completeness G B W

end Halo2.Ironwood.Action.Circuit
