import Clean.Halo2.Tactics.ContractBridges
import Clean.Ironwood.Sinsemilla.HashPieceRound

/-!
The Sinsemilla hash-word loop and the `hash_piece` bundle over the round gadget
(`HashPieceRound.lean`): a piece of `w + 1` words at rows `offset .. offset + w`. The `z_0` piece
copy is the only copy constraint — the entering `x_a` is positional (already assigned at the
offset, not copied) and the entering `y_a` is a pure `Value` thread (`yaIn`, a cell-derivation
program, never a cell).

Reference: `halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`.
-/

namespace Zcash.Circuits.Sinsemilla.HashPiece

open Halo2
open Ecc (DoubleAndAddRow)
open Ecc.DoubleAndAdd (xR yA)
open Specs.Sinsemilla (Generators step hashToPoint)
open Specs (K)
open Sinsemilla
  (GeneratorTableConfig GeneratorTableLoaded pieceWord pieceZ rowValue accAfter nextYA
   pieceWord_lt pieceZ_zero pieceZ_succ pieceZ_last chain_eq_sum piece_recombine
   chain_eq_suffix_sum step_coordinates_of_constraints step_honest accAfter_eq_chain)

/-- Read the assigned cell at a known region-local row/column (no op emitted). Lets
`synthesize` name output cells at fixed rows. (`MulIncomplete.cellAt`.) -/
def cellAt (col : Column .advice) (row : ℕ) : RegionCircuit Fp (AssignedCell Fp) :=
  fun self => (.of self row col, [])

@[circuit_norm]
theorem operations_cellAt (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    (cellAt col row).operations self = [] := rfl

@[circuit_norm]
theorem output_cellAt (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    (cellAt col row).output self = .of self row col := rfl

/-- Name a whole vector of cells at fixed region-local rows (no op emitted).
(`MulIncomplete.cellVec`.) -/
def cellVec (col : Column .advice) (rows : ℕ → ℕ) (len : ℕ) :
    RegionCircuit Fp (Vector (AssignedCell Fp) len) :=
  fun self => (Vector.ofFn (fun i => AssignedCell.of self (rows i) col), [])

@[circuit_norm]
theorem operations_cellVec (col : Column .advice) (rows : ℕ → ℕ) (len : ℕ) (self : RegionIndex) :
    (cellVec col rows len).operations self = [] := rfl

@[circuit_norm]
theorem output_cellVec (col : Column .advice) (rows : ℕ → ℕ) (len : ℕ) (self : RegionIndex) :
    (cellVec col rows len).output self
      = Vector.ofFn (fun i => AssignedCell.of self (rows i) col) := rfl

-- contract bridges for the `round` child (opened by the loop's proofs)
derive_contract_bridges roundC (G : Generators) (i : ℕ) := round G i

/-! ## The iterated honest step -/

/-- The honest state after `r` rounds: round `i` steps with the *next* word's generator
and running sum (the virtual-y quirk — round `i` witnesses row `i+1`'s slopes). -/
def State.iter (s : State Fp) (G : Generators) (p : Fp) : ℕ → State Fp
  | 0 => s
  | r + 1 => (s.iter G p r).step
      ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y) (pieceZ p (r + 1))

/-- Witness equations chain into the iterated step. -/
theorem iter_of_steps (G : Generators) (p : Fp) {n : ℕ} (st : ℕ → State Fp)
    (hstep : ∀ i : Fin n, st (i.val + 1) = (st i.val).step
      ((G.S (pieceWord p (i.val + 1))).x, (G.S (pieceWord p (i.val + 1))).y)
      (pieceZ p (i.val + 1))) :
    ∀ r, r ≤ n → st r = (st 0).iter G p r := by
  intro r hr
  induction r with
  | zero => rfl
  | succ v ih =>
    rw [hstep ⟨v, by omega⟩, ih (by omega)]
    rfl

/-- Honesty chains along the iterated step (via `step_exit`), up to the exit row. -/
theorem iter_honest (G : Generators) {p : Fp} {A B : Point Fp} {n : ℕ} (s0 : State Fp)
    (hH0 : s0.Honest G p A 0)
    (hchain : hashToPoint G.S A ((List.range (n + 1)).map (pieceWord p)) = some B) :
    ∀ r, r ≤ n → (s0.iter G p r).Honest G p A r := by
  intro r hr
  induction r with
  | zero => exact hH0
  | succ v ih =>
    obtain ⟨Cv, hCv⟩ := range_prefix_some G.S A (pieceWord p) hchain
      (show v + 1 ≤ n + 1 by omega)
    exact (step_exit G (ih (by omega)) hCv).1

/-! ## The loop's soundness fold -/

/-- The loop induction over an abstract row family: `n` constrained Sinsemilla steps fold
the accumulator along the spec-level chain, propagating on-curve-ness through the prefix
points. -/
private theorem loop_fold (G : Generators) {n : ℕ} (st : ℕ → State Fp) (ms : ℕ → ℕ)
    (hms : ∀ i : Fin n, ms i.val < 2 ^ K)
    (hstep : ∀ i : Fin n, ∀ A : Point Fp, A.OnCurve → A.x = (st i.val).row.xA →
      2 * A.y = yA (st i.val).row → ∀ B, step G.S (ms i.val) A = some B →
        (st (i.val + 1)).row.xA = B.x ∧ 2 * B.y = yA (st (i.val + 1)).row) :
    ∀ A : Point Fp, A.OnCurve → A.x = (st 0).row.xA → 2 * A.y = yA (st 0).row →
      ∀ B, hashToPoint G.S A ((List.range n).map ms) = some B →
        (st n).row.xA = B.x ∧ 2 * B.y = yA (st n).row := by
  intro A hAon hAx hAyA B hB
  have hAvalid : A.Valid := Or.inl hAon
  have hA0 : A ≠ 0 := Point.ne_zero_of_onCurve hAon
  suffices h : ∀ r, r ≤ n → ∀ C : Point Fp,
      hashToPoint G.S A ((List.range r).map ms) = some C →
      C.OnCurve ∧ (st r).row.xA = C.x ∧ 2 * C.y = yA (st r).row from
    ⟨(h n le_rfl B hB).2.1, (h n le_rfl B hB).2.2⟩
  intro r
  induction r with
  | zero =>
    intro _ C hC
    rw [show ((List.range 0).map ms) = ([] : List ℕ) from rfl,
      Specs.Sinsemilla.hashToPoint_nil] at hC
    obtain rfl : A = C := Option.some.inj hC
    exact ⟨hAon, hAx.symm, hAyA⟩
  | succ v ih =>
    intro hv C hC
    obtain ⟨Cv, hCv⟩ := range_prefix_some G.S A ms hC (show v ≤ v + 1 by omega)
    have hstepv : step G.S (ms v) Cv = some C := prefix_step_some G.S A ms hCv hC
    obtain ⟨hCvOn, hxv, hyv⟩ := ih (by omega) Cv hCv
    have hprefix_lt : ∀ m ∈ (List.range (v + 1)).map ms, m < 2 ^ K := by
      intro m hm
      rcases List.mem_map.mp hm with ⟨j, hj, rfl⟩
      simp only [List.mem_range] at hj
      exact hms ⟨j, by omega⟩
    have hCvalid : C.Valid :=
      Specs.Sinsemilla.hashToPoint_valid hAvalid hprefix_lt hC
    have hC0 : C ≠ 0 :=
      Specs.Sinsemilla.hashToPoint_ne_zero hAvalid hA0 hprefix_lt hC
    have hCOn : C.OnCurve := by
      rcases hCvalid with h | h
      · exact h
      · exact False.elim (hC0 h)
    obtain ⟨hx, hy⟩ := hstep ⟨v, by omega⟩ Cv hCvOn hxv.symm hyv C hstepv
    exact ⟨hCOn, hx, hy⟩

/-! ## The loop bundle -/

/-- The running-word chain: each of the `n` interior words decomposes its running sum,
`z_j = m_j + 2^K · z_{j+1}` (`z_0` the entering sum, `zs` the assigned interior sums). -/
def wordChain {n : ℕ} (zIn : Fp) (zs : Vector Fp n) (ms : ℕ → ℕ) : Prop :=
  ∀ j : Fin n, (if _ : j.val = 0 then zIn else zs[j.val - 1])
    = ((ms j.val : ℕ) : Fp) + 2 ^ K * zs[j.val]

/-- The loop's output: the exit row (the piece's last word row, whose lookup and the
piece-linking gate the composing circuits own) and the `n` interior running sums. -/
structure LoopOut (n : ℕ) (F : Type) where
  exit : State F
  zs : Vector F n
deriving ProvableStruct

/-- The loop’s row family: the word state at each round offset (top-level def — set/let
locals defeat higher-order unification; the MulIncomplete lesson). -/
private def rowFam (cfg : Config) (pl : RegionIndex → ℕ) (e : ProverEnvironment Fp)
    (self : RegionIndex) (offset : ℕ) : ℕ → State Fp := fun r =>
  { z := e.advice cfg.bits ((pl self + (offset + r) : ℕ) : ℤ),
    row := { xA := e.advice cfg.xA ((pl self + (offset + r) : ℕ) : ℤ),
             xP := e.advice cfg.xP ((pl self + (offset + r) : ℕ) : ℤ),
             lambda1 := e.advice cfg.lambda1 ((pl self + (offset + r) : ℕ) : ℤ),
             lambda2 := e.advice cfg.lambda2 ((pl self + (offset + r) : ℕ) : ℤ) } }

def loopSynthesisSummary (n : ℕ) (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .repeatColumnsWithSelectorPattern
    [(cfg.qS1.index, 0), (cfg.qS1.index, 0)]
    (roundColumns cfg) offset 1 2 0 n
    (lookupActivationCount := 1)

@[synthesis_summary_norm]
theorem loopSynthesisSummary_lookupActivationCount
    (n : ℕ) (cfg : Config) (offset : ℕ) :
    (loopSynthesisSummary n cfg offset).lookupActivationCount = n := by
  simp only [loopSynthesisSummary, synthesis_summary_norm, Nat.mul_one]

/-- The reduced interior-loop summary contains no deferred constant requests. -/
@[synthesis_summary_norm]
theorem loopSynthesisSummary_constantSiteCount
    (n : ℕ) (cfg : Config) (offset : ℕ) :
    (loopSynthesisSummary n cfg offset).constantSiteCount = 0 := by
  cases n <;> rfl

/-- The interior word rounds (`q_s2 = 1` rows) as one formal circuit: `n` rounds of the
`round` bundle at consecutive offsets. The entering row is positional (`Witness`), the
exit row and the interior running sums are the output. The round-to-round induction
lives in this bundle's proofs and nowhere else. -/
def loop (G : Generators) (n : ℕ) : FormalRegionCircuit Fp Config Config field (LoopOut n) where
  configure := pure
  elaborated :=
    { keygenRequirements :=
      { gates cfg _ := [sinsemillaGate cfg]
        lookups cfg _ := [generatorLookup G cfg]
        fixedColumns cfg _ := [cfg.qS2] }
      synthesisSummary cfg offset _ _ := loopSynthesisSummary n cfg offset
      synthesisSummary_eq := by
        intro cfg offset piece self
        simp only [circuit_norm, synthesis_summary_norm, Nat.mul_one]
        simpa [loopSynthesisSummary, roundSynthesisSummary, Nat.add_assoc] using
          (FloorPlanner.RegionSynthesisSummary.foldr_ofColumnsWithSelectorPattern_eq_repeatColumnsWithSelectorPattern
            [(cfg.qS1.index, 0), (cfg.qS1.index, 0)]
            (roundColumns cfg) offset 1 2 0 n
            (lookupActivationCount := 1)).symm
      fixedAssignmentsAgree := by
        intro configInput counts hconfig offset input region
        unfold RegionOperations.FixedAssignmentsAgree
        intro column row left right hleft hright
        simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
          HashPiece.operations_readState, operations_cellVec, List.append_nil] at hleft hright
        rw [RegionCircuit.forRange'_operations] at hleft hright
        simp only [List.mem_flatten, List.mem_ofFn] at hleft hright
        obtain ⟨_, ⟨i, rfl⟩, hleft⟩ := hleft
        obtain ⟨_, ⟨j, rfl⟩, hright⟩ := hright
        simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
          List.append_nil] at hleft hright
        rw [round_assignFixed_mem_iff] at hleft hright
        exact hleft.2.2.trans hright.2.2.symm
      copyCellsAssigned := by
        intro configInput counts hconfig offset input region
        simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
          RegionOperations.CopyCellsAssigned]
        rw [RegionOperations.copyCellsAssignedFrom_append_iff]
        constructor
        · apply RegionCircuit.forRange'_copyCellsAssignedFrom
          intro i
          keygen_registration
        · apply RegionOperations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
          simp only [circuit_norm, RegionOperation.copiedCells,
            List.Forall] }

  synthesize cfg offset (piece : AssignedCell Fp) := do
    RegionCircuit.forRange' offset 1 n (fun r o => do
      let _ ← (round G r).call cfg o piece)
    let exit ← readState cfg (offset + n)
    let zs ← cellVec cfg.bits (fun j => offset + 1 + j) n
    return { exit, zs }

  Witness := State
  extract cfg offset _ self env := eval env (reads cfg offset self)

  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.generatorTable env.env

  -- `n` constrained Sinsemilla words: some `< 2^K` word sequence enters the running sums,
  -- and — for any on-curve accumulator matching the entering row — the exit row carries
  -- the spec-level chain point over those words.
  Spec _ out ws :=
    ∃ ms : ℕ → ℕ,
      (∀ r, ms r < 2 ^ K) ∧
      wordChain ws.z out.zs ms ∧
      ∀ A : Point Fp, A.OnCurve → A.x = ws.row.xA → 2 * A.y = yA ws.row →
        ∀ B, hashToPoint G.S A ((List.range n).map ms) = some B →
          out.exit.row.xA = B.x ∧ 2 * B.y = yA out.exit.row

  -- honest entry: the entering row is the honest row 0 of the piece, with the spec-level
  -- chain defined over the whole piece (`n + 1` words — the exit row's own word too).
  ProverAssumptions piece ws _ :=
    ∃ A B : Point Fp, A.OnCurve ∧ ws.Honest G piece A 0 ∧
      hashToPoint G.S A ((List.range (n + 1)).map (pieceWord piece)) = some B

  ProverSpec piece out ws _ :=
    out.exit = ws.iter G piece n ∧
    ∀ j : Fin n, out.zs[j] = (ws.iter G piece (j.val + 1)).z

  soundness := by
    circuit_proof_start2 [wordChain, reads, readState]
    simp only [roundC_spec_eq, roundC_assumptions_eq, roundC_envAssumptions_eq,
      roundC_extract_eq, mul_one, reads, circuit_norm] at region_0
    -- the whole-vector zs naming, per index
    have h_output_zs : ∀ j, (hj : j < n) →
        env.advice cfg.bits ((place self + (offset + 1 + j) : ℕ) : ℤ)
          = output_zs[j]'hj := by
      intro j hj
      rw [← output_eq.2]
      simp [circuit_norm]
    obtain ⟨⟨h_output_exit_z, h_output_exit_row_xA, h_output_exit_row_xP,
      h_output_exit_row_lambda1, h_output_exit_row_lambda2⟩, -⟩ := output_eq
    have hc' := fun i : Fin n => region_0 i env_assumptions
    choose m hm hspec using hc'
    refine ⟨fun j => if h : j < n then m ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
    · intro r
      beta_reduce
      by_cases hr : r < n
      · rw [dif_pos hr]
        exact hm ⟨r, hr⟩
      · rw [dif_neg hr]
        norm_num [K]

    · -- the running-word chain, from the per-round word relations
      intro j
      rw [show (fun t => if h : t < n then m ⟨t, h⟩ else 0) (j : ℕ) = m j from by
        simp [j.isLt]]
      have hz := (hspec j).1
      rw [show offset + ↑j + 1 = offset + 1 + ↑j from by omega,
        h_output_zs ↑j j.isLt] at hz
      rcases Nat.eq_zero_or_pos j.val with h0 | hpos
      · rw [dif_pos h0]
        rw [show offset + ↑j = offset from by omega] at hz
        exact hz
      · rw [dif_neg (by omega)]
        rw [show offset + ↑j = offset + 1 + (↑j - 1) from by omega,
          h_output_zs (↑j - 1) (by omega)] at hz
        exact hz
    · -- the accumulator fold
      intro A hAon hAx hAyA B hB
      rw [← h_output_exit_row_xA, ← h_output_exit_row_xP,
        ← h_output_exit_row_lambda1, ← h_output_exit_row_lambda2]
      have hfold := loop_fold G
        (fun r => { z := env.advice cfg.bits ((place self + (offset + r) : ℕ) : ℤ),
                    row := { xA := env.advice cfg.xA ((place self + (offset + r) : ℕ) : ℤ),
                             xP := env.advice cfg.xP ((place self + (offset + r) : ℕ) : ℤ),
                             lambda1 := env.advice cfg.lambda1
                               ((place self + (offset + r) : ℕ) : ℤ),
                             lambda2 := env.advice cfg.lambda2
                               ((place self + (offset + r) : ℕ) : ℤ) } })
        (fun j => if h : j < n then m ⟨j, h⟩ else 0)
        (fun i => by
          beta_reduce
          rw [dif_pos i.isLt]
          exact hm i)
        (fun i => by
          beta_reduce
          rw [dif_pos i.isLt]
          have ha := (hspec i).2.2.2
          rw [show offset + (↑i + 1) = offset + ↑i + 1 from by omega]
          exact ha)
        A hAon (by simpa using hAx) (by simpa using hAyA) B hB
      simpa using hfold

  completeness := by
    circuit_proof_start2 [reads, readState]
    obtain ⟨A, B, hAon, hH0, hchain⟩ := prover_assumptions
    -- the whole-vector zs naming, per index
    have h_output_zs : ∀ j, (hj : j < n) →
        env.advice cfg.bits ((place self + (offset + 1 + j) : ℕ) : ℤ)
          = output_zs[j]'hj := by
      intro j hj
      rw [← output_eq.2]
      simp [circuit_norm]
    -- the per-round witness equations, as steps of the row family
    have hsteps : ∀ i : Fin n,
        rowFam cfg place env self offset (i.val + 1)
          = (rowFam cfg place env self offset i.val).step
            ((G.S (pieceWord input (i.val + 1))).x, (G.S (pieceWord input (i.val + 1))).y)
            (pieceZ input (i.val + 1)) := by
      intro i
      have hw := region_0 i
      rw [Halo2.SubcircuitRw.FormalRegionCircuit.extendsWitnesses_call] at hw
      simp only [roundC_synthesize_eq, circuit_norm, mul_one, reads, input_eq] at hw
      obtain ⟨hq, hz, hxp, hl1, hl2, hxa⟩ := hw
      simp only [rowFam]
      rw [show offset + (↑i + 1) = offset + ↑i + 1 from by omega]
      rw [State.mk.injEq, DoubleAndAddRow.mk.injEq]
      exact ⟨hz, hxa, hxp, hl1, hl2⟩
    have hIter := iter_of_steps G input _ hsteps
    have hHall := iter_honest G (rowFam cfg place env self offset 0)
      (by
        simp only [rowFam]
        exact hH0) hchain
    refine ⟨?_, ?_, ?_⟩
    · -- each round's precondition bundle (the engine strengthened the goal per round),
      -- via the chained honesty
      intro i
      rw [roundC_envAssumptions_eq, roundC_assumptions_eq, roundC_proverAssumptions_eq,
        roundC_extract_eq]
      obtain ⟨C, hC⟩ := range_prefix_some G.S A (pieceWord input) hchain
        (show ↑i + 2 ≤ n + 1 by omega)
      refine ⟨env_assumptions, trivial, A, C, hAon, ?_, hC⟩
      -- the entering neighborhood of round i is honest at word i
      have hH := hHall ↑i (by omega)
      rw [← hIter ↑i (by omega)] at hH
      simp only [rowFam] at hH
      simp only [reads, mul_one]
      provable_type_simp
      exact hH
    · -- the exit row is the iterated step
      rw [← output_eq.1.1, ← output_eq.1.2]
      have hn := hIter n le_rfl
      simp only [rowFam] at hn
      simpa using hn
    · -- the interior running sums are the iterated z's
      intro j
      rw [← h_output_zs ↑j j.isLt]
      have hj := hIter (↑j + 1) (by omega)
      simp only [rowFam] at hj
      rw [show offset + 1 + ↑j = offset + (↑j + 1) from by omega]
      exact congrArg State.z hj

/-- The loop publishes its reduced synthesis summary without exposing its operation
stream. -/
@[synthesis_summary_norm]
theorem loop_synthesisSummary_eq
    (G : Generators) (n : ℕ) (config : Config) (offset : ℕ)
    (piece : AssignedCell Fp) (region : RegionIndex) :
    (loop G n).elaborated.synthesisSummary config offset piece region =
      loopSynthesisSummary n config offset := rfl

/-- The interior hash-piece loop requests no deferred constants. -/
@[synthesis_summary_norm]
theorem loop_synthesisSummary_constantSiteCount
    (G : Generators) (n : ℕ) (config : Config) (offset : ℕ)
    (piece : AssignedCell Fp) (region : RegionIndex) :
    ((loop G n).elaborated.synthesisSummary
      config offset piece region).constantSiteCount = 0 := by
  rw [loop_synthesisSummary_eq]
  exact loopSynthesisSummary_constantSiteCount n config offset

/-- The loop writes `qS2 = 1` exactly at its `n` consecutive round rows. -/
theorem loop_assignFixed_mem_iff (G : Generators) (n : ℕ)
    (cfg : Config) (offset : ℕ) (piece : AssignedCell Fp)
    (self : RegionIndex) (column : Column .fixed) (row : ℕ) (value : Fp) :
    .assignFixed column row value ∈
        ((loop G n).call cfg offset piece).operations self ↔
      column = cfg.qS2 ∧ (∃ i : Fin n, row = offset + i.val) ∧ value = 1 := by
  rw [FormalRegionCircuit.call_operations]
  simp only [loop, RegionCircuit.operations_bind, RegionCircuit.operations_pure,
    HashPiece.operations_readState, operations_cellVec, List.append_nil]
  rw [RegionCircuit.forRange'_operations]
  simp only [List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro ⟨operations, ⟨i, rfl⟩, hoperation⟩
    simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
      List.append_nil] at hoperation
    rw [round_assignFixed_mem_iff] at hoperation
    rcases hoperation with ⟨hcolumn, hrow, hvalue⟩
    exact ⟨hcolumn, ⟨i, by simpa using hrow⟩, hvalue⟩
  · rintro ⟨hcolumn, ⟨i, hrow⟩, hvalue⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
      List.append_nil]
    rw [round_assignFixed_mem_iff]
    exact ⟨hcolumn, by simpa using hrow, hvalue⟩

-- contract bridges for the `loop` child (opened by the piece bundle's proofs)
derive_contract_bridges loopC (G : Generators) (n : ℕ) := loop G n

/-- The loop's output variable: exit row + interior z cells (rfl). -/
@[circuit_norm]
theorem loop_output (G : Generators) (n : ℕ) (cfg : Config) (o : ℕ) (iv : AssignedCell Fp)
    (self : RegionIndex) :
    (loop G n).output cfg o iv self
      = { exit := reads cfg (o + n) self,
          zs := Vector.ofFn (fun j => AssignedCell.of self (o + 1 + j) cfg.bits) } := rfl

/-- Every running-sum cell returned by the loop was assigned by its round. -/
theorem loop_output_z_cell_assigned (G : Generators) (n : ℕ)
    (cfg : Config) (offset : ℕ) (piece : AssignedCell Fp)
    (self : RegionIndex) (available : List Cell) (r : Fin n) :
    ((loop G n).output cfg offset piece self).zs[r].cell ∈
      (((loop G n).call cfg offset piece).operations self
        |>.assignedCellsAfter self available) := by
  rw [loop_output, FormalRegionCircuit.call_operations]
  simp only [loop, RegionCircuit.operations_bind,
    RegionCircuit.operations_pure, HashPiece.operations_readState,
    operations_cellVec, List.append_nil,
    RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
  right
  rw [RegionOperations.assignedCells, RegionCircuit.forRange'_operations]
  have hround := round_output_z_cell_assigned G r.val cfg
    (offset + r.val) piece self []
  rw [round_output] at hround
  simp only [reads, AssignedCell.of_cell,
    RegionOperations.mem_assignedCellsAfter_iff, List.nil_append] at hround
  obtain ⟨operation, hoperation, hcell⟩ := List.mem_flatMap.mp hround
  apply List.mem_flatMap.mpr
  refine ⟨operation, ?_, ?_⟩
  · apply List.mem_flatten.mpr
    let body : RegionCircuit Fp Unit := do
      let _ ← (round G r.val).call cfg (offset + r.val) piece
      pure ()
    refine ⟨body.operations self, ?_, ?_⟩
    · simpa only [body, Nat.mul_one] using List.mem_ofFn.mpr ⟨r, rfl⟩
    · simpa only [body, RegionCircuit.operations_bind,
        RegionCircuit.operations_pure, List.append_nil] using hoperation
  · have hrow : offset + r.val + 1 = offset + 1 + r.val := by omega
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn,
      AssignedCell.of_cell, hrow] using hcell

/-! ## The `hash_piece` bundle (edges)

The `z_0` piece copy, the init-row slopes (word 0's — the init materializes round 0's
input row), the loop, and the last-word edge (`q_s2 = qS2Boundary`, the exit `x_a`, the
word-`w` lookup — no gate: the piece-linking gate belongs to the composing circuit). -/

/-- The boundary `q_s2` value: `0` between pieces, `2` on the message's final piece —
re-exported alias so composing files keep their `open`s. -/
theorem qS2Boundary_def (final : Bool) : qS2Boundary final = if final then 2 else 0 := rfl

/-- Honest `x_p` at word 0: the generator x-column read off the piece cell. -/
def initXPWit (G : Generators) (piece : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[(G.S (pieceWord (readCell env piece) 0)).x]

@[circuit_norm]
theorem initXPWit_eval (G : Generators) (piece : AssignedCell Fp)
    (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((initXPWit G piece).eval env)[j]
      = (G.S (pieceWord
          (AssignedCell.eval env.place env.env.toEnvironment piece) 0)).x := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [initXPWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Honest word-0 slopes: `rowValue` of the entering accumulator (the positional `x_a`
cell and the `yaIn` derivation program — Rust's `Y<Value>` thread) at word 0's generator. -/
def initLWit (G : Generators) (piece xAcell : AssignedCell Fp)
    (yaIn : Placed Environment Fp → Fp) (f : Fp × Fp × (Fp × Fp) → Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    let p := readCell env piece
    #v[f (rowValue (readCell env xAcell, yaIn env.toEnvironment)
      ((G.S (pieceWord p 0)).x, (G.S (pieceWord p 0)).y))]

@[circuit_norm]
theorem initLWit_eval (G : Generators) (piece xAcell : AssignedCell Fp)
    (yaIn : Placed Environment Fp → Fp) (f : Fp × Fp × (Fp × Fp) → Fp)
    (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((initLWit G piece xAcell yaIn f).eval env)[j]
      = f (rowValue
          (AssignedCell.eval env.place env.env.toEnvironment xAcell,
           yaIn env.toEnvironment)
          ((G.S (pieceWord
              (AssignedCell.eval env.place env.env.toEnvironment piece) 0)).x,
           (G.S (pieceWord
              (AssignedCell.eval env.place env.env.toEnvironment piece) 0)).y)) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [initLWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The exit `x_a` (Rust assigns `x_a` for the next row on every word, the last included):
the stepped accumulator x over the exit-row readings. -/
def exitXAWit (w : State (AssignedCell Fp)) : WitgenIR Fp 1 :=
  .native fun env => #v[(readsValue w env).stepXA]

@[circuit_norm]
theorem exitXAWit_eval (w : State (AssignedCell Fp)) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((exitXAWit w).eval env)[j] = (readsValue w env).stepXA := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [exitXAWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Output: the first and last double-and-add rows, the exit `x_a` cell, and the piece's
`w + 1` running sums. -/
structure Output (numWords : ℕ) (F : Type) where
  first : DoubleAndAddRow F
  last : DoubleAndAddRow F
  xANext : F
  zs : Vector F numWords
deriving ProvableStruct

/-- The piece `Spec`: the piece is the base-`2^K` recombination of its
`< 2^K` words, the running sums are the suffix recombinations, the last row's `x_p`/`y_p`
land on `S(m_w)`, and — for any on-curve entering accumulator matching the first row —
the exit `x_a`/`Y_A` are the spec-level chain point over the first `w` words. The entering
`x_a` is positional (`output.first.xA` — never copied), matching Rust. -/
def Spec (G : Generators) (w : ℕ) (piece : Fp) (output : Output (w + 1) Fp) : Prop :=
  ∃ ms : ℕ → ℕ,
    (∀ r, ms r < 2 ^ K) ∧
    piece = ((∑ r ∈ Finset.range (w + 1), ms r * 2 ^ (K * r) : ℕ) : Fp) ∧
    output.zs = Vector.ofFn (fun r : Fin (w + 1) =>
      ((∑ j ∈ Finset.range (w + 1 - r.val), ms (r.val + j) * 2 ^ (K * j) : ℕ) : Fp)) ∧
    output.last.xP = (G.S (ms w)).x ∧
    yA output.last * (2 : Fp)⁻¹ - output.last.lambda1 * (output.last.xA - output.last.xP)
      = (G.S (ms w)).y ∧
    ∀ A : Point Fp, A.OnCurve → A.x = output.first.xA → 2 * A.y = yA output.first →
      ∀ B, hashToPoint G.S A ((List.range w).map ms) = some B →
        output.last.xA = B.x ∧ 2 * B.y = yA output.last

/-- The honest-prover precondition: the piece fits in `K·(w+1)` bits and the spec-level
chain from the entering accumulator (the positional `x_a` and the `yaIn` value — the
`Witness` pair) is defined. -/
def ProverAssumptions (G : Generators) (w : ℕ) (piece : Fp) (wit : Fp × Fp) : Prop :=
  piece.val < 2 ^ (K * (w + 1)) ∧
  ∃ A B : Point Fp, A.OnCurve ∧ A.x = wit.1 ∧ A.y = wit.2 ∧
    hashToPoint G.S A ((List.range (w + 1)).map (pieceWord piece)) = some B

/-- The honest-prover contract a COMPOSING circuit's completeness consumes: for the honest
entering accumulator (the `Witness` pair) with exit chain point `B`, the first row's
derived `Y_A` is `2·y_enter`, the exit `x_a` is `B.x`, the last row completes its step's
secant against the exit `x_a`, and the `nextYA` derivation lands on `2·B.y`. -/
def ProverSpec (G : Generators) (w : ℕ) (piece : Fp) (output : Output (w + 1) Fp)
    (wit : Fp × Fp) : Prop :=
  ∀ A B : Point Fp, A.x = wit.1 → A.y = wit.2 →
    hashToPoint G.S A ((List.range (w + 1)).map (pieceWord piece)) = some B →
    yA output.first = 2 * A.y ∧
    output.xANext = B.x ∧
    output.last.lambda2 * output.last.lambda2
      = output.xANext + xR output.last + output.last.xA ∧
    2 * output.last.lambda2 * (output.last.xA - output.xANext) - yA output.last = 2 * B.y

/-- Restricting the word family to its used indices keeps the chain. -/
private theorem map_range_congr (w : ℕ) (ms ms' : ℕ → ℕ)
    (h : ∀ j, j < w → ms j = ms' j) :
    (List.range w).map ms = (List.range w).map ms' :=
  List.map_congr_left fun j hj => h j (List.mem_range.mp hj)

/-- `stepXA` is the stepped row's `x_a`, for any generator/sum arguments (definitional). -/
private theorem stepXA_eq (s : State Fp) (g' : Fp × Fp) (z' : Fp) :
    s.stepXA = (s.step g' z').row.xA := rfl

def circuitSynthesisSummary (w : ℕ) (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  (FloorPlanner.RegionSynthesisSummary.ofColumns
      [.column .advice cfg.bits.index,
        .column .advice cfg.xP.index,
        .column .advice cfg.lambda1.index,
        .column .advice cfg.lambda2.index]
      (offset + 1) 0).combine
    ((loopSynthesisSummary w cfg offset).combine
      ((FloorPlanner.RegionSynthesisSummary.ofColumns
        [.column .fixed cfg.qS2.index,
          .column .advice cfg.xA.index,
          .selector cfg.qS1.index]
        (offset + w + 2) 0 (lookupActivationCount := 1))
          |>.withSelectorActivations [(cfg.qS1.index, offset + w)]))

@[synthesis_summary_norm]
theorem circuitSynthesisSummary_selectorActivations
    (w : ℕ) (cfg : Config) (offset : ℕ) :
    (circuitSynthesisSummary w cfg offset).selectorActivations =
      FloorPlanner.RegionSynthesisSummary.repeatedSelectorPattern
          [(cfg.qS1.index, 0), (cfg.qS1.index, 0)] offset 1 w ++
        [(cfg.qS1.index, offset + w)] := by
  simp only [circuitSynthesisSummary, loopSynthesisSummary,
    synthesis_summary_norm, List.nil_append]

theorem selector_eq_qS1_of_mem_circuitSynthesisSummary
    (w : ℕ) (cfg : Config) (offset : ℕ) (activation : ℕ × ℕ)
    (hactivation : activation ∈
      (circuitSynthesisSummary w cfg offset).selectorActivations) :
    activation.1 = cfg.qS1.index := by
  rw [circuitSynthesisSummary_selectorActivations, List.mem_append] at hactivation
  rcases hactivation with hrepeated | hlast
  · rw [FloorPlanner.RegionSynthesisSummary.mem_repeatedSelectorPattern_iff]
      at hrepeated
    obtain ⟨_, _, source, hsource, rfl⟩ := hrepeated
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsource
    rcases hsource with rfl | rfl <;> rfl
  · have heq := List.mem_singleton.mp hlast
    simpa using congrArg Prod.fst heq

theorem final_qS1_mem_circuitSynthesisSummary
    (w : ℕ) (cfg : Config) (offset : ℕ) :
    (cfg.qS1.index, offset + w) ∈
      (circuitSynthesisSummary w cfg offset).selectorActivations := by
  rw [circuitSynthesisSummary_selectorActivations, List.mem_append]
  exact Or.inr (by simp)

theorem initial_qS1_mem_circuitSynthesisSummary
    (w : ℕ) (cfg : Config) (offset : ℕ) :
    (cfg.qS1.index, offset) ∈
      (circuitSynthesisSummary w cfg offset).selectorActivations := by
  cases w with
  | zero => simpa using final_qS1_mem_circuitSynthesisSummary 0 cfg offset
  | succ w =>
      rw [circuitSynthesisSummary_selectorActivations, List.mem_append]
      left
      rw [FloorPlanner.RegionSynthesisSummary.mem_repeatedSelectorPattern_iff]
      exact ⟨0, by omega, (cfg.qS1.index, 0), by simp, by simp⟩

@[synthesis_summary_norm]
theorem circuitSynthesisSummary_lookupActivationCount
    (w : ℕ) (cfg : Config) (offset : ℕ) :
    (circuitSynthesisSummary w cfg offset).lookupActivationCount = w + 1 := by
  simp only [circuitSynthesisSummary, synthesis_summary_norm,
    loopSynthesisSummary_lookupActivationCount, Nat.zero_add]

@[synthesis_summary_norm]
theorem circuitSynthesisSummary_instanceRowExtent_eq (w : ℕ)
    (cfg : Config) (offset : ℕ) :
    (circuitSynthesisSummary w cfg offset).instanceRowExtent = 0 := by
  simp only [circuitSynthesisSummary, loopSynthesisSummary,
    synthesis_summary_norm]
  simp

def circuitBody (G : Generators) (w : ℕ) (final : Bool)
    (yaIn : Placed Environment Fp → Fp) (cfg : Config) (offset : ℕ)
    (piece : AssignedCell Fp) : RegionCircuit Fp (Output (w + 1) (AssignedCell Fp)) := do
  let _z0 ← copyAdvice piece cfg.bits offset
  let w0 ← readState cfg offset
  let _xP ← assignAdvice cfg.xP offset (initXPWit G piece)
  let _l1 ← assignAdvice cfg.lambda1 offset (initLWit G piece w0.row.xA yaIn (·.1))
  let _l2 ← assignAdvice cfg.lambda2 offset (initLWit G piece w0.row.xA yaIn (·.2.1))
  let _lp ← (loop G w).call cfg offset piece
  let ex ← readState cfg (offset + w)
  let _q ← assignFixed cfg.qS2 (offset + w) (qS2Boundary final)
  let _xf ← assignAdvice cfg.xA (offset + w + 1) (exitXAWit ex)
  (generatorLookup G cfg).enable [] (offset + w)
  let first0 ← cellAt cfg.xA offset
  let firstXP ← cellAt cfg.xP offset
  let firstL1 ← cellAt cfg.lambda1 offset
  let firstL2 ← cellAt cfg.lambda2 offset
  let last0 ← cellAt cfg.xA (offset + w)
  let lastXP ← cellAt cfg.xP (offset + w)
  let lastL1 ← cellAt cfg.lambda1 (offset + w)
  let lastL2 ← cellAt cfg.lambda2 (offset + w)
  let xANext ← cellAt cfg.xA (offset + w + 1)
  let zsCells ← cellVec cfg.bits (fun r => offset + r) (w + 1)
  return {
    first := { xA := first0, xP := firstXP, lambda1 := firstL1, lambda2 := firstL2 },
    last := { xA := last0, xP := lastXP, lambda1 := lastL1, lambda2 := lastL2 },
    xANext := xANext,
    zs := zsCells }

@[keygen_norm]
def circuitKeygenRequirements (G : Generators) :
    KeygenRequirements Fp Config (Var field Fp) where
  gates cfg _ := [sinsemillaGate cfg]
  lookups cfg _ := [generatorLookup G cfg]
  fixedColumns cfg _ := [cfg.qS2]
  permutationColumns cfg _ := [cfg.bits]
  inputCells _ _ input := [input.cell]

theorem circuitBody_copyCellsAssigned (G : Generators) (w : ℕ) (final : Bool)
    (yaIn : Placed Environment Fp → Fp) (cfg : Config) (offset : ℕ)
    (input : Var field Fp) (region : RegionIndex) :
    ((circuitBody G w final yaIn cfg offset input).operations region)
      |>.CopyCellsAssignedFrom region [input.cell] := by
  unfold circuitBody
  simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
    RegionOperations.copyCellsAssignedFrom_append_iff]
  repeat' apply And.intro
  all_goals first
    | (apply RegionOperations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
       simp only [circuit_norm, RegionOperation.copiedCells, List.Forall] <;> done)
    | keygen_registration

/-- The hash-piece body writes only its round selector column: `1` on each
interior round and the circuit's boundary marker on its final row. -/
theorem circuitBody_assignFixed_mem_iff (G : Generators) (w : ℕ)
    (final : Bool) (yaIn : Placed Environment Fp → Fp) (cfg : Config)
    (offset : ℕ) (piece : AssignedCell Fp) (self : RegionIndex)
    (column : Column .fixed) (row : ℕ) (value : Fp) :
    .assignFixed column row value ∈
        (circuitBody G w final yaIn cfg offset piece).operations self ↔
      column = cfg.qS2 ∧
        ((∃ i : Fin w, row = offset + i.val ∧ value = 1) ∨
          row = offset + w ∧ value = qS2Boundary final) := by
  simp only [circuitBody, circuit_norm, List.mem_append]
  rw [loop_assignFixed_mem_iff]
  aesop

def circuit (G : Generators) (w : ℕ) (final : Bool)
    (yaIn : Placed Environment Fp → Fp) :
    FormalRegionCircuit Fp Config Config field (Output (w + 1)) where
  name := "sinsemilla hash_piece"
  configure := pure
  elaborated :=
    { keygenRequirements := circuitKeygenRequirements G
      synthesisSummary cfg offset _ _ := circuitSynthesisSummary w cfg offset
      synthesisSummary_eq := by
        intro cfg offset piece self
        cases w <;> apply FloorPlanner.RegionSynthesisSummary.ext
        all_goals simp only [circuitSynthesisSummary,
            circuitBody, loopSynthesisSummary, roundColumns,
            circuit_norm, synthesis_summary_norm,
            FloorPlanner.RegionSynthesisSummary.ofColumns_columns,
            FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount]
        all_goals try omega
      fixedAssignmentsAgree := by
        intro configInput counts hconfig offset input region
        unfold RegionOperations.FixedAssignmentsAgree
        intro column row left right hleft hright
        simp only [circuitBody, circuit_norm, List.mem_append] at hleft hright
        rw [loop_assignFixed_mem_iff] at hleft hright
        simp at hleft hright
        rcases hleft with hleft | hleft <;>
          rcases hright with hright | hright
        · exact hleft.2.2.trans hright.2.2.symm
        · rcases hleft.2.1 with ⟨i, hi⟩
          omega
        · rcases hright.2.1 with ⟨i, hi⟩
          omega
        · exact hleft.2.2.trans hright.2.2.symm
      copyCellsAssigned := by
        intro configInput counts hconfig offset input region
        simpa only [Configure.output_pure, circuitKeygenRequirements]
          using circuitBody_copyCellsAssigned G w final yaIn configInput offset input region }

  synthesize := circuitBody G w final yaIn

  Witness := fieldPair
  extract cfg offset _ self env :=
    (eval env (AssignedCell.of self offset cfg.xA : Var field Fp), yaIn env)

  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.generatorTable env.env

  Spec piece output _ := Spec G w piece output
  ProverAssumptions piece wit _ := ProverAssumptions G w piece wit
  ProverSpec piece output wit _ := ProverSpec G w piece output wit

  soundness := by
    circuit_proof_start2 [generatorLookup, sinsemillaGate, yPExpr, yAExpr, xRExpr, qS3Expr,
      reads, readState, HashPiece.Spec]
    obtain ⟨⟨h_output_first_xA, h_output_first_xP, h_output_first_lambda1,
      h_output_first_lambda2⟩,
      ⟨h_output_last_xA, h_output_last_xP, h_output_last_lambda1,
        h_output_last_lambda2⟩,
      h_output_xANext, h_output_zsv⟩ := output_eq
    have h_output_zs : ∀ r, (hr : r < w + 1) →
        env.advice cfg.bits ((place self + (offset + r) : ℕ) : ℤ)
          = output_zs[r]'hr := by
      intro r hr
      rw [← h_output_zsv]
      simp [circuit_norm]
    -- the loop's contract, on its extracted entering row
    simp only [← wit_lp_eq, loopC_envAssumptions_eq, loopC_assumptions_eq,
      loopC_spec_eq, loopC_extract_eq, reads, circuit_norm, forall_const,
      wordChain] at lp_spec
    obtain ⟨ms0, hms0, hwc, hfold⟩ := lp_spec env_assumptions
    -- the last-word edge: `q_run` vanishes at the boundary value, the word is `z_w`
    simp only [List.cons.injEq, and_true] at region_2
    obtain ⟨t, ht, h0, h1, h2y⟩ := region_2
    obtain ⟨-, hSpec, -⟩ := env_assumptions
    obtain ⟨mw, hmw, hIdx, hX, hY⟩ := hSpec t ht
    rw [region_1] at h0
    rw [hIdx] at h0
    rw [hX] at h1
    rw [hY] at h2y
    have hzw : env.advice cfg.bits ((place self + (offset + w) : ℕ) : ℤ)
        = (mw : Fp) := by
      linear_combination h0
        + env.advice cfg.bits ((place self + (offset + w + 1) : ℕ) : ℤ)
          * (2 : Fp) ^ K * qS2Boundary_run final
    refine ⟨fun r => if r < w then ms0 r else mw, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r
      beta_reduce
      by_cases hr : r < w
      · rw [if_pos hr]
        exact hms0 r
      · rw [if_neg hr]
        exact hmw
    · -- the piece recombines from its words
      have hkey := chain_eq_sum (n := w + 1)
        (fun r => if r ≤ w
          then env.advice cfg.bits ((place self + (offset + r) : ℕ) : ℤ) else 0)
        (fun r => if r < w then ms0 r else mw)
        (by
          intro r hr
          beta_reduce
          rw [if_pos (show r ≤ w by omega)]
          rcases Nat.lt_or_ge r w with hrw | hrw
          · rw [if_pos hrw, if_pos (show r + 1 ≤ w by omega)]
            have hj := hwc ⟨r, hrw⟩
            simp only [circuit_norm] at hj
            rcases Nat.eq_zero_or_pos r with h0r | hposr
            · subst h0r
              rw [dif_pos rfl] at hj
              simpa using hj
            · rw [dif_neg (by omega)] at hj
              rw [show offset + 1 + (r - 1) = offset + r from by omega,
                show offset + 1 + r = offset + (r + 1) from by omega] at hj
              exact hj
          · obtain rfl : r = w := by omega
            rw [if_neg (by omega), if_neg (by omega)]
            rw [hzw]
            ring)
        (by
          beta_reduce
          rw [if_neg (by omega)])
      beta_reduce at hkey ⊢
      rw [if_pos (by omega : 0 ≤ w), Nat.add_zero] at hkey
      rw [← region_0]
      exact hkey
    · -- the running sums are the suffix recombinations
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      rw [← h_output_zs i hi]
      have hsfx := chain_eq_suffix_sum
        (fun r => env.advice cfg.bits ((place self + (offset + r) : ℕ) : ℤ))
        (fun r => if r < w then ms0 r else mw)
        (by
          intro sIdx hs
          beta_reduce
          rw [if_pos hs]
          have hj := hwc ⟨sIdx, hs⟩
          simp only [circuit_norm] at hj
          rcases Nat.eq_zero_or_pos sIdx with h0r | hposr
          · subst h0r
            rw [dif_pos rfl] at hj
            simpa using hj
          · rw [dif_neg (by omega)] at hj
            rw [show offset + 1 + (sIdx - 1) = offset + sIdx from by omega,
              show offset + 1 + sIdx = offset + (sIdx + 1) from by omega] at hj
            exact hj)
        (by
          beta_reduce
          rw [if_neg (by omega)]
          exact hzw)
        (w - i) i (by omega)
      rw [show w - i + 1 = w + 1 - i from by omega] at hsfx
      exact hsfx
    · -- the last row's x_p lands on the generator
      beta_reduce
      rw [if_neg (show ¬ w < w by omega)]
      linear_combination h1
    · -- the last row's y_p derivation lands on the generator
      beta_reduce
      rw [if_neg (show ¬ w < w by omega)]
      simp only [yA, xR]
      linear_combination h2y
    · -- the chain contract, from the loop's fold
      beta_reduce
      intro A hAon hAx hAyA B hB
      rw [← h_output_first_xA] at hAx
      rw [← h_output_first_xA, ← h_output_first_xP, ← h_output_first_lambda1,
        ← h_output_first_lambda2] at hAyA
      rw [map_range_congr w _ ms0 (fun j hj => if_pos hj)] at hB
      exact hfold A hAon hAx hAyA B hB

  completeness := by
    circuit_proof_start2 [generatorLookup, sinsemillaGate, yPExpr, yAExpr, xRExpr, qS3Expr,
      reads, readState, HashPiece.ProverSpec, HashPiece.ProverAssumptions]
    obtain ⟨hbound, A, B, hAon, hAx, hAy, hchain⟩ := prover_assumptions
    obtain ⟨⟨h_output_first_xA, h_output_first_xP, h_output_first_lambda1,
      h_output_first_lambda2⟩,
      ⟨h_output_last_xA, h_output_last_xP, h_output_last_lambda1,
        h_output_last_lambda2⟩,
      h_output_xANext, h_output_zsv⟩ := output_eq
    have h2 : (2 : Fp) ≠ 0 := by decide
    -- the entering row is the honest row 0
    have hH0 : (State.mk
        (env.advice cfg.bits ((place self + offset : ℕ) : ℤ))
        { xA := env.advice cfg.xA ((place self + offset : ℕ) : ℤ),
          xP := env.advice cfg.xP ((place self + offset : ℕ) : ℤ),
          lambda1 := env.advice cfg.lambda1 ((place self + offset : ℕ) : ℤ),
          lambda2 := env.advice cfg.lambda2 ((place self + offset : ℕ) : ℤ) }).Honest
        G input A 0 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show env.advice cfg.bits _ = pieceZ input 0
        rw [pieceZ_zero]
        exact region_0
      · exact h_output_first_xA.trans hAx.symm
      · exact h_output_first_xP.trans region_1
      · show env.advice cfg.lambda1 _
          = (rowValue (accAfter G (A.x, A.y) input 0) _).1
        rw [show accAfter G (A.x, A.y) input 0 = (A.x, A.y) from rfl, hAx, hAy]
        exact h_output_first_lambda1.trans region_2
      · show env.advice cfg.lambda2 _
          = (rowValue (accAfter G (A.x, A.y) input 0) _).2.1
        rw [show accAfter G (A.x, A.y) input 0 = (A.x, A.y) from rfl, hAx, hAy]
        exact h_output_first_lambda2.trans region_3
    -- the loop's honest-prover precondition, at the extract spelling
    have hLPA : (loop G w).ProverAssumptions input
        ((loop G w).extract cfg offset input_var self
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp)) env.hint := by
      rw [loopC_proverAssumptions_eq, loopC_extract_eq]
      simp only [reads, circuit_norm]
      exact ⟨A, B, hAon, hH0, hchain⟩
    -- the loop's Spec + ProverSpec on the honest run
    have hsp := lp_spec env_assumptions trivial (wit_lp_eq ▸ hLPA)
    simp only [← wit_lp_eq, loopC_spec_eq, loopC_proverSpec_eq, loopC_extract_eq,
      reads, circuit_norm] at hsp
    obtain ⟨-, hExit, hZs⟩ := hsp
    -- the exit row is honest at word w
    have hHexit := iter_honest G
      (State.mk (env.advice cfg.bits ((place self + offset : ℕ) : ℤ))
        { xA := env.advice cfg.xA ((place self + offset : ℕ) : ℤ),
          xP := env.advice cfg.xP ((place self + offset : ℕ) : ℤ),
          lambda1 := env.advice cfg.lambda1 ((place self + offset : ℕ) : ℤ),
          lambda2 := env.advice cfg.lambda2 ((place self + offset : ℕ) : ℤ) })
      hH0 hchain w le_rfl
    rw [← hExit] at hHexit
    -- the exit-row identities (the whole-piece chain point)
    have hEx := step_exit G hHexit hchain
    obtain ⟨-, hExB, hEyB, hEyp⟩ := hEx
    obtain ⟨hzE, hxAE, hxPE, hl1E, hl2E⟩ := hHexit
    have hUsable := env_assumptions.1
    have hBlock := env_assumptions.2.2
    obtain ⟨hb_idx, hb_x, hb_y⟩ := hBlock (pieceWord input w) (pieceWord_lt input w)
    refine ⟨⟨region_0, ⟨env_assumptions, trivial, wit_lp_eq ▸ hLPA⟩, region_4,
      ⟨pieceWord input w, lt_of_lt_of_le (pieceWord_lt input w) hUsable, ?_⟩⟩, ?_⟩
    · -- the word-`w` membership: `q_run` vanishes at the boundary, the word is `z_w`
      simp only [List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_⟩
      · rw [region_4, hb_idx]
        have hzwv : env.advice cfg.bits ((place self + (offset + w) : ℕ) : ℤ)
            = pieceZ input w := hzE
        rw [hzwv, pieceZ_last hbound]
        linear_combination
          (-(env.advice cfg.bits ((place self + (offset + w + 1) : ℕ) : ℤ))
            * (2 : Fp) ^ K) * qS2Boundary_run final
      · rw [hb_x]
        linear_combination hxPE
      · rw [hb_y]
        linear_combination hEyp
    · -- ProverSpec: the honest-cell facts the composing circuit consumes
      intro A' B' hA'x hA'y hchain'
      have hAA : A' = A := by
        have hx : A'.x = A.x := by rw [hA'x, hAx]
        have hy : A'.y = A.y := by rw [hA'y, hAy]
        cases A'
        cases A
        simp_all
      rw [hAA] at hchain' ⊢
      have hBB : B' = B := by
        rw [hchain] at hchain'
        exact (Option.some.inj hchain').symm
      rw [hBB]
      -- first-row Y_A = 2·A.y
      obtain ⟨B1, hB1⟩ := range_prefix_some G.S A (pieceWord input) hchain
        (show 1 ≤ w + 1 by omega)
      have hstep0 : step G.S (pieceWord input 0) A = some B1 := by
        refine prefix_step_some G.S A (pieceWord input) ?_ hB1
        rw [show ((List.range 0).map (pieceWord input)) = ([] : List ℕ) from rfl,
          Specs.Sinsemilla.hashToPoint_nil]
      have hyA0 := honest_yA G hH0 (show accAfter G (A.x, A.y) input 0 = (A.x, A.y) from rfl)
        hstep0
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← h_output_first_xA, ← h_output_first_xP, ← h_output_first_lambda1,
          ← h_output_first_lambda2]
        exact hyA0
      · rw [region_5,
          stepXA_eq _ ((G.S (pieceWord input (w + 1))).x, (G.S (pieceWord input (w + 1))).y)
            (pieceZ input (w + 1))]
        exact hExB
      · -- secant: the exit x_a is the stepped x over the last row's cells
        rw [region_5]
        simp only [State.stepXA, xR]
        ring
      · -- the `nextYA` derivation lands on `2·B.y`
        rw [region_5,
          stepXA_eq _ ((G.S (pieceWord input (w + 1))).x, (G.S (pieceWord input (w + 1))).y)
            (pieceZ input (w + 1))]
        simp only [yA, xR, State.accY, Ecc.DoubleAndAdd.yA,
          Ecc.DoubleAndAdd.xR] at hEyB ⊢
        linear_combination (norm := (field_simp; ring)) 2 * hEyB

/-- The complete piece publishes its reduced synthesis summary. -/
@[synthesis_summary_norm]
theorem circuitSynthesisSummary_constantSiteCount
    (w : ℕ) (config : Config) (offset : ℕ) :
    (circuitSynthesisSummary w config offset).constantSiteCount = 0 := by
  simp only [circuitSynthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem circuit_synthesisSummary_eq
    (G : Generators) (w : ℕ) (final : Bool)
    (yaIn : Placed Environment Fp → Fp) (config : Config) (offset : ℕ)
    (piece : AssignedCell Fp) (region : RegionIndex) :
    (circuit G w final yaIn).elaborated.synthesisSummary
      config offset piece region =
      circuitSynthesisSummary w config offset := rfl

/-- A complete hash-piece bundle requests no deferred constants. -/
@[synthesis_summary_norm]
theorem circuit_synthesisSummary_constantSiteCount
    (G : Generators) (w : ℕ) (final : Bool)
    (yaIn : Placed Environment Fp → Fp) (config : Config) (offset : ℕ)
    (piece : AssignedCell Fp) (region : RegionIndex) :
    ((circuit G w final yaIn).elaborated.synthesisSummary
      config offset piece region).constantSiteCount = 0 := by
  rw [circuit_synthesisSummary_eq]
  simp only [circuitSynthesisSummary, synthesis_summary_norm]

/-- The piece bundle's output variable (position-determined, rfl). -/
@[circuit_norm]
theorem piece_output (G : Generators) (w : ℕ) (final : Bool)
    (yaIn : Placed Environment Fp → Fp) (cfg : Config) (o : ℕ) (iv : AssignedCell Fp)
    (self : RegionIndex) :
    (circuit G w final yaIn).output cfg o iv self
      = { first := { xA := .of self o cfg.xA, xP := .of self o cfg.xP,
                     lambda1 := .of self o cfg.lambda1, lambda2 := .of self o cfg.lambda2 },
          last := { xA := .of self (o + w) cfg.xA, xP := .of self (o + w) cfg.xP,
                    lambda1 := .of self (o + w) cfg.lambda1,
                    lambda2 := .of self (o + w) cfg.lambda2 },
          xANext := .of self (o + w + 1) cfg.xA,
          zs := Vector.ofFn (fun r => .of self (o + r.val) cfg.bits) } := rfl

/-- The exit accumulator x-coordinate returned by a hash piece is assigned by its
last edge operation. -/
theorem circuit_output_xANext_cell_assigned (G : Generators) (w : ℕ)
    (final : Bool) (yaIn : Placed Environment Fp → Fp) (cfg : Config)
    (offset : ℕ) (piece : AssignedCell Fp) (self : RegionIndex)
    (available : List Cell) :
    ((circuit G w final yaIn).output cfg offset piece self).xANext.cell ∈
      (((circuit G w final yaIn).call cfg offset piece).operations self
        |>.assignedCellsAfter self available) := by
  rw [FormalRegionCircuit.call_operations, piece_output]
  simp only [circuit, circuitBody, circuit_norm, AssignedCell.of_cell,
    RegionOperations.mem_assignedCellsAfter_iff, List.mem_append,
    RegionOperations.assignedCells, List.flatMap_append, List.flatMap_cons,
    RegionOperation.assignedCells, List.singleton_append, List.mem_cons,
    true_or, or_true]

/-- Every running-sum cell returned by a hash piece is assigned either by the
initial copy (`z₀`) or its corresponding symbolic loop round. -/
theorem circuit_output_z_cell_assigned (G : Generators) (w : ℕ)
    (final : Bool) (yaIn : Placed Environment Fp → Fp)
    (cfg : Config) (offset : ℕ) (piece : AssignedCell Fp)
    (self : RegionIndex) (available : List Cell) (r : Fin (w + 1)) :
    ((circuit G w final yaIn).output cfg offset piece self).zs[r].cell ∈
      (((circuit G w final yaIn).call cfg offset piece).operations self
        |>.assignedCellsAfter self available) := by
  rcases r with ⟨r, hr⟩
  by_cases hzero : r = 0
  · subst r
    rw [FormalRegionCircuit.call_operations, piece_output]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, circuit, circuitBody,
      circuit_norm, AssignedCell.of_cell,
      RegionOperations.mem_assignedCellsAfter_iff, List.mem_append,
      RegionOperations.assignedCells, List.flatMap_append, List.flatMap_cons,
      RegionOperation.assignedCells, List.singleton_append, List.mem_cons,
      Nat.add_zero, true_or]
  · let j : Fin w := ⟨r - 1, by omega⟩
    have hloop := loop_output_z_cell_assigned G w cfg offset piece self
      available j
    rw [loop_output] at hloop
    have hrow : offset + 1 + j.val = offset + r := by
      simp only [j]
      omega
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, AssignedCell.of_cell,
      RegionOperations.mem_assignedCellsAfter_iff, List.mem_append,
      hrow] at hloop
    rw [FormalRegionCircuit.call_operations, piece_output]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, circuit, circuitBody,
      circuit_norm, AssignedCell.of_cell,
      RegionOperations.mem_assignedCellsAfter_iff, List.mem_append,
      RegionOperations.assignedCells, List.flatMap_append, List.flatMap_cons,
      RegionOperation.assignedCells, List.singleton_append, List.mem_cons]
    rcases hloop with havailable | hassigned
    · exact Or.inl havailable
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hassigned)))))

/-- The first interior running sum returned by a nontrivial hash piece is assigned
by the first loop round. -/
theorem circuit_output_z1_cell_assigned (G : Generators) (w : ℕ)
    (hw : 0 < w) (final : Bool) (yaIn : Placed Environment Fp → Fp)
    (cfg : Config) (offset : ℕ) (piece : AssignedCell Fp)
    (self : RegionIndex) (available : List Cell) :
    ((circuit G w final yaIn).output cfg offset piece self).zs[1].cell ∈
      (((circuit G w final yaIn).call cfg offset piece).operations self
        |>.assignedCellsAfter self available) :=
  circuit_output_z_cell_assigned G w final yaIn cfg offset piece self available
    ⟨1, by omega⟩

end Zcash.Circuits.Sinsemilla.HashPiece
