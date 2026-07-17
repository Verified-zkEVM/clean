import Clean.Halo2.Tactics.ContractBridges
import Clean.Ironwood.Sinsemilla.HashPieceRound

/-!
The Sinsemilla hash-word loop and the `hash_piece` bundle over the round gadget
(`HashPieceRound.lean`) — the loop-composition restructure (`sinsemilla-loop-design.md`).

Reference: `halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`,
`hash_piece` (:295-493): a piece of `w + 1` words at rows `offset .. offset + w`; the
`z_0` piece copy is the only copy constraint (the entering `x_a` "MUST have been already
assigned within this region at the correct offset" — positional, NOT copied); the
entering `y_a` is a pure `Value` thread (`yaIn`, a cell-derivation program — never a
cell). The piece-linking gate at the last row belongs to the composing circuit
(`hash_all_pieces`), as does the trailing dummy row.
-/

namespace Halo2.Ironwood.Sinsemilla.HashPiece

open Orchard (Point)
open Orchard.Ecc (DoubleAndAddRow)
open Orchard.Ecc.DoubleAndAdd (xR yA)
open Orchard.Specs.Sinsemilla (Generators step hashToPoint)
open Orchard.Specs (K)
open Halo2.Ironwood.Sinsemilla
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
  have hA0 : A ≠ 0 := Orchard.Point.ne_zero_of_onCurve hAon
  suffices h : ∀ r, r ≤ n → ∀ C : Point Fp,
      hashToPoint G.S A ((List.range r).map ms) = some C →
      C.OnCurve ∧ (st r).row.xA = C.x ∧ 2 * C.y = yA (st r).row from
    ⟨(h n le_rfl B hB).2.1, (h n le_rfl B hB).2.2⟩
  intro r
  induction r with
  | zero =>
    intro _ C hC
    rw [show ((List.range 0).map ms) = ([] : List ℕ) from rfl,
      Orchard.Specs.Sinsemilla.hashToPoint_nil] at hC
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
      Orchard.Specs.Sinsemilla.hashToPoint_valid hAvalid hprefix_lt hC
    have hC0 : C ≠ 0 :=
      Orchard.Specs.Sinsemilla.hashToPoint_ne_zero hAvalid hA0 hprefix_lt hC
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

/-- The interior word rounds (`q_s2 = 1` rows) as one formal circuit: `n` rounds of the
`round` bundle at consecutive offsets. The entering row is positional (`Witness`), the
exit row and the interior running sums are the output. The round-to-round induction
lives in this bundle's proofs and nowhere else. -/
def loop (G : Generators) (n : ℕ) : FormalRegionCircuit Fp Config Config field (LoopOut n) where
  configure := pure

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
    circuit_proof_start [wordChain, reads]
    simp only [roundC_spec_eq, roundC_assumptions_eq, roundC_envAssumptions_eq,
      roundC_extract_eq, mul_one, reads, circuit_norm] at hc
    provable_type_simp
    have hc' := fun i : Fin n => hc i _hE
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
        (fun r => { z := env.env.advice cfg.bits ((env.place self + (offset + r) : ℕ) : ℤ),
                    row := { xA := env.env.advice cfg.xA ((env.place self + (offset + r) : ℕ) : ℤ),
                             xP := env.env.advice cfg.xP ((env.place self + (offset + r) : ℕ) : ℤ),
                             lambda1 := env.env.advice cfg.lambda1
                               ((env.place self + (offset + r) : ℕ) : ℤ),
                             lambda2 := env.env.advice cfg.lambda2
                               ((env.place self + (offset + r) : ℕ) : ℤ) } })
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
    circuit_proof_start [reads]
    obtain ⟨A, B, hAon, hH0, hchain⟩ := hPA
    -- the per-round witness equations, as steps of the row family
    have hsteps : ∀ i : Fin n,
        rowFam cfg env.place env.env self offset (i.val + 1)
          = (rowFam cfg env.place env.env self offset i.val).step
            ((G.S (pieceWord input (i.val + 1))).x, (G.S (pieceWord input (i.val + 1))).y)
            (pieceZ input (i.val + 1)) := by
      intro i
      have hw := hwit i
      rw [Halo2.SubcircuitRw.FormalRegionCircuit.extendsWitnesses_call] at hw
      simp only [roundC_synthesize_eq, circuit_norm, mul_one, reads, h_input] at hw
      obtain ⟨hq, hz, hxp, hl1, hl2, hxa⟩ := hw
      simp only [rowFam]
      rw [show offset + (↑i + 1) = offset + ↑i + 1 from by omega]
      rw [State.mk.injEq, DoubleAndAddRow.mk.injEq]
      exact ⟨hz, hxa, hxp, hl1, hl2⟩
    have hIter := iter_of_steps G input _ hsteps
    have hHall := iter_honest G (rowFam cfg env.place env.env self offset 0)
      (by
        simp only [rowFam]
        exact hH0) hchain
    refine ⟨?_, ?_, ?_⟩
    · -- each round's constraints, via the engine leaf and the chained honesty
      intro i
      have hleaf := Halo2.SubcircuitRw.region_completeness_leaf_placed (round G ↑i) cfg
        (offset + ↑i * 1) self env input_var (hwit i)
      rw [roundC_envAssumptions_eq, roundC_assumptions_eq, roundC_proverAssumptions_eq,
        roundC_extract_eq] at hleaf
      obtain ⟨C, hC⟩ := range_prefix_some G.S A (pieceWord input) hchain
        (show ↑i + 2 ≤ n + 1 by omega)
      have hinp : (eval env input_var : Fp) = input := by
        rw [← h_input]
        with_unfolding_all rfl
      rw [← hinp] at hC
      refine hleaf ⟨_hE, trivial, A, C, hAon, ?_, hC⟩
      -- the entering neighborhood of round i is honest at word i
      have hH := hHall ↑i (by omega)
      rw [← hIter ↑i (by omega)] at hH
      simp only [rowFam] at hH
      simp only [reads, mul_one]
      provable_type_simp
      simp only [circuit_norm, h_input]
      exact hH
    · -- the exit row is the iterated step
      rw [← h_output_exit_z, ← h_output_exit_row_xA, ← h_output_exit_row_xP,
        ← h_output_exit_row_lambda1, ← h_output_exit_row_lambda2]
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

-- contract bridges for the `loop` child (opened by the piece bundle's proofs)
derive_contract_bridges loopC (G : Generators) (n : ℕ) := loop G n

/-- The loop's output variable: exit row + interior z cells (rfl). -/
@[circuit_norm]
theorem loop_output (G : Generators) (n : ℕ) (cfg : Config) (o : ℕ) (iv : AssignedCell Fp)
    (self : RegionIndex) :
    (loop G n).output cfg o iv self
      = { exit := reads cfg (o + n) self,
          zs := Vector.ofFn (fun j => AssignedCell.of self (o + 1 + j) cfg.bits) } := rfl

end Halo2.Ironwood.Sinsemilla.HashPiece
