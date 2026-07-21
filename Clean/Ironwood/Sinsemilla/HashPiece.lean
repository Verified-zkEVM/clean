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

namespace Halo2.Ironwood.Sinsemilla.HashPiece

open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc (DoubleAndAddRow)
open Halo2.Ironwood.Ecc.DoubleAndAdd (xR yA)
open Halo2.Ironwood.Specs.Sinsemilla (Generators step hashToPoint)
open Halo2.Ironwood.Specs (K)
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
  have hA0 : A ≠ 0 := Halo2.Ironwood.Point.ne_zero_of_onCurve hAon
  suffices h : ∀ r, r ≤ n → ∀ C : Point Fp,
      hashToPoint G.S A ((List.range r).map ms) = some C →
      C.OnCurve ∧ (st r).row.xA = C.x ∧ 2 * C.y = yA (st r).row from
    ⟨(h n le_rfl B hB).2.1, (h n le_rfl B hB).2.2⟩
  intro r
  induction r with
  | zero =>
    intro _ C hC
    rw [show ((List.range 0).map ms) = ([] : List ℕ) from rfl,
      Halo2.Ironwood.Specs.Sinsemilla.hashToPoint_nil] at hC
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
      Halo2.Ironwood.Specs.Sinsemilla.hashToPoint_valid hAvalid hprefix_lt hC
    have hC0 : C ≠ 0 :=
      Halo2.Ironwood.Specs.Sinsemilla.hashToPoint_ne_zero hAvalid hA0 hprefix_lt hC
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
    circuit_proof_start [reads]
    obtain ⟨A, B, hAon, hH0, hchain⟩ := hPA
    -- the per-round witness equations, as steps of the row family
    have hsteps : ∀ i : Fin n,
        rowFam cfg place env self offset (i.val + 1)
          = (rowFam cfg place env self offset i.val).step
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
    have hHall := iter_honest G (rowFam cfg place env self offset 0)
      (by
        simp only [rowFam]
        exact hH0) hchain
    refine ⟨?_, ?_, ?_⟩
    · -- each round's constraints, via the engine leaf and the chained honesty
      intro i
      have hleaf := Halo2.SubcircuitRw.region_completeness_leaf_placed (round G ↑i) cfg
        (offset + ↑i * 1) self (⟨place, env⟩ : Placed ProverEnvironment Fp) input_var (hwit i)
      rw [roundC_envAssumptions_eq, roundC_assumptions_eq, roundC_proverAssumptions_eq,
        roundC_extract_eq] at hleaf
      obtain ⟨C, hC⟩ := range_prefix_some G.S A (pieceWord input) hchain
        (show ↑i + 2 ≤ n + 1 by omega)
      have hinp : (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) input_var : Fp) = input := by
        rw [← h_input]
        simp only [circuit_norm]
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
      = (G.S (pieceWord (env.env.get piece.cell.column
          ((env.place piece.cell.regionIndex + piece.cell.rowOffset : ℕ) : ℤ)) 0)).x := by
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
          (env.env.get xAcell.cell.column
            ((env.place xAcell.cell.regionIndex + xAcell.cell.rowOffset : ℕ) : ℤ),
           yaIn env.toEnvironment)
          ((G.S (pieceWord (env.env.get piece.cell.column
              ((env.place piece.cell.regionIndex + piece.cell.rowOffset : ℕ) : ℤ)) 0)).x,
           (G.S (pieceWord (env.env.get piece.cell.column
              ((env.place piece.cell.regionIndex + piece.cell.rowOffset : ℕ) : ℤ)) 0)).y)) := by
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

def circuit (G : Generators) (w : ℕ) (final : Bool)
    (yaIn : Placed Environment Fp → Fp) :
    FormalRegionCircuit Fp Config Config field (Output (w + 1)) where
  name := "sinsemilla hash_piece"
  configure := pure

  synthesize cfg offset (piece : AssignedCell Fp) := do
    -- z_0 = copy of the piece into the `bits` column (the only copy — the entering
    -- `x_a` is positional, Rust `hash_piece`'s "not copied" rule)
    let _z0 ← copyAdvice piece cfg.bits offset
    let w0 ← readState cfg offset
    -- the init-row slopes: word 0's generator x and the `rowValue` slopes of the
    -- entering accumulator (positional x_a + the `yaIn` thread)
    let _xP ← assignAdvice cfg.xP offset (initXPWit G piece)
    let _l1 ← assignAdvice cfg.lambda1 offset (initLWit G piece w0.row.xA yaIn (·.1))
    let _l2 ← assignAdvice cfg.lambda2 offset (initLWit G piece w0.row.xA yaIn (·.2.1))
    -- the interior word rounds
    let _lp ← (loop G w).call cfg offset piece
    -- the last-word edge at row `offset + w`
    let ex ← readState cfg (offset + w)
    let _q ← assignFixed cfg.qS2 (offset + w) (qS2Boundary final)
    let _xf ← assignAdvice cfg.xA (offset + w + 1) (exitXAWit ex)
    (generatorLookup G cfg).enable [cfg.qS1] (offset + w)
    -- name the output cells (fixed rows)
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

  Witness := fieldPair
  extract cfg offset _ self env :=
    (eval env (AssignedCell.of self offset cfg.xA : Var field Fp), yaIn env)

  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.generatorTable env.env

  Spec piece output _ := Spec G w piece output
  ProverAssumptions piece wit _ := ProverAssumptions G w piece wit
  ProverSpec piece output wit _ := ProverSpec G w piece output wit

  soundness := by
    circuit_proof_start [generatorLookup, sinsemillaGate, yPExpr, yAExpr, xRExpr, qS3Expr,
      reads, HashPiece.Spec]
    obtain ⟨hZ0, hLoop, hQ, hMem⟩ := hc
    rw [loopC_envAssumptions_eq, loopC_assumptions_eq, loopC_spec_eq,
      loopC_extract_eq] at hLoop
    simp only [reads, circuit_norm, forall_const, wordChain] at hLoop
    obtain ⟨ms0, hms0, hwc, hfold⟩ := hLoop _hE
    -- the last-word edge: `q_run` vanishes at the boundary value, the word is `z_w`
    simp only [List.cons.injEq, and_true] at hMem
    obtain ⟨t, ht, h0, h1, h2y⟩ := hMem
    obtain ⟨-, hSpec, -⟩ := _hE
    obtain ⟨mw, hmw, hIdx, hX, hY⟩ := hSpec t ht
    rw [hQ] at h0
    rw [hIdx] at h0
    rw [hX] at h1
    rw [hY] at h2y
    have hzw : env.advice cfg.bits ((place self + (offset + w) : ℕ) : ℤ)
        = (mw : Fp) := by
      linear_combination h0
        + env.advice cfg.bits ((place self + (offset + w + 1) : ℕ) : ℤ)
          * (2 : Fp) ^ K * qS2Boundary_run final
    -- the word family and the running-sum family
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
      rw [← hZ0]
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
      rw [← h_output_last_xP, if_neg (show ¬ w < w by omega)]
      linear_combination h1
    · -- the last row's y_p derivation lands on the generator
      beta_reduce
      rw [← h_output_last_xA, ← h_output_last_xP, ← h_output_last_lambda1,
        ← h_output_last_lambda2, if_neg (show ¬ w < w by omega)]
      simp only [yA, xR]
      linear_combination h2y
    · -- the chain contract, from the loop's fold
      beta_reduce
      intro A hAon hAx hAyA B hB
      rw [← h_output_first_xA] at hAx
      rw [← h_output_first_xA, ← h_output_first_xP, ← h_output_first_lambda1,
        ← h_output_first_lambda2] at hAyA
      rw [map_range_congr w _ ms0 (fun j hj => if_pos hj)] at hB
      have hres := hfold A hAon hAx hAyA B hB
      rw [← h_output_last_xA, ← h_output_last_xP, ← h_output_last_lambda1,
        ← h_output_last_lambda2]
      exact hres

  completeness := by
    circuit_proof_start [generatorLookup, sinsemillaGate, yPExpr, yAExpr, xRExpr, qS3Expr,
      reads, HashPiece.ProverSpec, HashPiece.ProverAssumptions]
    obtain ⟨hbound, A, B, hAon, hAx, hAy, hchain⟩ := hPA
    obtain ⟨hWz0, hWxp, hWl1, hWl2, hWloop, hWq, hWxf⟩ := hwit
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
        exact hWz0
      · exact hAx.symm
      · exact hWxp
      · show env.advice cfg.lambda1 _
          = (rowValue (accAfter G (A.x, A.y) input 0) _).1
        rw [show accAfter G (A.x, A.y) input 0 = (A.x, A.y) from rfl, hAx, hAy]
        exact hWl1
      · show env.advice cfg.lambda2 _
          = (rowValue (accAfter G (A.x, A.y) input 0) _).2.1
        rw [show accAfter G (A.x, A.y) input 0 = (A.x, A.y) from rfl, hAx, hAy]
        exact hWl2
    rw [h_input] at h_spec_0
    -- the loop's honest-prover precondition
    have hLPA : (loop G w).ProverAssumptions input
        ((loop G w).extract cfg offset input_var self (⟨place, env.toEnvironment⟩ : Placed Environment Fp)) env.hint := by
      rw [loopC_proverAssumptions_eq, loopC_extract_eq]
      simp only [reads, circuit_norm]
      exact ⟨A, B, hAon, hH0, hchain⟩
    -- the loop's Spec + ProverSpec on the honest run
    have hsp := h_spec_0 _hE trivial hLPA
    rw [loopC_spec_eq, loopC_proverSpec_eq, loopC_extract_eq] at hsp
    simp only [reads, circuit_norm] at hsp
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
    have hUsable := _hE.1
    have hBlock := _hE.2.2
    rw [Placed.toEnvironment_env] at hUsable hBlock
    obtain ⟨hb_idx, hb_x, hb_y⟩ := hBlock (pieceWord input w) (pieceWord_lt input w)
    refine ⟨⟨⟨_hE, trivial, hLPA⟩,
      ⟨pieceWord input w, lt_of_lt_of_le (pieceWord_lt input w) hUsable, ?_⟩⟩, ?_⟩
    · -- the word-`w` membership: `q_run` vanishes at the boundary, the word is `z_w`
      simp only [List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_⟩
      · rw [hb_idx]
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
          Halo2.Ironwood.Specs.Sinsemilla.hashToPoint_nil]
      have hyA0 := honest_yA G hH0 (show accAfter G (A.x, A.y) input 0 = (A.x, A.y) from rfl)
        hstep0
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← h_output_first_xA, ← h_output_first_xP, ← h_output_first_lambda1,
          ← h_output_first_lambda2]
        exact hyA0
      · rw [← h_output_xANext, hWxf,
          stepXA_eq _ ((G.S (pieceWord input (w + 1))).x, (G.S (pieceWord input (w + 1))).y)
            (pieceZ input (w + 1))]
        exact hExB
      · -- secant: the exit x_a is the stepped x over the last row's cells
        rw [← h_output_last_xA, ← h_output_last_xP, ← h_output_last_lambda1,
          ← h_output_last_lambda2, ← h_output_xANext, hWxf]
        simp only [State.stepXA, xR]
        ring
      · -- the `nextYA` derivation lands on `2·B.y`
        rw [← h_output_last_xA, ← h_output_last_xP, ← h_output_last_lambda1,
          ← h_output_last_lambda2, ← h_output_xANext, hWxf,
          stepXA_eq _ ((G.S (pieceWord input (w + 1))).x, (G.S (pieceWord input (w + 1))).y)
            (pieceZ input (w + 1))]
        simp only [yA, xR, State.accY, Halo2.Ironwood.Ecc.DoubleAndAdd.yA,
          Halo2.Ironwood.Ecc.DoubleAndAdd.xR] at hEyB ⊢
        linear_combination (norm := (field_simp; ring)) 2 * hEyB

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

end Halo2.Ironwood.Sinsemilla.HashPiece

