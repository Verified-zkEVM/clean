/-
Soundness of a window of the Keccak-f AIR from the specs of its four steps: round control, θ,
ρ ∘ π ∘ χ, and ι with the link to the next row. θ's cells hold θ of the round's input, χ's cells
χ ∘ ρ ∘ π of θ's output, and ι's cells the round constant xored into lane `(0, 0)`, so the round's
output is `Lanes.round` of its input, which agrees with `Specs.Keccak256.keccakRound`.
-/
module

public import Clean.Examples.KeccakAir.Gadgets.RoundControl
public import Clean.Examples.KeccakAir.Gadgets.Theta
public import Clean.Examples.KeccakAir.Gadgets.RhoPiChi
public import Clean.Examples.KeccakAir.Gadgets.Iota

@[expose] public section

namespace KeccakAir
open Specs.Keccak256 Air.Flat

variable {p : ℕ}

lemma laneValue_lt {limb : Fin 4 → F p} (h : ∀ l, (limb l).val < 2 ^ 16) :
    laneValue limb < 2 ^ 64 := by
  have := h 0; have := h 1; have := h 2; have := h 3
  simp only [laneValue]
  omega

/-- A state of 16-bit limbs is the state of its lanes. -/
lemma stateOf_eq_toState {limb : Fin 5 → Fin 5 → Fin 4 → F p}
    (h : ∀ y x l, (limb y x l).val < 2 ^ 16) :
    stateOf limb = Lanes.toState (lanesOf fun y x => .ofFn (limb y x)) := by
  ext i hi
  simp only [stateOf, Lanes.toState, lanesOf, laneOf, Vector.getElem_ofFn, BitVec.toNat_ofNat,
    Fin.getElem_fin, Fin.eta]
  rw [Nat.mod_eq_of_lt (laneValue_lt (h _ _))]

lemma rounds_zero (state : Vector ℕ 25) : rounds 0 state = state := rfl

lemma rounds_succ (r : Fin 24) (state : Vector ℕ 25) :
    rounds (r.val + 1) state = keccakRound (rounds r state) roundConstants[r] := by
  simp only [rounds, List.take_add_one, List.foldl_append]
  rw [List.getElem?_eq_getElem (by simp)]
  simp

lemma lanesOf_injective (hp : 2 ^ 16 < p) {lane lane' : BitVec 64}
    (h : (limbsOfLane lane : Vector (F p) 4) = limbsOfLane lane') : lane = lane' := by
  rw [← laneOf_limbsOfLane hp lane, h, laneOf_limbsOfLane hp]

variable [Fact p.Prime]

lemma oneHot_getElem (r i : Fin 24) : (oneHot r : Vector (F p) 24)[i] = if i = r then 1 else 0 := by
  simp [oneHot]

/-- Flags that move by one round on a transition. -/
lemma oneHot_succ {window : Window Row (F p)} {r : Fin 24}
    (hflags : window.current.stepFlags = oneHot r)
    (h : window.current.stepFlags = RoundControl.nextFlags window) :
    window.next.stepFlags = oneHot (r + 1) := by
  ext i hi
  have hnext : window.next.stepFlags[i] =
      (oneHot r : Vector (F p) 24)[((⟨i, hi⟩ : Fin 24) - 1 : Fin 24).val] := by
    have := congrArg (fun v : Vector (F p) 24 => v[((⟨i, hi⟩ : Fin 24) - 1 : Fin 24).val]) h
    simp only [RoundControl.nextFlags, Vector.getElem_ofFn, Fin.getElem_fin, Fin.eta,
      sub_add_cancel, hflags] at this
    exact this.symm
  rw [hnext]
  simp only [oneHot, Vector.getElem_ofFn, Fin.eta, sub_eq_iff_eq_add]

lemma limbIndex_surjective (i : Fin 100) : ∃ y x limb, limbIndex y x limb = i :=
  ⟨⟨i.val / 20, by omega⟩, ⟨i.val / 4 % 5, by omega⟩, ⟨i.val % 4, by omega⟩, by
    ext
    simp only [limbIndex]
    omega⟩

lemma aPrimePrimePrimeLane_eq {α : Type} (row : Row α) (y x : Fin 5) :
    row.aPrimePrimePrimeLane y x =
      if y = 0 ∧ x = 0 then row.aPrimePrimePrime00Limbs else row.aPrimePrimeLane y x := by
  ext l hl
  simp only [Row.aPrimePrimePrimeLane, Row.aPrimePrimePrimeLimb, Row.aPrimePrimeLane,
    Vector.getElem_ofFn]
  split <;> simp

/-- The lanes of a row whose cells hold the steps of a round: its output is `Lanes.round` of its
input, and both are 16-bit. -/
theorem round_of_specs (hp : 2 ^ 16 < p) {window : Window Row (F p)} {r : Fin 24}
    (hr : window.current.stepFlags = oneHot r) (htheta : Theta.Spec window.current)
    (hchi : RhoPiChi.Spec window.current) (hiota : Iota.Spec window) :
    (∀ y x l, (window.current.aLimb y x l).val < 2 ^ 16) ∧
      (∀ y x l, (window.current.aPrimePrimePrimeLimb y x l).val < 2 ^ 16) ∧
      lanesOf window.current.aPrimePrimePrimeLane =
        Lanes.round (lanesOf window.current.aLane) roundConstants[r] := by
  set state := lanesOf window.current.aLane with hstate
  obtain ⟨hA, -, -, haPrime⟩ := htheta
  have hchi' := hchi (Lanes.theta state) haPrime
  obtain ⟨lane, -, h00, hout⟩ := hiota.1 r hr
  have hlane : lane = Lanes.chi (Lanes.rhoPi (Lanes.theta state)) 0 0 :=
    lanesOf_injective hp (h00.symm.trans (hchi' 0 0))
  have houtLane (y x : Fin 5) : window.current.aPrimePrimePrimeLane y x =
      limbsOfLane (Lanes.round state roundConstants[r] x y) := by
    rw [aPrimePrimePrimeLane_eq, Lanes.round, Lanes.iota]
    by_cases h0 : y = 0 ∧ x = 0
    · obtain ⟨rfl, rfl⟩ := h0
      simp only [and_self, ↓reduceIte, hout, hlane]
    · simp only [h0, show ¬(x = 0 ∧ y = 0) by tauto, ↓reduceIte, hchi']
  refine ⟨fun y x l => ?_, fun y x l => ?_, ?_⟩
  · have := val_lt_of_limbsOfLane hp (hA y x) l
    simpa [Row.aLane] using this
  · have := val_lt_of_limbsOfLane hp (houtLane y x) l
    simpa [Row.aPrimePrimePrimeLane] using this
  · funext x y
    simp only [lanesOf, houtLane, laneOf_limbsOfLane hp]

/-- A window that is the first row or carries the invariant, and whose cells hold its four steps,
computes a round of its preimage. -/
theorem windowSpec_of_specs (hp : 2 ^ 16 < p) {window : Window Row (F p)}
    (hassumption : window.isFirstRow = 1 ∨ Carried window.current)
    (hcontrol : RoundControl.Spec window) (htheta : Theta.Spec window.current)
    (hchi : RhoPiChi.Assumptions window.current → RhoPiChi.Spec window.current)
    (hiota : Iota.Assumptions window → Iota.Spec window) : WindowSpec window := by
  obtain ⟨hfirst, htransition, hpreimage, hsame, -, hexport⟩ := hcontrol
  -- the round of the row
  obtain ⟨r, hr, hcarried⟩ : ∃ r : Fin 24, window.current.stepFlags = oneHot r ∧
      (r ≠ 0 → window.current.PreimageNormalized ∧
        window.current.inputState = rounds r window.current.preimageState) := by
    rcases hassumption with hfirst' | ⟨r, hr, hcarried⟩
    · exact ⟨0, hfirst (by rw [hfirst']; exact one_ne_zero), fun h => absurd rfl h⟩
    · exact ⟨r, hr, hcarried⟩
  have hiota := hiota ⟨r, hr⟩
  have hchi := hchi ⟨_, htheta.2.2.2⟩
  obtain ⟨hinputBound, houtputBound, hround⟩ := round_of_specs hp hr htheta hchi hiota
  have hflag (i : ℕ) (hi : i < 24) :
      window.current.stepFlags[i] = if i = r.val then 1 else 0 := by
    have := oneHot_getElem (p := p) r ⟨i, hi⟩
    simp only [Fin.getElem_fin, Fin.ext_iff] at this
    rw [hr, this]
  -- the row's preimage and input
  have hinput : window.current.PreimageNormalized ∧
      window.current.inputState = rounds r window.current.preimageState := by
    by_cases hr0 : r = 0
    · subst hr0
      have hsame' := hpreimage (by rw [hflag 0 (by omega)]; simp)
      refine ⟨fun y x l => ?_, ?_⟩
      · rw [Row.preimageLimb, hsame']
        exact hinputBound y x l
      · simp only [Row.inputState, Row.preimageState, Fin.val_zero, rounds_zero]
        congr 1
        funext y x l
        rw [Row.preimageLimb, Row.aLimb, hsame']
    · exact hcarried hr0
  have houtputState :
      window.current.outputState = rounds (r.val + 1) window.current.preimageState := by
    rw [rounds_succ, ← hinput.right, Row.outputState, Row.inputState,
      stateOf_eq_toState houtputBound, stateOf_eq_toState hinputBound]
    change Lanes.toState (lanesOf window.current.aPrimePrimePrimeLane) =
      keccakRound (Lanes.toState (lanesOf window.current.aLane)) roundConstants[r]
    rw [hround, Lanes.keccakRound_toState]
  refine ⟨r, hr, hinput.left, hinput.right, houtputState, ?_, ?_⟩
  -- only the last round exports
  · intro hexported
    by_contra hne
    have := hexport (by
      rw [hflag 23 (by omega)]
      simp only [show ¬(23 = r.val) from fun h => hne (Fin.ext h.symm), ↓reduceIte]
      exact zero_ne_one)
    rw [hexported] at this
    exact one_ne_zero this
  -- transitions
  · intro htransition'
    have hnext := htransition (by rw [htransition']; exact one_ne_zero)
    refine ⟨oneHot_succ hr hnext, fun hlast => ?_⟩
    have hgate : transitionInPermutation window ≠ 0 := by
      rw [transitionInPermutation, htransition', hflag 23 (by omega)]
      simp only [show ¬(23 = r.val) from fun h => hlast (Fin.ext h.symm), ↓reduceIte]
      norm_num
    refine ⟨(hsame hgate).symm, ?_⟩
    simp only [Row.inputState, Row.outputState]
    congr 1
    funext y x l
    have := congrArg (·[l]) (hiota.2 hgate x y)
    simpa [Row.aLane, Row.aPrimePrimePrimeLane] using this.symm

end KeccakAir

namespace KeccakAir
open Air.Flat

variable {p : ℕ} [Fact p.Prime]

/-- A window that computes a round establishes the invariant of the next row on a transition. -/
theorem carried_of_windowSpec {window : Window Row (F p)} (hspec : WindowSpec window)
    (htransition : window.isTransition = 1) : Carried window.next := by
  obtain ⟨r, -, hnormalized, -, houtput, -, hnext⟩ := hspec
  obtain ⟨hflags, hsame⟩ := hnext htransition
  refine ⟨r + 1, hflags, fun hne => ?_⟩
  have hlast : r ≠ 23 := by
    rintro rfl
    exact hne rfl
  have hval : (r + 1).val = r.val + 1 := by
    have : r.val ≠ 23 := fun h => hlast (Fin.ext h)
    rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hpreimage, hinput⟩ := hsame hlast
  have hstate : window.next.preimageState = window.current.preimageState := by
    simp only [Row.preimageState]
    congr 1
    funext y x l
    simp only [Row.preimageLimb, hpreimage]
  refine ⟨fun y x l => ?_, ?_⟩
  · simpa only [Row.preimageLimb, hpreimage] using hnormalized y x l
  · rw [hinput, houtput, hstate, hval]

end KeccakAir
