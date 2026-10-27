/-
The lanes of a Keccak-f state as the cells of a row hold them: as 64 bit cells, lowest first, or as
four 16-bit limbs, lowest first. The gadgets' specs say which lanes their cells hold.
-/
module

public import Clean.Examples.KeccakAir.Spec
public import Clean.Gadgets.Bits

@[expose] public section

namespace KeccakAir
open Specs.Keccak256 Utils.Bits Gadgets

variable {p : ℕ}

/-! ### Bits -/

/-- The field element of a bit. -/
def ofBool (b : Bool) : F p := if b then 1 else 0

/-- The bit a field element `0` or `1` stands for. -/
def bitOf (v : F p) : Bool := decide (v = 1)

section Bits
variable [Fact p.Prime]

lemma isBool_ofBool (b : Bool) : IsBool (ofBool b : F p) := by
  cases b <;> simp [ofBool, IsBool]

lemma bitOf_ofBool (b : Bool) : bitOf (ofBool b : F p) = b := by
  cases b <;> simp [ofBool, bitOf]

lemma ofBool_bitOf {v : F p} (h : IsBool v) : ofBool (bitOf v) = v := by
  rcases h with rfl | rfl <;> simp [ofBool, bitOf]

lemma ofBool_injective {a b : Bool} (h : (ofBool a : F p) = ofBool b) : a = b := by
  rw [← bitOf_ofBool (p := p) a, h, bitOf_ofBool]

lemma val_ofBool (b : Bool) : (ofBool b : F p).val = b.toNat := by
  cases b <;> simp [ofBool, ZMod.val_one]

lemma bitXor_ofBool (a b : Bool) : bitXor (ofBool a : F p) (ofBool b) = ofBool (a ^^ b) := by
  cases a <;> cases b <;> norm_num [ofBool, bitXor]

lemma bitAndNot_ofBool (a b : Bool) :
    bitAndNot (ofBool a : F p) (ofBool b) = ofBool (!a && b) := by
  cases a <;> cases b <;> simp [ofBool, bitAndNot]

lemma natCast_ne_zero_of_lt {n : ℕ} (hn : 0 < n) (hp : n < p) : (n : F p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd hn h) (by omega)

/-- `diff (diff - 2) (diff - 4) = 0` for `diff = a0 + ... + a4 - c` says that `c` is the parity of
the bits `a0, ..., a4`. -/
lemma parity_iff (hp : 15 < p) (a0 a1 a2 a3 a4 c : Bool) :
    parityCheck (ofBool a0 : F p) (ofBool a1) (ofBool a2) (ofBool a3) (ofBool a4) (ofBool c) = 0 ↔
      c = (a0 ^^ a1 ^^ a2 ^^ a3 ^^ a4) := by
  have two : (2 : F p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (n := 2) (by omega) (by omega)
  have three : (3 : F p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (n := 3) (by omega) (by omega)
  have four : (4 : F p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (n := 4) (by omega) (by omega)
  have five : (5 : F p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (n := 5) (by omega) (by omega)
  have fifteen : (15 : F p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (n := 15) (by omega) (by omega)
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases c <;>
    norm_num [parityCheck, ofBool, two, three, four, five, fifteen]

end Bits

/-! ### Lanes -/

/-- The bit cells of a lane. -/
def bitsOfLane (lane : BitVec 64) : Vector (F p) 64 := .ofFn fun z => ofBool (lane.getLsbD z)

/-- The limb cells of a lane. -/
def limbsOfLane (lane : BitVec 64) : Vector (F p) 4 :=
  .ofFn fun limb => ((lane.toNat >>> (16 * limb.val) % 2 ^ 16 : ℕ) : F p)

/-- The lane of limb cells. -/
def laneOf (limbs : Vector (F p) 4) : BitVec 64 := BitVec.ofNat 64 (laneValue (limbs[·]))

/-- The lane of bit cells. -/
def laneOfBits (bits : Vector (F p) 64) : BitVec 64 :=
  BitVec.ofNat 64 (fromBits (bits.map ZMod.val))

/-- The lanes held as limbs `lane y x`. -/
def lanesOf (lane : Fin 5 → Fin 5 → Vector (F p) 4) : Lanes := fun x y => laneOf (lane y x)

section Lanes

lemma toNat_laneOf (limbs : Vector (F p) 4) : (laneOf limbs).toNat =
    (limbs[0].val + 2 ^ 16 * limbs[1].val + 2 ^ 32 * limbs[2].val + 2 ^ 48 * limbs[3].val) %
      2 ^ 64 := by
  simp only [laneOf, laneValue, BitVec.toNat_ofNat]
  rfl

lemma getElem_bitsOfLane (lane : BitVec 64) (z : ℕ) (hz : z < 64) :
    (bitsOfLane lane : Vector (F p) 64)[z] = ofBool (lane.getLsbD z) := by
  simp [bitsOfLane, BitVec.getLsbD_eq_getElem hz]

lemma val_limbsOfLane (hp : 2 ^ 16 < p) (lane : BitVec 64) (l : ℕ) (hl : l < 4) :
    (limbsOfLane lane : Vector (F p) 4)[l].val = lane.toNat >>> (16 * l) % 2 ^ 16 := by
  simp only [limbsOfLane, Vector.getElem_ofFn]
  rw [ZMod.val_natCast_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) hp)]

/-- The lane of a lane's limbs is the lane. -/
lemma laneOf_limbsOfLane (hp : 2 ^ 16 < p) (lane : BitVec 64) :
    laneOf (limbsOfLane lane : Vector (F p) 4) = lane := by
  apply BitVec.eq_of_toNat_eq
  have h0 := val_limbsOfLane hp lane 0 (by omega)
  have h1 := val_limbsOfLane hp lane 1 (by omega)
  have h2 := val_limbsOfLane hp lane 2 (by omega)
  have h3 := val_limbsOfLane hp lane 3 (by omega)
  have hlt := lane.isLt
  rw [toNat_laneOf, h0, h1, h2, h3]
  simp only [Nat.shiftRight_eq_div_pow]
  omega

lemma val_lt_of_limbsOfLane (hp : 2 ^ 16 < p) {lane : BitVec 64} {limbs : Vector (F p) 4}
    (h : limbs = limbsOfLane lane) (limb : Fin 4) : limbs[limb].val < 2 ^ 16 := by
  rw [h, Fin.getElem_fin, val_limbsOfLane hp _ _ limb.isLt]
  exact Nat.mod_lt _ (by norm_num)

variable [Fact p.Prime]

lemma testBit_fromBits {n : ℕ} (v : Vector ℕ n) (hv : ∀ i (hi : i < n), v[i] = 0 ∨ v[i] = 1)
    (k : ℕ) (hk : k < n) : (fromBits v).testBit k = decide (v[k] = 1) := by
  have := congrArg (·[k]) (toBits_fromBits v hv)
  simp only [Utils.Bits.toBits, Vector.getElem_mapRange] at this
  by_cases ht : (fromBits v).testBit k
  · simp only [ht, ↓reduceIte] at this
    simp [ht, ← this]
  · simp only [ht, Bool.false_eq_true, ↓reduceIte] at this
    simp [ht, ← this]

/-- Boolean cells are the bits of their lane. -/
lemma bitsOfLane_laneOfBits {bits : Vector (F p) 64} (h : ∀ z : Fin 64, IsBool bits[z]) :
    bitsOfLane (laneOfBits bits) = bits := by
  have hv : ∀ i (hi : i < 64), (bits.map ZMod.val)[i] = 0 ∨ (bits.map ZMod.val)[i] = 1 := by
    intro i hi
    have := h ⟨i, hi⟩
    simp only [Fin.getElem_fin] at this
    rcases this with h | h <;> simp [h, ZMod.val_one]
  ext z hz
  rw [getElem_bitsOfLane, laneOfBits, BitVec.getLsbD_ofNat, testBit_fromBits _ hv z hz]
  have := h ⟨z, hz⟩
  simp only [Fin.getElem_fin] at this
  rcases this with h | h <;> simp [h, ofBool, ZMod.val_one, hz]

lemma fromBits_limbBits (lane : BitVec 64) (limb : Fin 4) :
    fromBits ((limbBits (bitsOfLane lane : Vector (F p) 64))[limb].map ZMod.val) =
      lane.toNat >>> (16 * limb.val) % 2 ^ 16 := by
  have hbit (i : ℕ) (hi : i < 16) : ((limbBits (bitsOfLane lane : Vector (F p) 64))[limb].map
      ZMod.val)[i] = (lane.getLsbD (16 * limb.val + i)).toNat := by
    simp only [limbBits, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn,
      getElem_bitsOfLane, val_ofBool, limbBit]
  have hv : ∀ i (hi : i < 16),
      ((limbBits (bitsOfLane lane : Vector (F p) 64))[limb].map ZMod.val)[i] = 0 ∨
        ((limbBits (bitsOfLane lane : Vector (F p) 64))[limb].map ZMod.val)[i] = 1 := by
    intro i hi
    rw [hbit i hi]
    cases lane.getLsbD _ <;> simp
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 16
  · rw [testBit_fromBits _ hv k hk, hbit k hk, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp only [hk, decide_true, Bool.true_and, BitVec.testBit_toNat]
    cases lane.getLsbD (16 * limb.val + k) <;> simp
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (fromBits_lt _ hv)
      (Nat.pow_le_pow_right (by norm_num) (by omega))), Nat.testBit_mod_two_pow]
    simp [hk]

/-- The limbs of a lane pack its bits. -/
lemma fieldFromBits_limbBits (lane : BitVec 64) (limb : Fin 4) :
    fieldFromBits (limbBits (bitsOfLane lane : Vector (F p) 64))[limb] =
      (limbsOfLane lane : Vector (F p) 4)[limb] := by
  simp only [fieldFromBits, limbsOfLane, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [← fromBits_limbBits (p := p) lane limb]
  rfl

/-- 16-bit limbs are the limbs of their lane. -/
lemma limbsOfLane_laneOf (hp : 2 ^ 16 < p) {limbs : Vector (F p) 4}
    (h : ∀ limb : Fin 4, limbs[limb].val < 2 ^ 16) : limbsOfLane (laneOf limbs) = limbs := by
  have h0 : limbs[0].val < 2 ^ 16 := h 0
  have h1 : limbs[1].val < 2 ^ 16 := h 1
  have h2 : limbs[2].val < 2 ^ 16 := h 2
  have h3 : limbs[3].val < 2 ^ 16 := h 3
  ext l hl
  apply ZMod.val_injective
  rw [val_limbsOfLane hp _ l hl, toNat_laneOf, Nat.shiftRight_eq_div_pow]
  interval_cases l <;> omega

lemma getLsbD_rotateLeft (lane : BitVec 64) (offset z : Fin 64) :
    (lane.rotateLeft offset).getLsbD z = lane.getLsbD ((z - offset : Fin 64) : ℕ) := by
  rw [BitVec.getLsbD_rotateLeft, Fin.val_sub]
  obtain ⟨z, hz⟩ := z
  obtain ⟨k, hk⟩ := offset
  simp only [Nat.mod_eq_of_lt hk]
  split_ifs with h
  · congr 1
    rw [Nat.mod_eq_of_lt (by omega)]
  · simp only [hz, decide_true, Bool.true_and]
    congr 1
    omega

end Lanes

/-! ### Packing the bits of a lane into its limbs -/

/-- The inputs of `PackLimbs` that pack 64 bits into four 16-bit limbs. -/
def packLane {α : Type} (bits : Vector α 64) (limbs : Vector α 4) :
    Vector (PackBits.Input 16 α) 4 :=
  .ofFn fun limb => ⟨(limbBits bits)[limb], limbs[limb]⟩

section Pack
variable [Fact p.Prime]

lemma eval_packLane (env : Environment (F p)) (bits : Vector (Expression (F p)) 64)
    (limbs : Vector (Expression (F p)) 4) :
    eval env (packLane bits limbs) =
      packLane (bits.map (Expression.eval env)) (limbs.map (Expression.eval env)) := by
  ext l hl : 1
  simp only [packLane, eval_vector, Vector.getElem_map, Vector.getElem_ofFn, circuit_norm]
  ext k hk
  simp [limbBits]

/-- The limbs that pack the bits of a lane are the lane's limbs. -/
lemma packed_iff (lane : BitVec 64) (limbs : Vector (F p) 4) :
    (∀ l : Fin 4, (packLane (bitsOfLane lane) limbs)[l].value =
      fieldFromBits (packLane (bitsOfLane lane) limbs)[l].bits) ↔ limbs = limbsOfLane lane := by
  simp only [packLane, Fin.getElem_fin, Vector.getElem_ofFn]
  constructor
  · intro h
    ext l hl
    rw [h ⟨l, hl⟩]
    exact fieldFromBits_limbBits lane ⟨l, hl⟩
  · rintro rfl l
    exact (fieldFromBits_limbBits lane l).symm

end Pack

/-! ### The round constant -/

section Iota
variable [Fact p.Prime]

lemma foldl_oneHot (r : Fin 24) (rounds : List (Fin 24)) (hrounds : rounds.Nodup) (sum : F p) :
    rounds.foldl (fun sum r' => sum + (oneHot r)[r']) sum = sum + if r ∈ rounds then 1 else 0 := by
  induction rounds generalizing sum with
  | nil => simp
  | cons r' rounds ih =>
    rw [List.nodup_cons] at hrounds
    rw [List.foldl_cons, ih hrounds.right]
    by_cases h : r' = r
    · subst h
      simp [oneHot, hrounds.left]
    · simp [oneHot, h, Ne.symm h]

/-- With the step flags of round `r`, ι's bit is the bit xor the round constant's. -/
lemma iotaBit_oneHot (r : Fin 24) (b : Bool) (z : Fin 64) :
    iotaBit (oneHot r) (ofBool b : F p) z = ofBool (roundConstantBit r z ^^ b) := by
  have hmem : r ∈ (List.finRange 24).filter (roundConstantBit · z) ↔ roundConstantBit r z := by
    simp
  have hnodup : ((List.finRange 24).filter (roundConstantBit · z)).Nodup :=
    (List.nodup_finRange 24).filter _
  unfold iotaBit
  split
  · rename_i hnil
    rw [hnil] at hmem
    simp only [List.not_mem_nil, false_iff] at hmem
    simp [hmem]
  · rename_i r0 rs hcons
    rw [hcons] at hmem hnodup
    have hsum : rs.foldl (fun sum r' => sum + (oneHot r)[r']) (oneHot r)[r0] =
        (ofBool (roundConstantBit r z) : F p) := by
      have := foldl_oneHot r (r0 :: rs) hnodup (0 : F p)
      rw [List.foldl_cons, zero_add, zero_add] at this
      rw [this]
      simp only [hmem, ofBool]
    rw [hsum, bitXor_ofBool]

end Iota

end KeccakAir
