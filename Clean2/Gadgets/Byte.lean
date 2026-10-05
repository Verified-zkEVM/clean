/-
Bytes: an abstract data type, with one interface and two synthetic types.

`Byte.interface byte` is the vocabulary of bytes at the synthetic type `byte : CType Native UInt8`:
its contracts are stated on `UInt8`, and what a byte is made of is whatever `byte` says. The
representation invariant is added when a contract is lowered to native values: inputs are assumed
valid, outputs are proved valid. The synthetic types:
- `bits F`, for GF(2): a byte is eight native elements, and every eight elements are a byte, so
  the invariant is `True`. `xor` is eight additions, free on R1CS; `fromBits` is nothing.
- `field F`, for a large field: a byte is one native element, and the invariant is that it is
  below 256. `xor` takes both operands apart into bits; `fromBits` adds the bits up.

Bits are typed too: `bit` is one native element that is `0` or `1` (`Bool.lean`), and a contract
taking a `Vector Bool n` assumes that of its input. `CheckBits` is where native elements become
bits: an assertion whose output is its input, at the finer type.

The upper layers (`Xor3`, `XorOfBits`) are written once, for an unknown `byte`: they never see
the layout or the invariant, and their proofs only carry the invariant from the outputs of one
call to the inputs of the next.
-/
module

public import Clean2.Gadgets.Bits2Num
public import Clean2.Gadgets.Equality
public import Batteries.Data.BitVec.Lemmas
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Clean2.Byte

/-! ## Bytes from bits -/

/-- The byte with the given little-endian bits. -/
def ofBits (b : Fin 8 → Bool) : UInt8 := UInt8.ofBitVec (BitVec.ofFnLE b)

theorem toNat_ofBits (b : Fin 8 → Bool) : (ofBits b).toNat = Nat.ofBits b := by
  simp [ofBits, UInt8.toNat_ofBitVec, BitVec.toNat_ofFnLE]

theorem ofBits_xor (b c : Fin 8 → Bool) : ofBits b ^^^ ofBits c = ofBits fun i => b i ^^ c i := by
  apply UInt8.toBitVec_inj.mp
  ext i hi
  simp [ofBits]

theorem ofNat_ofBits (b : Fin 8 → Bool) : UInt8.ofNat (Nat.ofBits b) = ofBits b := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', toNat_ofBits, Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow b)]

theorem ofBits_eq_sum : ∀ {n : ℕ} (b : Fin n → Bool), Nat.ofBits b = ∑ i : Fin n, (b i).toNat * 2 ^ (i : ℕ)
  | 0, b => by simp [Nat.ofBits_zero]
  | n + 1, b => by
    rw [Nat.ofBits_succ, ofBits_eq_sum, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Function.comp_apply, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring

theorem ofBits_testBit {n m : ℕ} (h : m < 2 ^ n) : Nat.ofBits (fun i : Fin n => m.testBit i) = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_ofBits]
  split
  · rfl
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))]

variable {Native : Type} [Field Native]

theorem fromBits_eq [DecidableEq Native] {n : ℕ} (bits : Vector Native n) :
    Bits2Num.fromBits bits = Nat.ofBits fun i : Fin n => decide (bits[i] = 1) := by
  rw [ofBits_eq_sum, Bits2Num.fromBits]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.getElem_fin]
  split <;> simp_all

/-! ## Two synthetic types -/

/-- GF(2): a byte is its eight bits, one native element each. -/
@[reducible]
def bits (F : Type) [Field F] [DecidableEq F] : CType F UInt8 where
  Shape := natives 8
  Valid _ := True
  decode v := ofBits fun i => decide (v[i] = 1)

/-- A prime field, with the least natural number each element is the image of: computable, so that
the honest prover can take elements apart into bits. For `ZMod p`, it is `ZMod.val`. -/
class NatVal (F : Type) [Field F] where
  val : F → ℕ
  natCast_val (x : F) : (val x : F) = x
  val_natCast_le (m : ℕ) : val (m : F) ≤ m

export NatVal (natCast_val val_natCast_le)

/-- The least natural number a field element is the image of. -/
@[reducible]
def natVal {F : Type} [Field F] [NatVal F] (x : F) : ℕ := NatVal.val x

instance {p : ℕ} [NeZero p] [Fact p.Prime] : NatVal (ZMod p) where
  val := ZMod.val
  natCast_val := ZMod.natCast_zmod_val
  val_natCast_le m := by rw [ZMod.val_natCast]; exact Nat.mod_le m p

theorem natVal_spec {F : Type} [Field F] [NatVal F] {x : F} {m : ℕ} (h : x = m) :
    x = natVal x ∧ natVal x ≤ m := by
  subst h
  exact ⟨(natCast_val _).symm, val_natCast_le m⟩

theorem natVal_natCast {F : Type} [Field F] [NatVal F] {p : ℕ} [CharP F p] {m : ℕ} (hm : m < p) : natVal (m : F) = m := by
  obtain ⟨h_eq, h_le⟩ := natVal_spec (F := F) (m := m) rfl
  have := (CharP.natCast_eq_natCast F p).mp h_eq.symm
  rw [Nat.ModEq, Nat.mod_eq_of_lt (lt_of_le_of_lt h_le hm), Nat.mod_eq_of_lt hm] at this
  exact this

/-- The byte a field element below 256 denotes. -/
def decodeField {F : Type} [Field F] [NatVal F] (x : F) : UInt8 := UInt8.ofNat (natVal x)

/-- A large field: a byte is one native element, below 256. -/
@[reducible]
def field (F : Type) [Field F] [NatVal F] : CType F UInt8 where
  Shape := native
  Valid x := ∃ n : ℕ, n < 2 ^ 8 ∧ x = n
  decode := decodeField

/-! ## The operations on bytes, for any synthetic type -/

inductive Op | xor | fromBits

/-- `xor`, and `fromBits`, where bytes enter from bits. Stated on `UInt8` and `Bool`; what a byte
is made of is the argument. -/
@[reducible]
def interface [DecidableEq Native] (byte : CType Native UInt8) : Op → Interface Native
  | .xor =>
    { input := UInt8 × UInt8, inputCType := byte ×ᵗ byte,
      output := UInt8, outputCType := byte, Spec := fun (a, b) c => c = a ^^^ b }
  | .fromBits =>
    { input := Vector Bool 8, inputCType := CType.vec 8 (bit Native),
      output := UInt8, outputCType := byte, Spec := fun v b => b = ofBits fun i => v[i] }

/-! ## On GF(2) -/

/-- In characteristic 2, the sum of bits is their xor. -/
theorem decide_add_eq_one [DecidableEq Native] {a b : Native} (ha : IsBool a) (hb : IsBool b) (h_two : (1 : Native) + 1 = 0) :
    decide (a + b = 1) = (decide (a = 1) ^^ decide (b = 1)) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [h_two]

section GF2
variable {B : Backend} [Field B.Native] [DecidableEq B.Native]

/-- A byte is eight native elements: `xor` is eight additions, and `fromBits` is nothing at all.
For a field every element of which is a bit, of characteristic 2: GF(2). -/
def gf2 (arith : ∀ n, Impl B (Arith.interface n)) (h_bit : ∀ x : B.Native, IsBool x) (h_two : (1 : B.Native) + 1 = 0) :
    ∀ op, Impl B (interface (bits B.Native) op)
  | .xor =>
    { main | (x, y) => Circuit.mapFin 8 fun i => arith .add (x[i], y[i])
      consistent := by
        rintro ⟨x, y⟩ s
        exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
      spatial := by
        rintro ⟨x, y⟩ s h_in
        simp only [circuit_norm, Set.union_subset_iff] at h_in
        refine Circuit.mapFin_local _ s _ (fun i s => by simp only [circuit_norm]) (fun i s h_mono => ?_) id
        simp only [circuit_norm, Set.union_subset_iff]
        exact ⟨⟨(Backend.footprint_getElem_subset h_in.1 i i.isLt).trans h_mono,
          (Backend.footprint_getElem_subset h_in.2 i i.isLt).trans h_mono⟩, fun h _ => h⟩
      soundness := by
        rintro s env ⟨x, y⟩ _ h
        have hz := Circuit.mapFin_sound _ s env (fun i z => z = B.eval env x[i] + B.eval env y[i])
          (fun i s h => by simp only [circuit_norm] at h ⊢; exact h) h
        refine ⟨trivial, ?_⟩
        change ofBits (fun i => decide ((Vector.map (B.eval env)
          ((Circuit.mapFin 8 fun i => arith .add (x[i], y[i])).output s))[i] = 1)) = _
        rw [ofBits_xor]
        congr 1
        funext i
        simp only [Backend.evalT, ProvableType.map, Fin.getElem_fin, Vector.getElem_map] at hz ⊢
        rw [hz i i.isLt]
        exact decide_add_eq_one (h_bit _) (h_bit _) h_two
      completeness := by
        rintro s env ⟨x, y⟩ h _
        simp only [circuit_norm] at h ⊢ }
  | .fromBits =>
    { main v := pure v
      consistent := by
        intro v s; simp only [circuit_norm]
      spatial := by
        intro v s h_in
        simp only [circuit_norm, Set.iUnion_subset_iff] at h_in ⊢
        exact Set.iUnion_subset h_in
      soundness := by
        intro s env v _ _
        simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map]
      completeness := by
        intro s env v _ _
        simp only [circuit_norm] }

end GF2
end Clean2.Byte

namespace Clean2
variable {Native : Type} [Field Native]

/-! ## Bit vectors, of any width

Three gadgets for the large-field synthetic type, where a byte has to be taken apart into its
bits. They are generic in the width, so that their proofs are loops over it. `CheckBits` is the
entry point of bits: the other two are stated on `Vector Bool n`, and assume their inputs valid. -/

namespace CheckBits

/-- `n` native elements are bits. An assertion; its output is the same elements, as bits. -/
@[reducible]
def interface [DecidableEq Native] (n : ℕ) : Interface Native where
  input := Vector Native n
  inputCType := .natives n
  output := Vector Bool n
  outputCType := CType.vec n (bit Native)
  Spec := fun v b => ∀ i : Fin n, IsBool v[i] ∧ b[i] = decide (v[i] = 1)
  ProverAssumptions := fun v => ∀ i : Fin n, IsBool v[i]

def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] (assertBool : Impl B AssertBool.interface) (n : ℕ) :
    Impl B (interface n) where
  main v := do
    Circuit.foldr n (fun i _ => assertBool v[i]) ()
    return v
  consistent := by
    intro v s
    simp only [circuit_norm]
    exact Circuit.foldr_consistent _ _ _ fun i _ s => by simp only [circuit_norm]
  spatial := by
    intro v s h_in
    simp only [circuit_norm] at h_in ⊢
    refine Circuit.foldr_local (M := unit) _ () s _ (fun i _ s => by simp only [circuit_norm])
      (fun i _ s h_mono _ => ?_) (by rw [Backend.footprintT_unit]; exact Set.empty_subset _)
      fun _ => ?_
    · simp only [circuit_norm]
      exact ⟨(Backend.footprint_getElem_subset h_in i i.isLt).trans h_mono, fun _ _ => Set.empty_subset _⟩
    · have h_mono := Ops.alloc_mono (Circuit.foldr_consistent (fun i _ => assertBool v[i]) () s
        fun i _ s => by simp only [circuit_norm])
      exact Backend.footprintT_ctypeVec_subset.mpr fun i =>
        Backend.footprintT_native_subset.mpr ((Backend.footprint_getElem_subset h_in i i.isLt).trans h_mono)
  soundness := by
    intro s env v _ h
    simp only [circuit_norm] at h ⊢
    have h_bool := Circuit.foldr_sound _ () s env (fun i _ => ∀ j : Fin n, i ≤ j → IsBool (B.eval env v[j]))
      (fun j hj => absurd j.isLt (by omega)) ?_ h
    · simp only [Fin.getElem_fin, Vector.getElem_map]
      exact ⟨fun i => h_bool i (Nat.zero_le _), fun i => ⟨h_bool i (Nat.zero_le _), trivial⟩⟩
    · intro i _ s h_inv h_step j hj
      simp only [circuit_norm] at h_step
      rcases Nat.lt_or_eq_of_le hj with hj | hj
      · exact h_inv j hj
      · rw [show j = i from Fin.ext hj.symm]
        exact h_step
  completeness := by
    intro s env v h hv
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h hv ⊢
    refine ⟨Circuit.foldr_complete _ () s env (fun i _ s _ => ?_) h, hv⟩
    simp only [circuit_norm]
    exact hv i

end CheckBits

namespace XorBits

/-- The bitwise xor of two vectors of `n` bits. -/
@[reducible]
def interface [DecidableEq Native] (n : ℕ) : Interface Native where
  input := Vector Bool n × Vector Bool n
  inputCType := CType.vec n (bit Native) ×ᵗ CType.vec n (bit Native)
  output := Vector Bool n
  outputCType := CType.vec n (bit Native)
  Spec := fun (a, b) c => ∀ i : Fin n, c[i] = (a[i] ^^ b[i])

theorem decide_eq_xor {a b c : Prop} [Decidable a] [Decidable b] [Decidable c] (h : c ↔ ¬(a ↔ b)) :
    decide c = (decide a ^^ decide b) := by
  by_cases a <;> by_cases b <;> simp_all

def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] (xor : Impl B Xor.interface) (n : ℕ) :
    Impl B (interface n) where
  main | (a, b) => Circuit.mapFin n fun i => xor (a[i], b[i])
  consistent := by
    rintro ⟨a, b⟩ s
    exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  spatial := by
    rintro ⟨a, b⟩ s h_in
    simp only [circuit_norm, Set.union_subset_iff, Set.iUnion_subset_iff] at h_in
    refine Circuit.mapFin_local _ s _ (fun i s => by simp only [circuit_norm]) (fun i s h_mono => ?_) fun h => ?_
    · simp only [circuit_norm, Set.union_subset_iff]
      exact ⟨⟨(h_in.1 i).trans h_mono, (h_in.2 i).trans h_mono⟩, fun h _ => h⟩
    · simp only [circuit_norm, Set.iUnion_subset_iff]
      rw [Backend.footprintT_natives, Set.iUnion_subset_iff] at h
      exact h
  soundness := by
    rintro s env ⟨a, b⟩ h_as h
    simp only [circuit_norm] at h_as h ⊢
    have hc := Circuit.mapFin_sound _ s env
      (fun i c => IsBool (B.eval env a[i]) ∧ IsBool (B.eval env b[i]) →
        IsBool c ∧ (c = 1 ↔ ¬(B.eval env a[i] = 1 ↔ B.eval env b[i] = 1)))
      (fun i s h => by simp only [circuit_norm] at h ⊢; exact h) h
    simp only [Fin.getElem_fin, Vector.getElem_map] at h_as hc ⊢
    exact ⟨fun i => (hc i i.isLt ⟨h_as.1 i, h_as.2 i⟩).1,
      fun i => decide_eq_xor (hc i i.isLt ⟨h_as.1 i, h_as.2 i⟩).2⟩
  completeness := by
    rintro s env ⟨a, b⟩ h h_as
    simp only [circuit_norm] at h h_as ⊢
    have hc := Circuit.mapFin_honest _ s env
      (fun i c => IsBool (B.eval env a[i]) ∧ IsBool (B.eval env b[i]) → IsBool c)
      (fun i s h => by simp only [circuit_norm] at h ⊢; exact fun hab => (h hab).1) h
    simp only [Fin.getElem_fin, Vector.getElem_map] at h_as hc ⊢
    exact ⟨Circuit.mapFin_complete _ s env (fun i s h => by simp only [circuit_norm]) h,
      fun i => hc i i.isLt ⟨h_as.1 i, h_as.2 i⟩⟩

end XorBits

namespace ToBits
open Byte

/-- The `i`-th bit of the number a field element denotes: what the honest prover witnesses. -/
def bitOf {F : Type} [Field F] [NatVal F] (i : ℕ) (x : F) : F := if (natVal x).testBit i then 1 else 0

theorem isBool_bitOf {F : Type} [Field F] [NatVal F] (i : ℕ) (x : F) : IsBool (bitOf i x) := by
  unfold bitOf IsBool; split <;> simp

/-- The honest bits denote the number. -/
theorem fromBits_bitOf {F : Type} [Field F] [NatVal F] {n : ℕ} (w : Vector F n) (x : F) (hw : ∀ i : Fin n, w[i] = bitOf i x)
    (h : natVal x < 2 ^ n) : Bits2Num.fromBits w = natVal x := by
  classical
  rw [fromBits_eq]
  conv => rhs; rw [← ofBits_testBit h]
  congr 1
  funext i
  rw [hw i, bitOf]
  split <;> simp_all

/-- `x` is below `2^n`, and these are its `n` bits. An assertion. -/
@[reducible]
def interface [DecidableEq Native] (n : ℕ) : Interface Native where
  input := Native
  inputCType := .native
  output := Vector Bool n
  outputCType := CType.vec n (bit Native)
  Spec := fun x bits => x = ((Nat.ofBits fun i : Fin n => bits[i] : ℕ) : Native)
  ProverAssumptions := fun x => ∃ m : ℕ, m < 2 ^ n ∧ x = m

/-- Witness the bits, check they are bits, and that they add up to `x`. -/
def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] [NatVal B.Native] (arith : ∀ n, Impl B (Arith.interface n))
    (checkBits : ∀ n, Impl B (CheckBits.interface n)) (bits2num : ∀ n, Impl B (Bits2Num.interface n))
    (assertEq : Impl B AssertEq.interface) (n : ℕ) : Impl B (interface n) where
  main x := do
    let raw ← Circuit.mapFin n fun i => arith (.witness native (bitOf i)) x
    let bits ← checkBits n raw
    let v ← bits2num n bits
    assertEq (v, x)
    return bits
  consistent := by
    intro x s
    simp only [circuit_norm]
    exact Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm]
  spatial := by
    intro x s h_in
    simp only [circuit_norm] at h_in ⊢
    rw [Ops.localHold_append_of_consistent (Circuit.mapFin_consistent _ _ fun i s => by simp only [circuit_norm])]
    refine Circuit.mapFin_local _ s _ (fun i s => by simp only [circuit_norm])
      (fun i s h_mono => ?_) fun h_raw => ?_
    · simp only [circuit_norm]
      exact ⟨h_in.trans h_mono, fun h _ => h⟩
    · have h_mono := Ops.alloc_mono (Circuit.mapFin_consistent (n := n)
        (fun i => arith (.witness native (bitOf i)) x) s fun i s => by simp only [circuit_norm])
      simp only [circuit_norm, Set.union_subset_iff, Set.iUnion_subset_iff]
      refine ⟨h_raw, fun h_bits h₁ => ⟨Set.iUnion_subset h_bits, fun h_v h₂ =>
        ⟨⟨h_v, (h_in.trans h_mono).trans (h₁.trans h₂)⟩, fun _ h₃ i => ((h_bits i).trans h₂).trans h₃⟩⟩⟩
  soundness := by
    intro s env x _ h
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h ⊢
    obtain ⟨-, ⟨h_valid, h_spec⟩, h_num, h_eq⟩ := h
    obtain ⟨h_v, -⟩ := h_num h_valid
    refine ⟨h_valid, ?_⟩
    rw [← h_eq, h_v, fromBits_eq]
    simp only [Fin.getElem_fin, Vector.getElem_map]
  completeness := by
    intro s env x h h_as
    have h_raw := Circuit.mapFin_honest (fun i => arith (.witness native (bitOf i)) x) s env
      (fun i b => b = bitOf i (B.eval env x))
      (fun i s h => by simp only [circuit_norm] at h ⊢; exact h) (by simp only [circuit_norm] at h; exact h.1)
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h h_as ⊢
    obtain ⟨m, hm, hx⟩ := h_as
    have h_bool : ∀ i : Fin n, IsBool (B.eval env ((Circuit.mapFin n fun i =>
        arith (.witness native (bitOf i)) x).output s)[i]) := by
      intro i
      rw [Fin.getElem_fin, h_raw i i.isLt]
      exact isBool_bitOf _ _
    obtain ⟨h_map, h_check, h_num⟩ := h
    obtain ⟨⟨h_valid, h_spec⟩, -⟩ := h_check h_bool
    obtain ⟨h_v, -⟩ := h_num h_valid
    refine ⟨⟨Circuit.mapFin_complete _ s env (fun i s h => by simp only [circuit_norm]) h_map, h_bool, ?_⟩, h_valid⟩
    obtain ⟨h_nat, h_le⟩ := natVal_spec hx
    have h_num := fromBits_bitOf ((Circuit.mapFin n fun i => arith (.witness native (bitOf i)) x).output s |>.map (B.eval env))
      (B.eval env x) (fun i => by simp only [Fin.getElem_fin, Vector.getElem_map]; exact h_raw i i.isLt) (lt_of_le_of_lt h_le hm)
    rw [h_v, fromBits_eq, h_nat, ← h_num, fromBits_eq]
    congr 2
    funext i
    simp only [Fin.getElem_fin, Vector.getElem_map]
    exact (h_spec i).2

end ToBits
end Clean2

namespace Clean2.Byte

/-! ## On a large field -/

section Large
variable {F : Type} [Field F] [NatVal F] {p : ℕ} [CharP F p]

theorem decodeField_natCast (hp : 256 ≤ p) {m : ℕ} (hm : m < 256) : decodeField (m : F) = UInt8.ofNat m := by
  rw [decodeField, natVal_natCast (lt_of_lt_of_le hm hp)]

/-- The byte eight bits add up to. -/
theorem decodeField_fromBits [DecidableEq F] (hp : 256 ≤ p) (b : Vector F 8) :
    decodeField ((Bits2Num.fromBits b : ℕ) : F) = ofBits fun i => decide (b[i] = 1) := by
  have h := Bits2Num.fromBits_lt b
  rw [decodeField_natCast hp (by simpa using h), fromBits_eq, ofNat_ofBits]

/-- The byte a number below 256 denotes, by its bits. -/
theorem decodeField_ofBits (hp : 256 ≤ p) (b : Fin 8 → Bool) : decodeField ((Nat.ofBits b : ℕ) : F) = ofBits b := by
  rw [decodeField_natCast hp (Nat.ofBits_lt_two_pow b), ofNat_ofBits]

end Large

section Large
variable {B : Backend} [Field B.Native] [DecidableEq B.Native] [NatVal B.Native] {p : ℕ} [CharP B.Native p]

/-- Take both bytes apart into bits, xor the bits, and add them back up. -/
def largeXor (hp : 256 ≤ p) (toBits : ∀ n, Impl B (ToBits.interface n)) (xorBits : ∀ n, Impl B (XorBits.interface n))
    (bits2num : ∀ n, Impl B (Bits2Num.interface n)) : Impl B (interface (field B.Native) .xor) where
  main | (x, y) => do
    let xb ← toBits 8 x
    let yb ← toBits 8 y
    let zb ← xorBits 8 (xb, yb)
    bits2num 8 zb
  soundness := by
    rintro s env ⟨x, y⟩ h_as h
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h_as h ⊢
    obtain ⟨⟨hxb, hx⟩, ⟨hyb, hy⟩, h_xor, h_num⟩ := h
    obtain ⟨hzb, hz⟩ := h_xor ⟨hxb, hyb⟩
    obtain ⟨hz_eq, hz_lt⟩ := h_num hzb
    refine ⟨⟨_, hz_lt, hz_eq⟩, ?_⟩
    rw [hz_eq, hx, hy, decodeField_fromBits hp, decodeField_ofBits hp, decodeField_ofBits hp, ofBits_xor]
    congr 1
    funext i
    simp only [Fin.getElem_fin, Vector.getElem_map]
    exact hz i
  completeness := by
    rintro s env ⟨x, y⟩ h h_as
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h h_as ⊢
    obtain ⟨hx, hy⟩ := h_as
    obtain ⟨h_x, h_y, h_xor, h_num⟩ := h
    obtain ⟨-, hxb⟩ := h_x hx
    obtain ⟨-, hyb⟩ := h_y hy
    obtain ⟨-, hzb⟩ := h_xor ⟨hxb, hyb⟩
    obtain ⟨hz_eq, hz_lt⟩ := h_num hzb
    exact ⟨⟨hx, hy, hxb, hyb⟩, _, hz_lt, hz_eq⟩

/-- Add the bits up. -/
def largeFromBits (hp : 256 ≤ p) (bits2num : ∀ n, Impl B (Bits2Num.interface n)) :
    Impl B (interface (field B.Native) .fromBits) where
  main v := bits2num 8 v
  soundness := by
    intro s env v h_as h
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h_as h ⊢
    obtain ⟨h_eq, h_lt⟩ := h h_as
    refine ⟨⟨_, h_lt, h_eq⟩, ?_⟩
    rw [h_eq, decodeField_fromBits hp]
    simp only [Fin.getElem_fin, Vector.getElem_map]
  completeness := by
    intro s env v h hv
    simp only [circuit_norm] at h hv ⊢
    obtain ⟨h_eq, h_lt⟩ := h hv
    exact ⟨_, h_lt, h_eq⟩

/-- A byte is one native element, range-checked where it enters. For a field of characteristic
at least 256. -/
def large (hp : 256 ≤ p) (arith : ∀ n, Impl B (Arith.interface n)) : ∀ op, Impl B (interface (field B.Native) op) :=
  let checkBits := CheckBits.impl (AssertBool.impl (arith .mulEq))
  let bits2num := Bits2Num.impl arith
  let toBits := ToBits.impl arith checkBits bits2num (AssertEq.impl arith)
  fun
  | .xor => largeXor hp toBits (XorBits.impl (Xor.impl arith)) bits2num
  | .fromBits => largeFromBits hp bits2num

end Large
end Clean2.Byte

namespace Clean2.Byte
variable {Native : Type} [Field Native] [DecidableEq Native]

/-! ## Upper layers: written once, for every synthetic type of bytes

They see bytes only through `Byte.interface byte`, for a `byte` they know nothing about: the
layout of a byte and its invariant are opaque. The proofs carry the invariant, as opaque facts,
from the outputs of one call to the inputs of the next. -/

namespace Xor3

/-- `a ⊕ b ⊕ c` on bytes. -/
@[reducible]
def interface (byte : CType Native UInt8) : Interface Native where
  input := UInt8 × UInt8 × UInt8
  inputCType := byte ×ᵗ byte ×ᵗ byte
  output := UInt8
  outputCType := byte
  Spec := fun (a, b, c) d => d = a ^^^ b ^^^ c

def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] {byte : CType B.Native UInt8}
    (bytes : ∀ op, Impl B (Byte.interface byte op)) : Impl B (interface byte) where
  main | (a, b, c) => do
    let ab ← bytes .xor (a, b)
    bytes .xor (ab, c)
  spatial := by
    rintro ⟨a, b, c⟩ s h_in
    obtain ⟨ha, hb, hc⟩ := (Backend.footprintT_ctypeProd_subset.mp h_in).imp_right Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    exact ⟨Set.union_subset ha hb, fun h_ab h_mono => ⟨Set.union_subset h_ab (hc.trans h_mono), fun h_d _ => h_d⟩⟩
  soundness := by
    rintro s env ⟨a, b, c⟩ h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    obtain ⟨v_ab, e_ab⟩ := h.1 ⟨ha, hb⟩        -- the inputs are valid: hand them to the first xor
    obtain ⟨v_d, e_d⟩ := h.2 ⟨v_ab, hc⟩        -- its output is valid: hand it to the second
    exact ⟨v_d, by rw [e_d, e_ab]⟩
  completeness := by
    rintro s env ⟨a, b, c⟩ h h_as
    simp only [circuit_norm] at h h_as ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    have v_ab := (h.1 ⟨ha, hb⟩).2
    exact ⟨⟨⟨ha, hb⟩, v_ab, hc⟩, (h.2 ⟨v_ab, hc⟩).2⟩

end Xor3

namespace XorOfBits

/-- A whole circuit: two bytes enter as native elements, checked to be bits, and their xor is
returned. No invariant is assumed of the inputs: `CheckBits` establishes it. -/
@[reducible]
def interface (byte : CType Native UInt8) : Interface Native where
  input := Vector Native 8 × Vector Native 8
  inputCType := CType.natives 8 ×ᵗ CType.natives 8
  output := UInt8
  outputCType := byte
  Spec := fun (a, b) c => (∀ i : Fin 8, IsBool a[i]) ∧ (∀ i : Fin 8, IsBool b[i]) ∧
    c = ofBits (fun i => decide (a[i] = 1)) ^^^ ofBits (fun i => decide (b[i] = 1))
  ProverAssumptions := fun (a, b) => (∀ i : Fin 8, IsBool a[i]) ∧ (∀ i : Fin 8, IsBool b[i])

def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] {byte : CType B.Native UInt8}
    (checkBits : ∀ n, Impl B (CheckBits.interface n)) (bytes : ∀ op, Impl B (Byte.interface byte op)) :
    Impl B (interface byte) where
  main | (a, b) => do
    let x ← bytes .fromBits (← checkBits 8 a)
    let y ← bytes .fromBits (← checkBits 8 b)
    bytes .xor (x, y)
  soundness := by
    rintro s env ⟨a, b⟩ _ h
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h ⊢
    obtain ⟨⟨v_a, h_a⟩, h_x, ⟨v_b, h_b⟩, h_y, h_xor⟩ := h
    obtain ⟨v_x, e_x⟩ := h_x v_a
    obtain ⟨v_y, e_y⟩ := h_y v_b
    obtain ⟨v_z, e_z⟩ := h_xor ⟨v_x, v_y⟩
    refine ⟨v_z, fun i => (h_a i).1, fun i => (h_b i).1, ?_⟩
    rw [e_z, e_x, e_y]
    congr 1 <;> (congr 1; funext i)
    · exact (h_a i).2
    · exact (h_b i).2
  completeness := by
    rintro s env ⟨a, b⟩ h h_as
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h h_as ⊢
    obtain ⟨ha, hb⟩ := h_as
    obtain ⟨h_ca, h_x, h_cb, h_y, h_xor⟩ := h
    have v_a := (h_ca ha).2
    have v_x := (h_x v_a).2
    have v_b := (h_cb hb).2
    have v_y := (h_y v_b).2
    exact ⟨⟨ha, v_a, hb, v_b, v_x, v_y⟩, (h_xor ⟨v_x, v_y⟩).2⟩

end XorOfBits

/-! ## Instances: the same circuits on GF(2) and on a large prime field -/

theorem isBool_zmod_two (x : ZMod 2) : IsBool x := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

instance {F : Type} [Field F] [NatVal F] : NatVal (R1CS F).Native := ‹NatVal F›

/-- R1CS over GF(2): a byte is eight cells. -/
def gf2R1CS : ∀ op, Impl (R1CS (ZMod 2)) (Byte.interface (bits (ZMod 2)) op) :=
  gf2 R1CS.arith isBool_zmod_two (show (1 : ZMod 2) + 1 = 0 by decide)

/-- R1CS over `ZMod p`, for a prime `p ≥ 256`: a byte is one cell. -/
def largeR1CS (p : ℕ) [Fact p.Prime] [Fact (256 ≤ p)] : ∀ op, Impl (R1CS (ZMod p)) (Byte.interface (field (ZMod p)) op) :=
  letI : CharP (R1CS (ZMod p)).Native p := ZMod.charP p
  large (Fact.out : 256 ≤ p) R1CS.arith

/-- The generic layers, at each byte type: `byte` is inferred from the implementation. -/
def xor3GF2 := Xor3.impl gf2R1CS
def xor3Large (p : ℕ) [Fact p.Prime] [Fact (256 ≤ p)] := Xor3.impl (largeR1CS p)
def xorOfBitsGF2 := XorOfBits.impl (CheckBits.impl (AssertBool.impl R1CS.mulEq)) gf2R1CS
def xorOfBitsLarge (p : ℕ) [Fact p.Prime] [Fact (256 ≤ p)] :=
  XorOfBits.impl (CheckBits.impl (AssertBool.impl R1CS.mulEq)) (largeR1CS p)

/-- On GF(2), `xor` is free: additions are linear. -/
example (x y : Vector (LinComb (ZMod 2)) 8) (s : ℕ) : (gf2R1CS .xor).advance (x, y) s = s := rfl

end Clean2.Byte
