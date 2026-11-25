module

public import Clean.Circuit.WitnessIR

/-!
# Wide unsigned integers in the witness IR

The witness IR's integer sort is `u64`. Values wider than 64 bits — the `ℕ` value of a
field element, a scalar plus a constant, a bit window above bit 64 — are computed on
little-endian vectors of 64-bit limbs, as an implementation on machine words would.

`LimbsOver.toNat` reads limbs back as the number `Σ limbᵢ · 2^(64·i)`, and each operation
has an evaluation lemma stated on that number, so proofs about witness programs reason
about plain `ℕ` arithmetic and never about limb carries.

Operations:
- `FExprOver.window x start len`: bits `start .. start+len-1` of `val x` as one `u64`
  (`len ≤ 64`), summed from `BExpr.bit`. Exact on every `FiniteField`.
- `LimbsOver.ofField x n`: the `n` low limbs of `val x`.
- `LimbsOver.const c n`: the `n` low limbs of a constant.
- `LimbsOver.add a b`: addition with carry propagation, wrapping at `2^(64·n)`.
- `LimbsOver.window a lo len`: bits `lo .. lo+len-1` of a limb vector as one `u64`
  (`len ≤ 64`).

All operations are generic over the variable atom `V`, like the IR itself.
-/

@[expose] public section

variable {F V Env : Type}

namespace Witgen

/-- The number represented by little-endian 64-bit limbs: `Σ limbᵢ · 2^(64·i)`. -/
def limbsToNat : List UInt64 → ℕ
  | [] => 0
  | a :: as => a.toNat + 2 ^ 64 * limbsToNat as

/-- A wide unsigned integer in the witness IR: `n` little-endian 64-bit limbs. -/
abbrev LimbsOver (F V : Type) (n : ℕ) := Vector (U64ExprOver F V) n

/-- Bits `start .. start+len-1` of `val x`, as the `u64` sum of `bit (start + k) · 2^k`.
Meaningful for `len ≤ 64`. -/
def FExprOver.window (x : FExprOver F V) (start : ℕ) : ℕ → U64ExprOver F V
  | 0 => .const 0
  | k + 1 => .add (x.window start k)
      (.ite (.bit x (start + k)) (.const (UInt64.ofNat (2 ^ k))) (.const 0))

namespace LimbsOver

/-- The number a limb vector evaluates to. -/
def toNat [FiniteField F] [WitgenEnv F Env V] (ctx : CtxOver F Env) {n : ℕ}
    (a : LimbsOver F V n) : ℕ :=
  limbsToNat (a.toList.map (U64ExprOver.eval ctx))

/-- The `n` low limbs of `val x`. -/
def ofField (x : FExprOver F V) (n : ℕ) : LimbsOver F V n :=
  Vector.ofFn fun i => x.window (64 * i.val) 64

/-- The `n` low limbs of the constant `c`. -/
def const (c : ℕ) (n : ℕ) : LimbsOver F V n :=
  Vector.ofFn fun i => .const (UInt64.ofNat (c / 2 ^ (64 * i.val)))

/-- The carry out of `a + b + c` for limbs `a`, `b` and a carry-in `c ∈ {0, 1}`: one of the
two additions wrapped. -/
def carry (a b c : U64ExprOver F V) : U64ExprOver F V :=
  .add (.ite (.lt (.add a b) a) (.const 1) (.const 0))
    (.ite (.lt (.add (.add a b) c) (.add a b)) (.const 1) (.const 0))

/-- Limb-wise addition with carry propagation, starting from carry-in `c`. -/
def addList (c : U64ExprOver F V) : List (U64ExprOver F V) → List (U64ExprOver F V) →
    List (U64ExprOver F V)
  | a :: as, b :: bs => .add (.add a b) c :: addList (carry a b c) as bs
  | _, _ => []

theorem length_addList (c : U64ExprOver F V) :
    ∀ (as bs : List (U64ExprOver F V)), as.length = bs.length →
      (addList c as bs).length = as.length
  | [], _, _ => by simp [addList]
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [addList, length_addList (carry a b c) as bs h]

/-- Addition of limb vectors, wrapping at `2^(64·n)`. -/
def add {n : ℕ} (a b : LimbsOver F V n) : LimbsOver F V n :=
  ⟨(addList (.const 0) a.toList b.toList).toArray, by
    simp [length_addList _ _ _ (by simp : a.toList.length = b.toList.length)]⟩

/-- `window` on a limb list: skip whole limbs below `lo`, then combine the limb holding
bit `lo` with its upper neighbour and mask to `len` bits. -/
def windowList (lo len : ℕ) : List (U64ExprOver F V) → U64ExprOver F V
  | [] => .const 0
  | a :: as =>
    if 64 ≤ lo then windowList (lo - 64) len as
    else .land
      (if lo = 0 then a
        else .add (.shiftR a (.const (UInt64.ofNat lo)))
          (.shiftL (as.headD (.const 0)) (.const (UInt64.ofNat (64 - lo)))))
      (.const (UInt64.ofNat (2 ^ len - 1)))

/-- Bits `lo .. lo+len-1` of a limb vector, as one `u64`. Meaningful for `len ≤ 64`. -/
def window {n : ℕ} (a : LimbsOver F V n) (lo len : ℕ) : U64ExprOver F V :=
  windowList lo len a.toList

end LimbsOver

/-! ## Evaluation lemmas -/

section Eval
variable [FiniteField F] [WitgenEnv F Env V] (ctx : CtxOver F Env)

private theorem pow_le_two_pow_64 {k : ℕ} (hk : k ≤ 64) : 2 ^ k ≤ 2 ^ 64 :=
  Nat.pow_le_pow_right (by norm_num) hk

private theorem toNat_ofNat_of_lt {n : ℕ} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

@[simp, circuit_norm]
theorem FExprOver.toNat_eval_window (x : FExprOver F V) (start : ℕ) {len : ℕ}
    (hlen : len ≤ 64) :
    ((x.window start len).eval ctx).toNat = FiniteField.val (x.eval ctx) / 2 ^ start % 2 ^ len := by
  induction len with
  | zero => simp [FExprOver.window, U64ExprOver.eval, Nat.mod_one]
  | succ k ih =>
    set y := FiniteField.val (x.eval ctx) / 2 ^ start
    have hk : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hbit : (FiniteField.val (x.eval ctx)).testBit (start + k) = decide (y / 2 ^ k % 2 = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul, ← pow_add]
    have hsplit : y % 2 ^ (k + 1) = y % 2 ^ k + 2 ^ k * (y / 2 ^ k % 2) := by
      rw [pow_succ, Nat.mod_mul]
    have hlt : y % 2 ^ (k + 1) < 2 ^ 64 :=
      lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (pow_le_two_pow_64 hlen)
    simp only [FExprOver.window, U64ExprOver.eval, BExprOver.eval, UInt64.toNat_add,
      ih (by omega), hbit]
    rw [hsplit] at hlt ⊢
    rcases Nat.mod_two_eq_zero_or_one (y / 2 ^ k) with h | h <;> rw [h] at hlt ⊢ <;>
      simp [toNat_ofNat_of_lt hk]

/-- Limbs whose `i`-th entry is the `i`-th 64-bit digit of `y` represent `y` modulo
`2^(64·n)`. -/
private theorem limbsToNat_ofFn_digits {n : ℕ} :
    ∀ (y : ℕ) (g : ℕ → UInt64), (∀ i, (g i).toNat = y / 2 ^ (64 * i) % 2 ^ 64) →
      limbsToNat (List.ofFn fun i : Fin n => g i.val) = y % 2 ^ (64 * n) := by
  induction n with
  | zero => intro y g _; simp [limbsToNat, Nat.mod_one]
  | succ n ih =>
    intro y g hg
    rw [List.ofFn_succ]
    simp only [limbsToNat, Fin.val_zero, Fin.val_succ]
    have hrest := ih (y / 2 ^ 64) (fun i => g (i + 1)) (fun i => by
      rw [hg (i + 1), Nat.div_div_eq_div_mul, ← pow_add]; ring_nf)
    rw [hrest, hg 0, Nat.mul_zero, pow_zero, Nat.div_one,
      show 64 * (n + 1) = 64 + 64 * n by ring, pow_add, Nat.mod_mul]

@[simp, circuit_norm]
theorem LimbsOver.toNat_ofField (x : FExprOver F V) (n : ℕ) :
    (LimbsOver.ofField x n).toNat ctx = FiniteField.val (x.eval ctx) % 2 ^ (64 * n) := by
  simp only [LimbsOver.toNat, LimbsOver.ofField, Vector.toList_ofFn, List.map_ofFn]
  exact limbsToNat_ofFn_digits _ (fun i => (x.window (64 * i) 64).eval ctx)
    (fun i => FExprOver.toNat_eval_window ctx x _ le_rfl)

@[simp, circuit_norm]
theorem LimbsOver.toNat_const (c n : ℕ) :
    (LimbsOver.const c n : LimbsOver F V n).toNat ctx = c % 2 ^ (64 * n) := by
  simp only [LimbsOver.toNat, LimbsOver.const, Vector.toList_ofFn, List.map_ofFn]
  exact limbsToNat_ofFn_digits c (fun i => UInt64.ofNat (c / 2 ^ (64 * i)))
    (fun i => UInt64.toNat_ofNat')

private theorem toNat_carry (a b c : U64ExprOver F V) (hc : (c.eval ctx).toNat ≤ 1) :
    ((LimbsOver.carry a b c).eval ctx).toNat
        = ((a.eval ctx).toNat + (b.eval ctx).toNat + (c.eval ctx).toNat) / 2 ^ 64 ∧
      (((a.add b).add c).eval ctx).toNat
        = ((a.eval ctx).toNat + (b.eval ctx).toNat + (c.eval ctx).toNat) % 2 ^ 64 := by
  have ha := UInt64.toNat_lt (a.eval ctx)
  have hb := UInt64.toNat_lt (b.eval ctx)
  simp only [LimbsOver.carry, U64ExprOver.eval, BExprOver.eval, UInt64.toNat_add,
    UInt64.lt_iff_toNat_lt]
  simp only [Nat.reducePow]
  constructor
  · split_ifs <;> simp only [decide_eq_true_eq, UInt64.toNat_one, UInt64.toNat_zero] at * <;>
      omega
  · omega

private theorem limbsToNat_addList (c : U64ExprOver F V) :
    ∀ (as bs : List (U64ExprOver F V)), as.length = bs.length → (c.eval ctx).toNat ≤ 1 →
      limbsToNat ((LimbsOver.addList c as bs).map (U64ExprOver.eval ctx))
        = (limbsToNat (as.map (U64ExprOver.eval ctx)) + limbsToNat (bs.map (U64ExprOver.eval ctx))
            + (c.eval ctx).toNat) % 2 ^ (64 * as.length)
  | [], _, _, hc => by simp [LimbsOver.addList, limbsToNat, Nat.mod_one]
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, h, hc => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    obtain ⟨hcarry, hsum⟩ := toNat_carry ctx a b c hc
    have hc' : ((LimbsOver.carry a b c).eval ctx).toNat ≤ 1 := by
      rw [hcarry]
      have := UInt64.toNat_lt (a.eval ctx)
      have := UInt64.toNat_lt (b.eval ctx)
      omega
    simp only [LimbsOver.addList, List.map_cons, limbsToNat, List.length_cons]
    rw [limbsToNat_addList (LimbsOver.carry a b c) as bs h hc', hcarry, hsum]
    set A := (a.eval ctx).toNat
    set B := (b.eval ctx).toNat
    set C := (c.eval ctx).toNat
    set X := limbsToNat (as.map (U64ExprOver.eval ctx))
    set Y := limbsToNat (bs.map (U64ExprOver.eval ctx))
    have hsplit : A + 2 ^ 64 * X + (B + 2 ^ 64 * Y) + C
        = (A + B + C) % 2 ^ 64 + 2 ^ 64 * (X + Y + (A + B + C) / 2 ^ 64) := by
      have := Nat.div_add_mod (A + B + C) (2 ^ 64)
      linarith
    have hlow : (A + B + C) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
    rw [hsplit, show 64 * (as.length + 1) = 64 + 64 * as.length by ring, pow_add, Nat.mod_mul,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow, Nat.add_mul_div_left _ _ (by norm_num),
      Nat.div_eq_of_lt hlow, Nat.zero_add]

@[simp, circuit_norm]
theorem LimbsOver.toNat_add {n : ℕ} (a b : LimbsOver F V n) :
    (a.add b).toNat ctx = (a.toNat ctx + b.toNat ctx) % 2 ^ (64 * n) := by
  simp only [LimbsOver.toNat, LimbsOver.add, Vector.toList_mk]
  rw [limbsToNat_addList ctx _ _ _ (by simp) (by simp [U64ExprOver.eval])]
  simp [U64ExprOver.eval]

/-- The exact form of `toNat_add` when the sum fits. -/
theorem LimbsOver.toNat_add_of_lt {n : ℕ} (a b : LimbsOver F V n)
    (h : a.toNat ctx + b.toNat ctx < 2 ^ (64 * n)) :
    (a.add b).toNat ctx = a.toNat ctx + b.toNat ctx := by
  rw [LimbsOver.toNat_add, Nat.mod_eq_of_lt h]

private theorem limbsToNat_cons_div {a : UInt64} {as : List UInt64} {lo : ℕ} (h : 64 ≤ lo) :
    limbsToNat (a :: as) / 2 ^ lo = limbsToNat as / 2 ^ (lo - 64) := by
  have ha := UInt64.toNat_lt a
  rw [limbsToNat, show lo = 64 + (lo - 64) by omega, pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt ha, Nat.zero_add,
    Nat.add_sub_cancel_left]

/-- The limb holding bit `lo < 64`, combined with the next limb's low bits, determines the
`len ≤ 64` bits from `lo` upwards. -/
private theorem window_digits {A B R lo len : ℕ} (hlo : lo < 64)
    (hlen : len ≤ 64) :
    (A + 2 ^ 64 * (B + 2 ^ 64 * R)) / 2 ^ lo % 2 ^ len
      = (A / 2 ^ lo + 2 ^ (64 - lo) * B) % 2 ^ len := by
  have h64 : (2 : ℕ) ^ 64 = 2 ^ lo * 2 ^ (64 - lo) := by rw [← pow_add]; congr 1; omega
  obtain ⟨m, hm⟩ : 2 ^ len ∣ 2 ^ (64 - lo) * 2 ^ 64 := Dvd.dvd.mul_left (pow_dvd_pow 2 hlen) _
  have hN : A + 2 ^ 64 * (B + 2 ^ 64 * R)
      = A + 2 ^ lo * (2 ^ (64 - lo) * B + 2 ^ len * (m * R)) := by
    rw [← mul_assoc (2 ^ len), ← hm, h64]; ring
  rw [hN, Nat.add_mul_div_left _ _ (by positivity), ← add_assoc, Nat.add_mul_mod_self_left]

private theorem toNat_windowList (len : ℕ) (hlen : len ≤ 64) :
    ∀ (as : List (U64ExprOver F V)) (lo : ℕ),
      ((LimbsOver.windowList lo len as).eval ctx).toNat
        = limbsToNat (as.map (U64ExprOver.eval ctx)) / 2 ^ lo % 2 ^ len
  | [], lo => by simp [LimbsOver.windowList, U64ExprOver.eval, limbsToNat]
  | a :: as, lo => by
    have hmask : (UInt64.ofNat (2 ^ len - 1)).toNat = 2 ^ len - 1 :=
      toNat_ofNat_of_lt (by have := pow_le_two_pow_64 hlen; have := Nat.one_le_two_pow (n := len); omega)
    have hdvd : 2 ^ len ∣ 2 ^ 64 := pow_dvd_pow 2 hlen
    have hA := UInt64.toNat_lt (a.eval ctx)
    by_cases h64 : 64 ≤ lo
    · simp only [LimbsOver.windowList, h64, ↓reduceIte, List.map_cons]
      rw [toNat_windowList len hlen as (lo - 64), limbsToNat_cons_div h64]
    · simp only [LimbsOver.windowList, h64, ↓reduceIte, List.map_cons, limbsToNat]
      -- the next limb and the limbs above it
      obtain ⟨B, R, hrest, hB⟩ : ∃ B R : ℕ,
          limbsToNat (as.map (U64ExprOver.eval ctx)) = B + 2 ^ 64 * R ∧
            ((as.headD (.const 0)).eval ctx).toNat = B := by
        cases as with
        | nil => exact ⟨0, 0, by simp [limbsToNat], by simp [U64ExprOver.eval]⟩
        | cons b bs =>
          exact ⟨(b.eval ctx).toNat, limbsToNat (bs.map (U64ExprOver.eval ctx)),
            by simp [limbsToNat], rfl⟩
      rw [hrest, window_digits (by omega) hlen]
      by_cases h0 : lo = 0
      · subst h0
        simp only [↓reduceIte, U64ExprOver.eval, UInt64.toNat_and, hmask,
          Nat.and_two_pow_sub_one_eq_mod, pow_zero, Nat.div_one, Nat.sub_zero]
        obtain ⟨m, hm⟩ := hdvd
        rw [hm, mul_assoc, Nat.add_mul_mod_self_left]
      · have hshr : (UInt64.ofNat lo).toNat % 64 = lo := by
          rw [toNat_ofNat_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hshl : (UInt64.ofNat (64 - lo)).toNat % 64 = 64 - lo := by
          rw [toNat_ofNat_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        simp only [h0, ↓reduceIte, U64ExprOver.eval, UInt64.toNat_and, hmask,
          Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_add, UInt64.toNat_shiftRight,
          UInt64.toNat_shiftLeft, hshr, hshl, hB, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
        rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod, Nat.mod_mod_of_dvd _ hdvd, ← Nat.add_mod,
          Nat.mul_comm B]

@[simp, circuit_norm]
theorem LimbsOver.toNat_eval_window {n : ℕ} (a : LimbsOver F V n) (lo : ℕ) {len : ℕ}
    (hlen : len ≤ 64) :
    ((a.window lo len).eval ctx).toNat = a.toNat ctx / 2 ^ lo % 2 ^ len :=
  toNat_windowList ctx len hlen a.toList lo

end Eval
end Witgen
