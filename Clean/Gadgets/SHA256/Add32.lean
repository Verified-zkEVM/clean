import Clean.Gadgets.SHA256.BitwiseOps

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Gadgets.SHA256

/-!
# 32-bit Modular Addition for SHA-256

Adds two 32-bit words (as `fields 32` bit vectors, LSB first) modulo 2^32.

R1CS structure (per call):
- 32 witnesses for output bits z[0..31]
- 1  witness  for carry-out bit cout
- 32 boolean constraints: z[i] · (z[i] − 1) = 0
- 1  boolean constraint:  cout · (cout − 1) = 0
- 1  linear  constraint:  Σ a[i]·2^i + Σ b[i]·2^i = Σ z[i]·2^i + 2^32 · cout

Soundness requires the prime p to exceed 2^33 so that the linear constraint
can distinguish the intended ℕ-level relation from field wraparound.
-/

private def evalBitsNat (env : ProverEnvironment (F p)) (a : Var (fields 32) (F p)) : ℕ :=
  Finset.univ.sum fun (i : Fin 32) => (env a[i]).val * 2^i.val

/-- IR expression for the ℕ value of a vector of bit-variables: `Σ a[i].val · 2^i`
(authoring-time fold; the witness-IR counterpart of `evalBitsNat`). -/
private def bitsVal (a : Var (fields 32) (F p)) : Witgen.NExpr (F p) :=
  (List.finRange 32).foldr
    (fun i acc => a[i.val].val * (2^i.val : ℕ) + acc) 0

omit h_large in
private lemma bitsVal_eval (env : ProverEnvironment (F p)) (a : Var (fields 32) (F p)) :
    (bitsVal a).eval { env } = evalBitsNat env a := by
  rw [evalBitsNat, Fin.sum_univ_def, bitsVal, List.sum_eq_foldr, List.foldr_map]
  generalize List.finRange 32 = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, circuit_norm, ih]

/-- Add two 32-bit words mod 2^32.
    Both inputs are assumed to have boolean values in each bit position. -/
def add32 (a b : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  -- Witness the lower 32 bits of the sum
  let z ← witnessVectorProgram 32 do
    let sum ← (bitsVal a + bitsVal b) % ((2^32 : ℕ) : Witgen.NExpr (F p))
    return .range 32 fun i => ((sum >>> i) % 2).toField
  -- Witness the carry-out bit
  let cout ← witness (((bitsVal a + bitsVal b) >>> 32) % 2).toField
  -- Boolean constraints on output bits
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] * (z[i] - 1))
  -- Boolean constraint on carry-out
  assertZero (cout * (cout - 1))
  -- Sum constraint: fromBits(a) + fromBits(b) = fromBits(z) + 2^32 * cout
  assertZero (fromBitsExpr a + fromBitsExpr b - fromBitsExpr z - (2^32 : F p) * cout)
  return z

namespace Add32

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  add32 input.a input.b

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = (valueBits input.a + valueBits input.b) % 2^32 ∧ Normalized z

/-!
## Helper lemmas
-/

private lemma sum_bool_lt_two_pow (n : ℕ) (f : Fin n → ℕ) (hf : ∀ i, f i ≤ 1) :
    ∑ i : Fin n, f i * 2^i.val < 2^n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
    have ihm : ∑ i : Fin m, f (Fin.castSucc i) * 2 ^ i.val < 2 ^ m :=
      ih (f ∘ Fin.castSucc) (fun i => hf _)
    have hfm : f (Fin.last m) ≤ 1 := hf _
    have hfm_bound : f (Fin.last m) * 2 ^ m ≤ 2 ^ m := by nlinarith [Nat.two_pow_pos m]
    have h2 : 2^m + 2^m = 2^(m+1) := by ring
    omega

omit h_large in
/-- valueBits of normalized bits is < 2^32 -/
private lemma valueBits_lt_two_pow (bits : Vector (F p) 32) (h : Normalized bits) :
    valueBits bits < 2^32 := by
  apply sum_bool_lt_two_pow
  intro i
  rcases h i with h0 | h1
  · simp [h0, ZMod.val_zero]
  · simp [h1, ZMod.val_one]

omit [Fact (Nat.Prime p)] h_large in
/-- The natural-number sum from fromBits equals valueBits -/
private lemma fromBits_map_val_eq_valueBits (bits : Vector (F p) 32) :
    Utils.Bits.fromBits (bits.map ZMod.val) = valueBits bits := by
  simp only [Utils.Bits.fromBits, valueBits, Fin.foldl_to_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Vector.getElem_map]
  rfl

omit h_large in
/-- fieldFromBits bits = (valueBits bits : F p) -/
private lemma fieldFromBits_eq_valueBits (bits : Vector (F p) 32) :
    Utils.Bits.fieldFromBits bits = (valueBits bits : F p) := by
  unfold Utils.Bits.fieldFromBits
  rw [fromBits_map_val_eq_valueBits]

omit h_large in
/-- fromBitsExpr evaluated at concrete inputs = (valueBits bits : F p) -/
private lemma fromBitsExpr_eval_normalized (env : Environment (F p))
    (bits_var : Var (fields 32) (F p)) (bits : Vector (F p) 32)
    (h_eval : Vector.map (Expression.eval env) bits_var = bits) :
    Expression.eval env (fromBitsExpr bits_var) = (valueBits bits : F p) := by
  show Expression.eval env (Utils.Bits.fieldFromBitsExpr bits_var) = _
  simp only [Utils.Bits.fieldFromBits_eval]
  rw [h_eval, fieldFromBits_eq_valueBits]

omit h_large in
/-- For normalized bits with p > 2^32, (fromBitsExpr bits_var).val = valueBits bits -/
private lemma fromBitsExpr_val_eq (env : Environment (F p))
    (bits_var : Var (fields 32) (F p)) (bits : Vector (F p) 32)
    (h_eval : Vector.map (Expression.eval env) bits_var = bits)
    (h_norm : Normalized bits) (hp : 2^32 < p) :
    (Expression.eval env (fromBitsExpr bits_var)).val = valueBits bits := by
  rw [fromBitsExpr_eval_normalized env bits_var bits h_eval]
  exact ZMod.val_natCast_of_lt (by linarith [valueBits_lt_two_pow bits h_norm])

omit h_large in
/-- The z output variable vector evaluates to env.get at the witness offsets -/
private lemma z_var_eval (env : Environment (F p)) (i₀ : ℕ) :
    Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))
    = Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := by
  ext i; simp [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]

omit h_large in
/-- IsBool from boolean constraint x * (x + -1) = 0 -/
private lemma isbool_of_bool_constraint {x : F p} (h : x * (x + -1) = 0) : IsBool x := by
  rwa [show x + -1 = x - 1 by ring, ← IsBool.iff_mul_sub_one] at h

omit h_large in
/-- Normalized z from boolean constraints -/
private lemma normalized_of_bool_holds (env : Environment (F p)) (i₀ : ℕ)
    (h : ∀ i : Fin 32, env.get (i₀ + i.val) * (env.get (i₀ + i.val) + -1) = 0) :
    Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) := by
  intro i
  have hi := h i
  have h_get : (Vector.ofFn fun j : Fin 32 => env.get (i₀ + j.val))[i] = env.get (i₀ + i.val) := by
    simp [Vector.getElem_ofFn]
  rw [h_get]
  exact isbool_of_bool_constraint hi

omit h_large in
/-- evalBitsNat env a = valueBits a when the variables evaluate to a -/
private lemma evalBitsNat_eq_valueBits (env : ProverEnvironment (F p))
    (a_var : Var (fields 32) (F p)) (a : fields 32 (F p))
    (h : Vector.map (Expression.eval env.toEnvironment) a_var = a) :
    evalBitsNat env a_var = valueBits a := by
  subst h
  unfold evalBitsNat valueBits
  apply Finset.sum_congr rfl
  intro i _
  simp [Vector.getElem_map]

/-- testBit equals div/mod expression -/
private lemma testBit_ite_eq (n i : ℕ) : (if n.testBit i = true then 1 else 0 : ℕ) = n / 2^i % 2 := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (n / 2^i) with h | h <;> rw [h] <;> rfl

/-- Bit decomposition: ∑ i, (n / 2^i % 2) * 2^i = n for n < 2^32 -/
private lemma bit_decomp_sum (n : ℕ) (h_n_lt : n < 2^32) :
    ∑ i : Fin 32, n / 2^i.val % 2 * 2^i.val = n := by
  conv_rhs => rw [← Utils.Bits.fromBits_toBits h_n_lt]
  unfold Utils.Bits.fromBits Utils.Bits.toBits
  rw [Fin.foldl_to_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.getElem_mapRange, testBit_ite_eq]

omit h_large in
/-- For n < 2^32 and 2^32 < p, fieldFromBits of the bit decomposition vector equals (n : F p) -/
private lemma fieldFromBits_bit_decomp (n : ℕ) (h_n_lt : n < 2^32) (hp32 : (2:ℕ)^32 < p) :
    Utils.Bits.fieldFromBits (Vector.ofFn fun i : Fin 32 => ((n / 2^i.val % 2 : ℕ) : F p)) =
    ((n : ℕ) : F p) := by
  simp only [Utils.Bits.fieldFromBits, Utils.Bits.fromBits, Fin.foldl_to_sum]
  have h_val_eq : ∀ i : Fin 32, ((Vector.ofFn fun j : Fin 32 =>
      ((n / 2^j.val % 2 : ℕ) : F p)).map ZMod.val)[i.val] = n / 2^i.val % 2 := by
    intro i
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hbit_lt : n / 2^i.val % 2 < p := by
      have : n / 2^i.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
      linarith
    exact ZMod.val_natCast_of_lt hbit_lt
  have h_sum_eq : ∑ i : Fin 32, ((Vector.ofFn fun j : Fin 32 =>
      ((n / 2^j.val % 2 : ℕ) : F p)).map ZMod.val)[i.val] * 2^i.val = n := by
    calc ∑ i : Fin 32, ((Vector.ofFn fun j : Fin 32 =>
            ((n / 2^j.val % 2 : ℕ) : F p)).map ZMod.val)[i.val] * 2^i.val
        = ∑ i : Fin 32, n / 2^i.val % 2 * 2^i.val := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h_val_eq i]
      _ = n := bit_decomp_sum n h_n_lt
  rw [h_sum_eq]

/-!
## Soundness
Soundness requires p > 2^33 so the field linear constraint can be lifted to ℕ.
-/

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [add32]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  obtain ⟨h_z_bool, h_cout_bool, h_lin⟩ := h_holds
  rw [z_var_eval env i₀]
  -- Boolean properties
  have h_z_norm : Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) :=
    normalized_of_bool_holds env i₀ h_z_bool
  have h_cout_isbool : IsBool (env.get (i₀ + 32)) :=
    isbool_of_bool_constraint h_cout_bool
  refine ⟨?_, h_z_norm⟩
  -- Numeric setup
  have h_p_large := h_large.elim
  have h33 : (2:ℕ)^33 = 2^32 + 2^32 := by norm_num
  have hp32 : (2:ℕ)^32 < p := by omega
  -- Abbreviations
  set vz := valueBits (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) with hvz_def
  set vcout := (env.get (i₀ + 32)).val with hvcout_def
  have hva_lt : valueBits input_a < 2^32 := valueBits_lt_two_pow input_a ha
  have hvb_lt : valueBits input_b < 2^32 := valueBits_lt_two_pow input_b hb
  have hvz_lt : vz < 2^32 := valueBits_lt_two_pow _ h_z_norm
  have hvcout_le : vcout ≤ 1 := by
    rcases IsBool.val_of_IsBool h_cout_isbool with h | h <;> omega
  -- Field evaluations
  have h_fa : (Expression.eval env (fromBitsExpr input_var_a)).val = valueBits input_a :=
    fromBitsExpr_val_eq env input_var_a input_a h_input_a ha hp32
  have h_fb : (Expression.eval env (fromBitsExpr input_var_b)).val = valueBits input_b :=
    fromBitsExpr_val_eq env input_var_b input_b h_input_b hb hp32
  have h_z_eval : Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
      Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := z_var_eval env i₀
  have h_fz : (Expression.eval env (fromBitsExpr
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))))).val = vz :=
    fromBitsExpr_val_eq env _ _ h_z_eval h_z_norm hp32
  -- (2^32 : F p).val = 2^32
  have h_pow32_val : (2^32 : F p).val = 2^32 := by
    have hcast : ((2^32 : ℕ) : F p) = (2^32 : F p) := by push_cast; ring
    rw [← hcast, ZMod.val_natCast_of_lt hp32]
  -- Lift h_lin from F p to ℕ
  have h_lin' : Expression.eval env (fromBitsExpr input_var_a) +
      Expression.eval env (fromBitsExpr input_var_b) =
      Expression.eval env (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) +
      (2^32 : F p) * env.get (i₀ + 32) := by
    rw [← sub_eq_zero]
    have h_ring : Expression.eval env (fromBitsExpr input_var_a) +
        Expression.eval env (fromBitsExpr input_var_b) -
        (Expression.eval env (fromBitsExpr
          (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) +
        (2^32 : F p) * env.get (i₀ + 32)) =
        Expression.eval env (fromBitsExpr input_var_a) +
        Expression.eval env (fromBitsExpr input_var_b) +
        -Expression.eval env (fromBitsExpr
          (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) +
        -((2^32 : F p) * env.get (i₀ + 32)) := by ring
    rw [h_ring]
    exact h_lin
  have h_sum_lt_p : valueBits input_a + valueBits input_b < p := by linarith
  have h_lhs_val : (Expression.eval env (fromBitsExpr input_var_a) +
      Expression.eval env (fromBitsExpr input_var_b)).val =
      valueBits input_a + valueBits input_b := by
    rw [ZMod.val_add, h_fa, h_fb]
    exact Nat.mod_eq_of_lt h_sum_lt_p
  have h_mul_le : 2^32 * vcout ≤ 2^32 := by
    calc 2^32 * vcout ≤ 2^32 * 1 := Nat.mul_le_mul_left _ hvcout_le
      _ = 2^32 := Nat.mul_one _
  have h_mul_lt : 2^32 * vcout < p := by linarith
  have h_total_lt : vz + 2^32 * vcout < p := by linarith
  have h_rhs_val : (Expression.eval env (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) +
      (2^32 : F p) * env.get (i₀ + 32)).val = vz + 2^32 * vcout := by
    rw [ZMod.val_add, ZMod.val_mul, h_fz, h_pow32_val]
    rw [Nat.mod_eq_of_lt h_mul_lt, Nat.mod_eq_of_lt h_total_lt]
  have h_nat_eq : valueBits input_a + valueBits input_b = vz + 2^32 * vcout := by
    have := congr_arg ZMod.val h_lin'
    rw [h_lhs_val, h_rhs_val] at this
    exact this
  -- Conclude: vz = (valueBits a + valueBits b) % 2^32
  rcases IsBool.val_of_IsBool h_cout_isbool with hc0 | hc1
  · rw [show vcout = 0 from hc0, Nat.mul_zero, Nat.add_zero] at h_nat_eq
    rw [← h_nat_eq]
    exact (Nat.mod_eq_of_lt (h_nat_eq ▸ hvz_lt)).symm
  · rw [show vcout = 1 from hc1, Nat.mul_one] at h_nat_eq
    omega

/-!
## Completeness
-/

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [add32]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  obtain ⟨h_env_z, h_env_cout⟩ := h_env
  obtain ⟨S, hS_def⟩ : ∃ S, S = evalBitsNat env input_var_a + evalBitsNat env input_var_b := ⟨_, rfl⟩
  simp only [bitsVal_eval, Nat.shiftRight_eq_div_pow, ← hS_def] at h_env_z h_env_cout
  have h_p_large := h_large.elim
  have h33 : (2:ℕ)^33 = 2^32 + 2^32 := by norm_num
  have hp32 : (2:ℕ)^32 < p := by linarith
  refine ⟨fun i => ?_, ?_, ?_⟩
  · -- Boolean constraint for z[i]: z[i] * (z[i] + -1) = 0
    have henv_i := h_env_z i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (S % 2^32 / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · -- Boolean constraint for cout
    rw [h_env_cout]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^32) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · -- Linear constraint: FA + FB - FZ - 2^32 * cout = 0 in F p
    -- We prove evalBitsNat env a = valueBits input_a, similarly for b
    have h_evalBits_a : evalBitsNat env input_var_a = valueBits input_a :=
      evalBitsNat_eq_valueBits env input_var_a input_a h_input_a
    have h_evalBits_b : evalBitsNat env input_var_b = valueBits input_b :=
      evalBitsNat_eq_valueBits env input_var_b input_b h_input_b
    have hS_eq : S = valueBits input_a + valueBits input_b := by
      rw [hS_def, h_evalBits_a, h_evalBits_b]
    -- valueBits bounds
    have hva_lt : valueBits input_a < 2^32 := valueBits_lt_two_pow input_a ha
    have hvb_lt : valueBits input_b < 2^32 := valueBits_lt_two_pow input_b hb
    have hS_lt_33 : S < 2^33 := by rw [hS_eq]; linarith
    -- Bit decomposition of S % 2^32: S % 2^32 = ∑ i, (S%2^32 / 2^i % 2) * 2^i
    have h_S_mod_lt : S % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
    -- S / 2^32 ∈ {0, 1} since S < 2^33
    have h_div_le : S / 2^32 ≤ 1 := by
      have hbd : S < 2 * 2^32 := by linarith
      have : S / 2^32 < 2 := (Nat.div_lt_iff_lt_mul (by norm_num)).mpr hbd
      omega
    -- so S / 2^32 % 2 = S / 2^32
    have h_div_mod : S / 2^32 % 2 = S / 2^32 := by omega
    -- Key identity: S = S%2^32 + 2^32 * (S/2^32 % 2)
    have hS_decomp : S = S % 2^32 + 2^32 * (S / 2^32 % 2) := by
      rw [h_div_mod]; exact (Nat.mod_add_div S (2^32)).symm.trans (by ring)
    -- FA = (valueBits input_a : F p)
    have h_FA : Expression.eval env.toEnvironment (fromBitsExpr input_var_a) =
        ((valueBits input_a : ℕ) : F p) :=
      fromBitsExpr_eval_normalized env.toEnvironment input_var_a input_a h_input_a
    have h_FB : Expression.eval env.toEnvironment (fromBitsExpr input_var_b) =
        ((valueBits input_b : ℕ) : F p) :=
      fromBitsExpr_eval_normalized env.toEnvironment input_var_b input_b h_input_b
    -- For FZ, compute via fieldFromBits_eval
    have h_z_eval : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) :=
      z_var_eval env.toEnvironment i₀
    -- z's evaluated bits equal Vector.ofFn (fun i => ((S%2^32/2^i%2 : ℕ) : F p))
    have h_z_eval' : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => ((S % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [h_z_eval]
      ext i hi
      simp only [Vector.getElem_ofFn]
      exact h_env_z ⟨i, hi⟩
    -- Compute FZ using the helper
    have h_FZ : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) =
        ((S % 2^32 : ℕ) : F p) := by
      show Expression.eval env.toEnvironment (Utils.Bits.fieldFromBitsExpr _) = _
      simp only [Utils.Bits.fieldFromBits_eval]
      rw [h_z_eval']
      exact fieldFromBits_bit_decomp (S % 2^32) h_S_mod_lt hp32
    -- cout value
    have h_cout_eq : env.get (i₀ + 32) = ((S / 2^32 % 2 : ℕ) : F p) := h_env_cout
    -- Combine all
    rw [h_FA, h_FB, h_FZ, h_cout_eq]
    -- Now reduce to a Nat equation cast to F p
    have hnat : valueBits input_a + valueBits input_b = S % 2^32 + 2^32 * (S / 2^32 % 2) := by
      rw [← hS_eq, ← hS_decomp]
    have hF : ((valueBits input_a : ℕ) : F p) + ((valueBits input_b : ℕ) : F p) =
              ((S % 2^32 : ℕ) : F p) + (2^32 : F p) * ((S / 2^32 % 2 : ℕ) : F p) := by
      have h := congr_arg (Nat.cast : ℕ → F p) hnat
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul] at h
      rw [show ((2^32 : ℕ) : F p) = (2^32 : F p) from by push_cast; ring] at h
      exact h
    -- Goal: ↑va + ↑vb + -↑(S%2^32) + -((2^32 : F p) * ↑(S/2^32%2)) = 0
    have rearrange : ((valueBits input_a : ℕ) : F p) + ((valueBits input_b : ℕ) : F p) +
        -((S % 2^32 : ℕ) : F p) + -((2^32 : F p) * ((S / 2^32 % 2 : ℕ) : F p)) =
        (((valueBits input_a : ℕ) : F p) + ((valueBits input_b : ℕ) : F p)) -
        (((S % 2^32 : ℕ) : F p) + (2^32 : F p) * ((S / 2^32 % 2 : ℕ) : F p)) := by ring
    rw [rearrange, hF, sub_self]

def circuit [Fact (p > 2^33)] : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Add32
end Gadgets.SHA256
end
