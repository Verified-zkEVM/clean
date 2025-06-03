-- goals:
-- define prime numbers, prove enough basic theorems
-- to show the numbers 0,...,p-1 for p prime are a field

import Mathlib.Data.Nat.GCD.Basic

def prime (p : Nat) :=
  (p ≠ 0) ∧ (p ≠ 1) ∧
  ∀ x : Nat, (x ∣ p) → (x = 1) ∨ (x = p)

def prime' (p : Nat) :=
  (p ≠ 0) ∧ (p ≠ 1) ∧
  ∀ a b : Nat, (p ∣ a*b) → (p ∣ a) ∨ (p ∣ b)

theorem prime_eq_prime' : ∀ p : ℕ, prime p ↔ prime' p := by
  intro p
  constructor
  · rintro ⟨pz, p1, h⟩
    exact ⟨pz, p1, fun a b hab =>
      if pa : p ∣ a then .inl pa else
        match h (Nat.gcd p a) (Nat.gcd_dvd_left _ _) with
        | .inl h1 => .inr (Nat.Coprime.dvd_of_dvd_mul_left h1 hab)
        | .inr h2 => absurd (h2 ▸ Nat.gcd_dvd_right _ _) pa⟩
  · rintro ⟨pz, p1, h⟩
    exact ⟨pz, p1, fun x ⟨k, pk⟩ =>
      match h x k (by rw [pk]) with
      | .inl px => .inr (Nat.dvd_antisymm ⟨k, pk⟩ px)
      | .inr ⟨m, km⟩ =>
        have p_pos := Nat.pos_of_ne_zero pz
        have : x * m * p = 1 * p := by rw [Nat.mul_assoc, Nat.mul_comm m p, ←km, pk, Nat.one_mul]
        .inl (Nat.eq_one_of_mul_eq_one_right (Nat.eq_of_mul_eq_mul_right p_pos this))⟩

noncomputable def prime_def_eq_prime'_def : prime = prime' :=
  funext (fun p => propext (prime_eq_prime' p))

structure Prime where
  val : Nat
  prime : prime val

namespace Prime
  instance coeToNat : CoeOut Prime Nat :=
    ⟨fun v => v.val⟩

  theorem gt_0 (p : Prime) : p.val > 0 :=
    (p.prime.left : p.val ≠ 0) |> Nat.pos_of_ne_zero

  -- lemma: primes are > 1
  -- TODO can we simplify this?
  theorem gt_1 (p : Prime) : p.val > 1 := by
    have ne_1 : p.val ≠ 1 := p.prime.right.left
    have le_1 : 1 ≤ p.val := p.gt_0 |> Nat.succ_le_of_lt
    cases (Nat.lt_or_eq_of_le le_1) with
    | inl lt_1 => assumption
    | inr eq_1 => exact absurd (Eq.symm eq_1) ne_1
end Prime

structure Field (p : Prime) where
  val : Nat
  less : val < p.val

namespace Field
  variable {p : Prime} (x y z : Field p) (m n : Nat)

  -- taking a number mod p produces something < p
  theorem mod_smaller (x : Nat) : x % p < p := Nat.mod_lt x p.gt_0

  /--
  create a field element from a Nat, taking the number mod p.
  -/
  def create (x : Nat) : Field p :=
    mk (x % p) (mod_smaller x)

  instance ofNat : OfNat (Field p) n where
    ofNat := create n

  instance coeToNat : CoeOut (Field p) Nat :=
    ⟨fun v => v.val⟩

  instance : ToString (Field p) where
    toString x := Nat.repr x.val

  /--
  a simple proof strategy for algebraic identities in the field is to lift them to Nat,
  i.e. `x + y = y + x` for all Fields holds because `(x + y) % p = (y + x) % p` for all Nats.

  to execute that strategy, we always start with `ext; simp;`:
    1. `ext` reduces to an identity on the values `(x + y).val = (y + x).val`
    2. `simp` is equipped with lemmas that expand field ops, like `(x + y).val = (x.val + y.val) % p`
    3. we end up with something like `(x.val + y.val) % p = (y.val + x.val) % p` which is just `Nat.add_comm`
  -/
  @[ext] theorem ext {x y : Field p} (h : (x : Nat) = y) : x = y :=
    -- proof taken from Fin.ext
    match x, y, h with
    | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

  -- constants
  def zero : Field p := 0
  def one : Field p := 1

  @[simp] theorem zero_val : (0 : Field p).val = 0 := rfl
  @[simp] theorem one_val : (1 : Field p).val = 1 := Nat.mod_eq_of_lt p.gt_1
  @[simp] theorem one_mod : 1 % p.val = 1 := Nat.mod_eq_of_lt p.gt_1

  -- create preserves field elements

  -- helpers for ext; simp
  @[simp] theorem create_val : (@create p n).val = n % p := rfl
  @[simp] theorem mod_noop : x.val % p = x.val := Nat.mod_eq_of_lt x.less

  theorem create_eq : x = create x.val := by ext; simp

  -- addition

  instance : Add (Field p) where
    add x y := x.val + y.val |> create

  -- simp expands addition
  @[simp] theorem add_val : (x + y).val = (x.val + y.val) % p := by rfl

  -- create preserves addition
  theorem create_add : create n + create m = @create p (n + m) := by ext; simp

  -- addition: neutral element
  theorem add_zero : x + 0 = x := by ext; simp
  theorem zero_add : 0 + x = x := by ext; simp

  -- addition: commutative
  theorem add_comm : x + y = y + x := by
    ext; simp; rw [Nat.add_comm]

  -- addition: associative
  theorem add_assoc : x + y + z = x + (y + z) := by
    ext; simp; rw [Nat.add_assoc]

  -- additive inverse

  instance : Neg (Field p) where
    neg x := p - x.val |> create

  instance : Sub (Field p) where
    sub x y := x.val + (p - y.val) |> create

  @[simp] theorem neg_val : (-x).val = (p - x.val) % p := rfl
  @[simp] theorem sub_val : (x - y).val = (x.val + (p - y.val)) % p := rfl

  -- helper facts for simp: x < p, x ≤ p
  @[simp] theorem lt_p : x.val < p := x.less
  @[simp] theorem le_p : x.val ≤ p := x.less |> Nat.le_of_lt

  theorem neg_add : -x + x = 0 := by ext; simp
  theorem add_neg : x + (-x) = 0 := by ext; simp
  theorem add_sub : x - x = 0 := by ext; simp
  theorem sub_def : x - y = x + (-y) := by ext; simp
  theorem neg_zero : -(0 : Field p) = 0 := by ext; simp

  -- multiplication

  instance : Mul (Field p) where
    mul x y := x.val * y.val |> create

  @[simp] theorem mul_val : (x * y).val = (x.val * y.val) % p := by rfl

  -- help simp pull out mod p (for addition this already works)
  @[simp] theorem mul_mod_right : (n * (m % p)) % p = (n * m) % p := by
    rw [Nat.mul_mod]; rw [Nat.mod_mod]; rw [Nat.mul_mod n]

  @[simp] theorem mul_mod_left : ((n % p) * m) % p = (n * m) % p := by
    rw [Nat.mul_mod]; rw [Nat.mod_mod]; rw [Nat.mul_mod n]

  -- create preserves multiplication
  theorem create_mul : create n * create m = @create p (n * m) := by ext; simp

  -- multiplication: neutral element
  theorem mul_one : x * 1 = x := by ext; simp
  theorem one_mul : 1 * x = x := by ext; simp

  -- multiplication by zero
  theorem zero_mul : 0 * x = 0 := by ext; simp
  theorem mul_zero : x * 0 = 0 := by ext; simp

  -- multiplication: commutative
  theorem mul_comm : x * y = y * x := by
    ext; simp; rw [Nat.mul_comm]

  -- multiplication: associative
  theorem mul_assoc : x * y * z = x * (y * z) := by
    ext; simp; rw [Nat.mul_assoc]

  -- multiplication: distributive
  theorem left_distrib : x * (y + z) = x * y + x * z := by
    ext; simp; rw [Nat.left_distrib]

  theorem right_distrib : (x + y) * z = x * z + y * z := by
    ext; simp; rw [Nat.right_distrib]

  -- exponentiation

  instance : NatPow (Field p) where
    -- TODO inefficient algorithm -- do we actually care?
    pow x n := x.val ^ n |> create

  @[simp] theorem pow_val : (x ^ n).val = (x.val ^ n) % p := by rfl

  theorem pow_zero : x^0 = 1 := by ext; simp
  theorem pow_one : x^1 = x := by ext; simp
  theorem square : x^2 = x * x := by ext; simp; rw [Nat.pow_two]
  theorem pow_add : x^(m + n) = x^m * x^n := by ext; simp; rw [Nat.pow_add]
  theorem cube : x^3 = x * x * x := by rw [pow_add x 2 1, square, pow_one]
end Field

-- now we have to prove enough group theory to get to little Fermat and inverses

-- lemma for manipulating equation we need below
theorem move_plus_to_right {a b : Nat} (c : Nat) (h : a + c = b) : a = (b : Int) - c := by
  rw [← h]; simp;

theorem Bezout's_Lemma (m n : Nat) : ∃ x y : Int, m*x + n*y = Nat.gcd m n := by
  induction m, n using Nat.gcd.induction with
  -- base case: `m = 0`
  | H0 n =>
    --  `gcd 0 n = n`, so `y = 1` does the job
    simp; exists 1; simp
  -- induction step: `m > 0` and we have a proof for `(n % m) * x + m * y = gcd (n % m) m`
  | H1 m n _ ih =>
    let ⟨x, y, h⟩ := ih -- unpack `∃ x y : h`
    -- we rewrite the hypothesis until it looks like what we want

    --  use `gcd m n = gcd (n % m) m`
    rw [← Nat.gcd_rec m n] at h

    -- rewrite `n % m = n - m * (n / m)`
    have n_mod_eq : ↑(n % m) = (n : Int) - ↑m * ↑(n / m) := Nat.mod_add_div n m |> move_plus_to_right (m * (n / m))
    rw [n_mod_eq] at h

    -- now it's a matter to group by m instead of x
    rw [Int.sub_mul, Int.mul_assoc] at h

    have sub_add (a b c : Int) : a - b + c = a + (c - b) := by
      rw [Int.sub_eq_add_neg, Int.add_assoc, Int.add_comm (-b), ← Int.sub_eq_add_neg]

    rw [sub_add, ← Int.mul_sub, Int.add_comm] at h

    -- now h is exactly what we want with these x and y
    exists (y - ↑(n / m) * x)
    exists x

-- to get an inverse of x mod p (for x > 0), we need to apply Bezout's Lemma to x and p, using that gcd(x, p) = 1

theorem Field.gcd_eq_1 {x : Field p} (gt_0 : x.val > 0) : Nat.gcd x p = 1 := by
  let d := Nat.gcd x p

  -- d = gcd(x,p) divides p, so it must be 1 or p
  have div_p : d ∣ p := Nat.gcd_dvd_right x p
  have eq_1_or_p : d = 1 ∨ d = p := p.prime.right.right d div_p

  -- exclude the d = p case by showing d < p
  have le_x : d ≤ x := Nat.gcd_le_left p gt_0
  have lt_p : d < p := Nat.lt_of_le_of_lt le_x x.less
  have ne_p : d ≠ p := Nat.ne_of_lt lt_p
  cases eq_1_or_p with
  | inl eq_1 => assumption
  | inr eq_p => contradiction

-- mul_mod theorem for Int, proof copied from Nat.mul_mod
theorem Int.mul_mod (a b p : Int) : a * b % p = (a % p) * (b % p) % p := by
  rw (config := {occs := .pos [1]}) [← Int.emod_add_ediv a p]
  rw (config := {occs := .pos [1]}) [← Int.emod_add_ediv b p]
  rw [Int.add_mul, Int.mul_add, Int.mul_add,
    Int.mul_assoc, Int.mul_assoc, ← Int.mul_add p, Int.add_mul_emod_self_left,
    Int.mul_comm _ (p * (b / p)), Int.mul_assoc, Int.add_mul_emod_self_left]

-- we really want simp to be good with mod p simplifications
@[simp] theorem Int.mul_mod_right' (a b p : Int) : a * (b % p) % p = a * b % p := by
  rw [Int.mul_mod, Int.emod_emod, ← Int.mul_mod]
@[simp] theorem Int.mul_mod_left' (a b p : Int) : (a % p) * b % p = a * b % p := by
  rw [Int.mul_mod, Int.emod_emod, ← Int.mul_mod]

-- how to get an inverse from Bezout's Lemma
structure BezoutPair (m n : Nat) where
  x : Int
  y : Int
  eq : m*x + n*y = Nat.gcd m n

structure Inverse (x : Field p) where
  x_inv : Field p
  eq : x * x_inv = 1

def inv_from_bezout_pair (x : Field p) (gt_0 : x.val > 0) (pair: BezoutPair x p) : Inverse x := by
  let d := Nat.gcd x p
  have d_eq_1 : d = 1 := x.gcd_eq_1 gt_0

  let ⟨ x_inv', y, (h : x * x_inv' + p * y = d)⟩ := pair

  -- simplify the Bezout equation h into an equation mod p
  have eq1 : (x * x_inv' + p * y) % p = 1 := by
    rw [h, d_eq_1, ← Int.ofNat_emod]; simp

  have eq2 : x * x_inv' % p = 1 := by
    simp at eq1; exact eq1

  -- from eq2, we only have to reinterpret the Integer x_inv as a Field element > 0
  let x_inv : Nat := Int.natAbs (x_inv' % p)

  have p_ne_0 : (p: Int) ≠ 0 := fun p_eq_0 => absurd (Int.ofNat_inj.mp p_eq_0) p.prime.left

  have inv_to_nat: x_inv = x_inv' % p := Int.natAbs_of_nonneg (Int.emod_nonneg x_inv' p_ne_0)

  -- now we can get rid of Ints and get an equation of Nats
  have eq3 : x * x_inv % p = 1 := by
    apply Int.ofNat_inj.mp -- moves goal to Int
    simp [inv_to_nat, eq2];

  -- move into the Field
  have eq4 : x * Field.create x_inv = 1 := by ext; simp [eq3];
  exact { x_inv := Field.create x_inv, eq := eq4 }

-- non-constructive inverse from non-constructive Bezout's Lemma
theorem Field.inv_exists (x : Field p) (gt_0 : x.val > 0) : ∃ x_inv : Field p, x * x_inv = 1 := by
  let ⟨ x_inv, y, existence ⟩ := Bezout's_Lemma x p
  let inv := inv_from_bezout_pair x gt_0 ⟨ x_inv, y, existence ⟩
  exact ⟨ inv.x_inv, inv.eq ⟩

-- TODO the same thing but constructive
-- "extended" gcd algorithm (Euclidean algorithm)

-- def egcd (m n : Nat) : BezoutPair m n :=
--   let rec loop (r0 r1 : Nat) (x0 x1 y0 y1 : Int) : Nat × Nat × Int × Int × Int × Int :=
--     if r1 = 0 then
--       ( r0, r1, x0, x1, y0, y1 )
--     else
--       let qotient := r0 / r1
--       let (r0, r1) : Nat × Nat := (r1, r0 - qotient * r1)
--       let (x0, x1) : Int × Int := (x1, x0 - qotient * x1)
--       let (y0, y1) : Int × Int := (y1, y0 - qotient * y1)
--       loop r0 r1 x0 x1 y0 y1
--   termination_by r0
--   decreasing_by simp_wf; apply Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _); assumption

--   let (r, _, x, y, _, _) := loop m n 1 0 0 1
--   ⟨ x, y, Nat.gcd_eq_of_bezout r m n x y ⟩
