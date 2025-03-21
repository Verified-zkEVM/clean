import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Basic
import Mathlib.Data.ZMod.Basic

variable {α β : Type} {n : ℕ}

def Vector (α : Type) (n: ℕ) := { l: List α // l.length = n }

instance [Repr α] {n: ℕ} : Repr (Vector α n) where
  reprPrec l _ := repr l.val

@[reducible]
def vec (l: List α) : Vector α l.length := ⟨ l, rfl ⟩

namespace Vector
def len (_: Vector α n) : ℕ := n

@[ext]
theorem ext (l : ℕ) (v w: Vector α l) : v.val = w.val → v = w := by
  intro h
  cases v
  cases w
  simp only at h
  simp only [h]

@[simp]
def nil : Vector α 0 := ⟨ [], rfl ⟩

@[simp]
def cons (a: α) (v: Vector α n)  : Vector α (n + 1) :=
  ⟨ a :: v.val, by simp only [List.length_cons, v.prop] ⟩

@[simp]
def map (f: α → β) (v: Vector α n) : Vector β n :=
  ⟨ v.val.map f, by rw [List.length_map, v.prop] ⟩

def zip {n} : Vector α n → Vector β n → Vector (α × β) n
  | ⟨ [], ha ⟩, ⟨ [], _ ⟩  => ⟨ [], ha ⟩
  | ⟨ a::as, (ha : as.length + 1 = n) ⟩,
    ⟨ b::bs, (hb : bs.length + 1 = n) ⟩ =>
    let ⟨ z, hz ⟩ := zip ⟨ as, rfl ⟩ ⟨ bs, by apply Nat.add_one_inj.mp; rw [ha, hb] ⟩
    ⟨ (a, b) :: z, by show z.length + 1 = n; rw [hz, ha] ⟩

@[simp]
def get (v: Vector α n) (i: Fin n) : α :=
  let i' : Fin v.val.length := Fin.cast v.prop.symm i
  v.val.get i'

def get_eq {n} (v: Vector α n) (i: Fin n) : v.get i = v.val[i.val] := by
  simp only [get, List.get_eq_getElem, Fin.coe_cast]

/-- this is exactly what's needed to rewrite `v.get i` into a `List.getElem` if `n` is a concrete Nat -/
def get_eq_lt {n} [NeZero n] (v: Vector α n) (i : ℕ) (h: i < n := by norm_num) :
  v.get ((Fin.instOfNatOfNeZeroNat (a:=i)).ofNat : Fin n) = v.val[i]'(by rw [v.prop]; exact h) := by
  simp only [get_eq, OfNat.ofNat, Fin.val_ofNat', Nat.mod_eq_of_lt h]

@[simp]
theorem get_map {n} {f: α → β} {v: Vector α n} {i: Fin n} : get (map f v) i = f (get v i) := by
  simp only [get, map, List.get_eq_getElem, Fin.coe_cast, List.getElem_map]

@[simp]
def append {m} (v: Vector α n) (w: Vector α m) : Vector α (n + m) :=
  ⟨ v.val ++ w.val, by simp only [List.length_append, v.prop, w.prop] ⟩

@[simp]
instance instAppend {α : Type} {n : ℕ} {m : ℕ} : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) where
  hAppend xs ys := append xs ys

@[simp]
theorem append_vec (v w: List α) : vec v ++ vec w = ⟨ v ++ w, by simp [List.append] ⟩ := rfl

@[simp]
def push (v: Vector α n) (a: α) : Vector α (n + 1) :=
  ⟨ v.val ++ [a], by simp only [List.length_append, v.prop, List.length_singleton] ⟩

theorem push_of_len_succ {n: ℕ} (v: Vector α (n + 1)) : ∃ as: Vector α n, ∃ a: α, v = push as a := by
  match v with
  | ⟨ [], h ⟩ => cases h
  | ⟨ a::as, h ⟩ =>
    rcases as with _ | ⟨ a', as' ⟩
    · have : n = 0 := by simp_all only [List.length_singleton, self_eq_add_left]
      subst this
      use nil, a
      simp only [Nat.reduceAdd, push, nil, List.nil_append]
    have : as'.length + 1 = n := by simp_all only [List.length_cons, add_left_inj]
    subst this
    obtain ⟨ as'', a'', ih ⟩ := push_of_len_succ ⟨ a' :: as', rfl ⟩
    use cons a as'', a''
    apply ext
    simp only [push, cons, List.cons_append, List.cons.injEq, true_and]
    exact congrArg Subtype.val ih

-- map over monad
def mapM {M : Type → Type} {n} [Monad M] (v : Vector (M α) n) : M (Vector α n) :=
  match (v : Vector (M α) n) with
  | ⟨ [], h ⟩ => pure ⟨ [], h ⟩
  | ⟨ a :: as, (h : as.length + 1 = n) ⟩ => do
    let hd ← a
    let tl ← mapM ⟨ as, rfl ⟩
    pure ⟨ hd :: tl.val, by rwa [List.length_cons, tl.prop]⟩

/- induction principle for Vector.cons -/
def induct {motive : {n: ℕ} → Vector α n → Prop}
  (h0: motive nil)
  (h1: ∀ {n: ℕ} (a: α) {as: Vector α n}, motive as → motive (cons a as))
  {n: ℕ} (v: Vector α n) : motive v := by
  match v with
  | ⟨ [], prop ⟩ =>
    have : n = 0 := by rw [←prop, List.length_eq_zero]
    subst this
    congr
  | ⟨ a::as, h ⟩ =>
    have : as.length + 1 = n := by rw [←h, List.length_cons]
    subst this
    have ih := induct (n:=as.length) h0 h1 ⟨ as, rfl ⟩
    let h' : motive ⟨ a :: as, rfl ⟩ := h1 a ih
    congr

/- induction principle for Vector.push -/
def induct_push {motive : {n: ℕ} → Vector α n → Prop}
  (h0: motive nil)
  (h1: ∀ {n: ℕ} {as: Vector α n} (a: α), motive as → motive (as.push a))
  {n: ℕ} (v: Vector α n) : motive v := by
  match v with
  | ⟨ [], prop ⟩ =>
    have : n = 0 := by rw [←prop, List.length_eq_zero]
    subst this
    congr
  | ⟨ a::as, h ⟩ =>
    have : as.length + 1 = n := by rw [←h, List.length_cons]
    subst this
    obtain ⟨ as', a', ih ⟩ := push_of_len_succ ⟨ a :: as, rfl ⟩
    have ih' : motive as' := induct_push h0 h1 as'
    have h' := h1 a' ih'
    rwa [ih]

@[simp]
def init {n} (create: Fin n → α) : Vector α n :=
  match n with
  | 0 => nil
  | k + 1 =>
    (init (fun i : Fin k => create i)).push (create k)

def finRange (n : ℕ) : Vector (Fin n) n :=
  ⟨ List.finRange n, List.length_finRange n ⟩

def fill (n : ℕ) (a: α) : Vector α n :=
  match n with
  | 0 => nil
  | k + 1 => (fill k a).push a

instance [Inhabited α] {n: ℕ} : Inhabited (Vector α n) where
  default := fill n default
end Vector
