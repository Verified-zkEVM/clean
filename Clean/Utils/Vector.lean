import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Basic
import Mathlib.Data.ZMod.Basic
import Init.Data.List.Find

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
def cons (a: α) (v: Vector α n) : Vector α (n + 1) :=
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

@[simp]
def set (v: Vector α n) (i: Fin n) (a: α) : Vector α n :=
  ⟨ v.val.set i a, by rw [List.length_set, v.prop] ⟩

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
  (nil: motive nil)
  (cons: ∀ {n: ℕ} (a: α) (as: Vector α n), motive as → motive (cons a as))
  {n: ℕ} (v: Vector α n) : motive v := by
  match v with
  | ⟨ [], prop ⟩ =>
    have : n = 0 := by rw [←prop, List.length_eq_zero]
    subst this
    congr
  | ⟨ a::as, h ⟩ =>
    have : as.length + 1 = n := by rw [←h, List.length_cons]
    subst this
    have ih := induct (n:=as.length) nil cons ⟨ as, rfl ⟩
    let h' : motive ⟨ a :: as, rfl ⟩ := cons a ⟨ as, rfl ⟩ ih
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

@[simp]
def fill (n : ℕ) (a: α) : Vector α n :=
  match n with
  | 0 => nil
  | k + 1 => (fill k a).push a

instance [Inhabited α] {n: ℕ} : Inhabited (Vector α n) where
  default := fill n default

@[reducible]
def find? (v: Vector α n) (p: α → Bool) : Option α :=
  v.val.find? p

def findIdx?_base {n: ℕ} (p : α → Bool) : Vector α n → (start : ℕ := 0) → Option ℕ
| ⟨ [], _ ⟩, _ => none
| ⟨ a::as, _⟩, i => if p a then some i else findIdx?_base (n:=as.length) p ⟨ as, rfl ⟩ (i + 1)

lemma findIdx?_cons {n: ℕ} (p : α → Bool) (a: α) (as: Vector α n) (i: ℕ) :
  findIdx?_base p (cons a as) i = if p a then some i else findIdx?_base p as (i + 1) := by
  simp only [cons, findIdx?_base]
  congr <;> simp

lemma findIdx?_lt {n: ℕ} (p : α → Bool) (v: Vector α n) :
  ∀ start i, findIdx?_base p v start = some i → i < start + n := by
  induction v using induct with
  | nil => intro _ _ h; simp [findIdx?_base] at h
  | cons a as ih =>
    intro start i h
    rw [findIdx?_cons] at h
    by_cases ha : p a
    · simp [ha] at h; rw [h]; simp
    simp [ha] at h
    specialize ih (start + 1) i h
    linarith

def findIdx? {n: ℕ} (p : α → Bool) (v: Vector α n) : Option (Fin n) :=
  let i? := findIdx?_base p v 0
  if h : Option.isSome i? then
    let i := i?.get h
    some ⟨ i, by
      have : findIdx?_base p v = some i := by simp [i]
      have h := findIdx?_lt p v 0 i this
      simpa using h
    ⟩
  else none
end Vector

def Matrix (α : Type) (n m: ℕ) := Vector (Vector α m) n

namespace Matrix
variable {α β : Type} {n m : ℕ}

@[simp]
def get (A: Matrix α n m) (i: Fin n) (j: Fin m) : α := Vector.get A i |>.get j

def getRow (A: Matrix α n m) (i: Fin n) : Vector α m := .get A i

@[simp]
def set (A: Matrix α n m) (i: Fin n) (j: Fin m) (value : α) : Matrix α n m :=
  Vector.set A i (Vector.get A i |>.set j value)

def setRow (A: Matrix α n m) (i: Fin n) (row: Vector α m) : Matrix α n m :=
  Vector.set A i row

@[simp]
def fill (n: ℕ) (m : ℕ) (a: α) : Matrix α n m := .fill n (.fill m a)

@[simp]
def map {α β: Type} (f: α → β) : Matrix α n m → Matrix β n m := Vector.map (Vector.map f)

def findIdx? {n m: ℕ} (matrix : Matrix α n m) (prop : α → Bool) : Option (Fin n × Fin m) :=
  match matrix with
  | ⟨ [], _ ⟩ => none
  | ⟨ row :: rest, (h_rest : rest.length + 1 = n) ⟩ =>
    match row.findIdx? prop with
    | some j => some (⟨ rest.length, h_rest ▸ lt_add_one _⟩, j)
    | none =>
      (findIdx? ⟨ rest, rfl ⟩ prop).map
        (fun ⟨i, j⟩ => (h_rest ▸ i.castSucc, j))
end Matrix
