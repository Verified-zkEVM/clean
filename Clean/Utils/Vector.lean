-- import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
-- import Mathlib.Data.ZMod.Basic
import Init.Data.List.Find

variable {α β : Type} {n : ℕ}

def fromList (l: List α) : Vector α l.length := ⟨ .mk l, rfl ⟩

namespace Vector
def len (_: Vector α n) : ℕ := n

def cons (a: α) (v: Vector α n) : Vector α (n + 1) :=
  ⟨ .mk (a :: v.toList), by simp ⟩

def get_eq {n} (v: Vector α n) (i: Fin n) : v.get i = v.toArray[i.val] := by
  simp only [get, List.get_eq_getElem, Fin.coe_cast]

/-- this is exactly what's needed to rewrite `v.get i` into a `List.getElem` if `n` is a concrete Nat -/
def get_eq_lt {n} [NeZero n] (v: Vector α n) (i : ℕ) (h: i < n := by norm_num) :
  v.get ((Fin.instOfNat (i:=i)).ofNat : Fin n) = v.toArray[i]'(by rw [v.size_toArray]; exact h) := by
  simp only [get_eq, OfNat.ofNat, Fin.val_ofNat', Nat.mod_eq_of_lt h]

@[simp]
theorem get_map {n} {f: α → β} {v: Vector α n} {i: Fin n} : get (map f v) i = f (get v i) := by
  simp only [get, map, Fin.coe_cast, Array.getElem_map, getElem_toArray]

attribute [simp] Vector.set

@[simp]
def set? (v: Vector α n) (i: ℕ) (a: α) : Vector α n :=
  ⟨ .mk <| v.toList.set i a, by rw [Array.size_eq_length_toList, List.length_set, ← Array.size_eq_length_toList, v.size_toArray] ⟩

@[simp]
def update (v: Vector α n) (i: Fin n) (f: α → α) : Vector α n :=
  v.set i (f (v.get i))

-- map over monad
def mapMonad {M : Type → Type} {n} [Monad M] (v : Vector (M α) n) : M (Vector α n) :=
  match (v : Vector (M α) n) with
  | ⟨ .mk [], h ⟩ => pure ⟨ #[], h ⟩
  | ⟨ .mk (a :: as), (h : as.length + 1 = n) ⟩ => do
    let hd ← a
    let tl ← mapMonad ⟨ .mk as, rfl ⟩
    pure ⟨ .mk <| hd :: tl.toList, by simp only [Array.size_toArray, List.length_cons,
      Array.length_toList, size_toArray]; exact h⟩

/- induction principle for Vector.cons -/
def induct {motive : {n: ℕ} → Vector α n → Prop}
  (nil: motive #v[])
  (cons: ∀ {n: ℕ} (a: α) (as: Vector α n), motive as → motive (cons a as))
  {n: ℕ} (v: Vector α n) : motive v :=
  match v with
  | ⟨ .mk [], h ⟩ => by
    have : n = 0 := by rw [←h, List.length_eq_zero]
    subst this
    congr
  | ⟨ .mk (a::as), h ⟩ => by
    have : as.length + 1 = n := by rw [←h, Array.size_toArray, List.length_cons]
    subst this
    have ih := induct (n:=as.length) nil cons ⟨ .mk as, rfl ⟩
    let h' : motive ⟨ .mk (a :: as), rfl ⟩ := cons a ⟨ as.toArray, rfl ⟩ ih
    congr

/- induction principle for Vector.push -/
def induct_push {motive : {n: ℕ} → Vector α n → Prop}
  (h0: motive #v[])
  (h1: ∀ {n: ℕ} {as: Vector α n} (a: α), motive as → motive (as.push a))
  {n: ℕ} (v: Vector α n) : motive v := by
  match v with
  | ⟨ .mk [], prop ⟩ =>
    have : n = 0 := by rw [←prop, List.length_eq_zero]
    subst this
    congr
  | ⟨ .mk (a::as), h ⟩ =>
    have : as.length + 1 = n := by rw [←h, Array.size_toArray, List.length_cons]
    subst this
    obtain ⟨ as', a', ih ⟩ := exists_push (xs := ⟨.mk (a :: as), rfl⟩)
    have ih' : motive as' := induct_push h0 h1 as'
    have h' := h1 a' ih'
    rwa [ih]

@[simp]
def init {n} (create: Fin n → α) : Vector α n :=
  match n with
  | 0 => #v[]
  | k + 1 =>
    (init (fun i : Fin k => create i)).push (create k)

def finRange (n : ℕ) : Vector (Fin n) n :=
  ⟨ .mk (List.finRange n), List.length_finRange n ⟩

@[simp]
def fill (n : ℕ) (a: α) : Vector α n :=
  match n with
  | 0 => #v[]
  | k + 1 => (fill k a).push a

instance [Inhabited α] {n: ℕ} : Inhabited (Vector α n) where
  default := fill n default

/-
def findIdx?_base {n: ℕ} (p : α → Bool) : Vector α n → (start : ℕ := 0) → Option ℕ
| ⟨ .mk [], _ ⟩, _ => none
| ⟨ .mk (a::as), _⟩, i => if p a then some i else findIdx?_base (n:=as.length) p ⟨ as, rfl ⟩ (i + 1)

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
-/

-- some simp tagging because we use Vectors a lot
attribute [simp] Vector.append Vector.get Array.getElem_append
end Vector

def Vector.Matrix (α : Type) (n m: ℕ) := Vector (Vector α m) n

namespace Vector.Matrix
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
def update (A: Matrix α n m) (i: Fin n) (j: Fin m) (f: α → α) : Matrix α n m :=
  A.set i j (f (A.get i j))

@[simp]
def fill (n: ℕ) (m : ℕ) (a: α) : Matrix α n m := Vector.fill n (.fill m a)

@[simp]
def map {α β: Type} (f: α → β) : Matrix α n m → Matrix β n m := Vector.map (Vector.map f)

/-
def findIdx? {n m: ℕ} (matrix : Matrix α n m) (prop : α → Bool) : Option (Fin n × Fin m) :=
  match matrix with
  | ⟨ .mk [], _ ⟩ => none
  | ⟨ .mk (row :: rest), (h_rest : rest.length + 1 = n) ⟩ =>
    match row.findIdx? prop with
    | some j => some (⟨ rest.length, h_rest ▸ lt_add_one _⟩, j)
    | none =>
      (findIdx? ⟨ rest, rfl ⟩ prop).map
        (fun ⟨i, j⟩ => (h_rest ▸ i.castSucc, j))
-/
end Vector.Matrix
