import Mathlib.Tactic
import Init.Data.List.Find

variable {α β : Type} {n m : ℕ}

def fromList (l: List α) : Vector α l.length := ⟨ .mk l, rfl ⟩

namespace Vector
def len (_: Vector α n) : ℕ := n

def cons (a: α) (v: Vector α n) : Vector α (n + 1) :=
  ⟨ .mk (a :: v.toList), by simp ⟩

theorem toList_cons {a: α} {v: Vector α n} : (cons a v).toList = a :: v.toList := by
  simp [cons]

def get_eq {n} (v: Vector α n) (i: Fin n) : v.get i = v.toArray[i.val] := by
  simp only [get, List.get_eq_getElem, Fin.coe_cast]

/-- this is exactly what's needed to rewrite `v.get i` into a `List.getElem` if `n` is a concrete Nat -/
def get_eq_lt {n} [NeZero n] (v: Vector α n) (i : ℕ) (h: i < n := by norm_num) :
  v.get ((Fin.instOfNat (i:=i)).ofNat : Fin n) = v.toArray[i]'(by rw [v.size_toArray]; exact h) := by
  simp only [get_eq, OfNat.ofNat, Fin.val_ofNat', Nat.mod_eq_of_lt h]

@[simp]
theorem get_map {n} {f: α → β} {v: Vector α n} {i: Fin n} : get (map f v) i = f (get v i) := by
  simp only [get, map, Fin.coe_cast, Array.getElem_map, getElem_toArray]

@[simp]
def set? (v: Vector α n) (i: ℕ) (a: α) : Vector α n :=
  ⟨ .mk <| v.toList.set i a, by rw [Array.size_eq_length_toList, List.length_set, ← Array.size_eq_length_toList, v.size_toArray] ⟩

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
universe u

def induct {motive : {n: ℕ} → Vector α n → Sort u}
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

structure ToPush (v : Vector α (n + 1)) where
  as : Vector α n
  a : α
  h : v = as.push a

def to_push (v : Vector α (n + 1)) : ToPush v where
  as := v.take n |>.cast Nat.min_add_right
  a := v[n]
  h := by rcases v with ⟨ ⟨xs⟩, h ⟩; simp_all

/- induction principle for Vector.push -/
def induct_push {motive : {n: ℕ} → Vector α n → Sort u}
  (nil: motive #v[])
  (push: ∀ {n: ℕ} (as: Vector α n) (a: α), motive as → motive (as.push a))
  {n: ℕ} (v: Vector α n) : motive v := by
  match v with
  | ⟨ .mk [], prop ⟩ =>
    have : n = 0 := by rw [←prop, List.length_eq_zero]
    subst this
    congr
  | ⟨ .mk (a::as), h ⟩ =>
    have : as.length + 1 = n := by rw [←h, Array.size_toArray, List.length_cons]
    subst this
    obtain ⟨ as', a', ih ⟩ := to_push ⟨.mk (a :: as), rfl⟩
    have ih' : motive as' := induct_push nil push as'
    have h' := push _ a' ih'
    rwa [ih]

@[simp]
def init {n} (create: Fin n → α) : Vector α n :=
  match n with
  | 0 => #v[]
  | k + 1 =>
    (init (fun i : Fin k => create i)).push (create k)

theorem cast_init {n} {create: Fin n → α} (h : n = m) :
    init create = (init (n:=m) (fun i => create (i.cast h.symm))).cast h.symm := by
  subst h; simp

@[simp]
def natInit (n: ℕ) (create: ℕ → α) : Vector α n :=
  match n with
  | 0 => #v[]
  | k + 1 => natInit k create |>.push (create k)

theorem cast_natInit {n} {create: ℕ → α} (h : n = m) :
    natInit n create = (natInit m create).cast h.symm := by
  subst h; simp

theorem natInit_succ {n} {create: ℕ → α} :
    natInit (n + 1) create = (natInit n create).push (create n) := rfl

theorem natInit_add_eq_append {n m} (create: ℕ → α) :
    natInit (n + m) create = natInit n create ++ natInit m (fun i => create (n + i)) := by
  induction m with
  | zero => simp only [Nat.add_zero, natInit, append_empty]
  | succ m ih => simp only [natInit, Nat.add_eq, append_push, ih]

def finRange (n : ℕ) : Vector (Fin n) n :=
  ⟨ .mk (List.finRange n), List.length_finRange n ⟩

@[simp]
def fill (n : ℕ) (a: α) : Vector α n :=
  match n with
  | 0 => #v[]
  | k + 1 => (fill k a).push a

instance [Inhabited α] {n: ℕ} : Inhabited (Vector α n) where
  default := fill n default

-- some simp tagging because we use Vectors a lot
attribute [simp] Vector.append Vector.get Array.getElem_append

-- two complementary theorems about `Vector.take` and `Vector.drop` on appended vectors
theorem cast_take_append_of_eq_length {v : Vector α n} {w : Vector α m} :
    (v ++ w |>.take n |>.cast Nat.min_add_right) = v := by
  have hv_length : v.toList.length = n := by rw [Array.length_toList, size_toArray]
  rw [cast_mk, ←toArray_inj, take_eq_extract, toArray_extract, toArray_append,
    ← Array.toArray_toList (_ ++ _), List.extract_toArray, Array.toList_append,
    List.extract_eq_drop_take, List.drop_zero, Nat.sub_zero,
    List.take_append_of_le_length (Nat.le_of_eq hv_length.symm),
    List.take_of_length_le (Nat.le_of_eq hv_length), List.toArray_toList]

theorem cast_drop_append_of_eq_length {v : Vector α n} {w : Vector α m} :
    (v ++ w |>.drop n |>.cast (Nat.add_sub_self_left n m)) = w := by
  have hv_length : v.toList.length = n := by rw [Array.length_toList, size_toArray]
  have hw_length : w.toList.length = m := by rw [Array.length_toList, size_toArray]
  rw [drop_eq_cast_extract, cast_cast, cast_mk, ←toArray_inj, toArray_extract, toArray_append,
    ← Array.toArray_toList (_ ++ _), List.extract_toArray, Array.toList_append,
    List.extract_eq_drop_take, Nat.add_sub_self_left,
    List.drop_append_of_le_length (Nat.le_of_eq hv_length.symm),
    List.drop_of_length_le (Nat.le_of_eq hv_length), List.nil_append,
    List.take_of_length_le (Nat.le_of_eq hw_length), List.toArray_toList]
end Vector

-- helpers for `Vector.toChunks`

/--
The composition `n * m = m + ... + m` (where `m > 0`)
-/
def Composition.ofProductLength (m: ℕ+) {α : Type} {l : List α} (hl : l.length = n * m.val) : Composition l.length := {
  blocks := List.replicate n m.val
  blocks_pos hi := (List.mem_replicate.mp hi).right ▸ m.pos
  blocks_sum := hl ▸ List.sum_replicate_nat _ _
}

theorem Composition.ofProductLength_mem_length {m: ℕ+} {α : Type} {l : List α} {hl : l.length = n * m.val}
  (comp : Composition l.length) (hcomp : comp = Composition.ofProductLength m hl) :
  ∀ li ∈ l.splitWrtComposition comp, li.length = m := by
  intro li hli
  let l_split := l.splitWrtComposition comp
  have hli_length : li.length ∈ l_split.map List.length := List.mem_map_of_mem _ hli
  have hli_length_replicate : li.length ∈ List.replicate n m.val := by
    have map_length := List.map_length_splitWrtComposition l comp
    rw [map_length, hcomp, Composition.ofProductLength] at hli_length
    exact hli_length
  exact List.mem_replicate.mp hli_length_replicate |>.right

namespace Vector
/-- Split a vector into equally-sized chunks. -/
def toChunks (m: ℕ+) {α : Type} (v : Vector α (n*m)) : Vector (Vector α m) n :=
  let comp := Composition.ofProductLength m v.length_toList
  let list : List (Vector α m) := v.toList.splitWrtComposition comp
    |>.attachWith (List.length · = m) (comp.ofProductLength_mem_length rfl)
    |>.map fun ⟨ l, hl ⟩ => .mk (.mk l) hl
  .mk (.mk list) (by
    simp only [Array.length_toList, Composition.ofProductLength, Array.size_toArray,
      List.length_map, List.length_attachWith, List.length_splitWrtComposition, list, comp]
    rw [←Composition.blocks_length, List.length_replicate]
  )

theorem toChunks_flatten {α : Type} (m: ℕ+) (v : Vector α (n*m)) :
    (v.toChunks m).flatten = v := by
  -- simp can reduce the statement to lists and use `List.flatten_splitWrtComposition`!
  simp [toChunks]

theorem flatten_toChunks {α : Type} (m: ℕ+) (v : Vector (Vector α m) n) :
    v.flatten.toChunks m = v := by
  simp only [toChunks]
  rw [←Vector.toArray_inj,←Array.toList_inj]
  simp only
  let v_list_list := v.toList.map (Array.toList ∘ toArray)
  have h_flatten : v.flatten.toList = v_list_list.flatten := by
    rw [Vector.flatten_mk, Array.toList_flatten, Array.toList_map, List.map_map]
  have h_length : v.flatten.toList.length = n * ↑m := by rw [Array.length_toList, size_toArray]
  have h_flatten_length : v_list_list.flatten.length = n * ↑m := by rw [←h_flatten, h_length]
  have h' : (v.flatten.toList.splitWrtComposition (Composition.ofProductLength m h_length)) = v_list_list := by
    rw [← v_list_list.splitWrtComposition_flatten (Composition.ofProductLength m h_flatten_length)]
    congr 1
    · rw [h_length, h_flatten_length]
    congr
    · simp [h_flatten]
    simp only [List.map_map, Composition.ofProductLength, v_list_list]
    clear *-
    induction v using Vector.induct
    case nil => rfl
    case cons xs x hi => rw [List.replicate_succ, Vector.toList_cons, List.map_cons, hi,
      Function.comp_apply, Function.comp_apply, Array.length_toList, size_toArray]
  simp only [h', v_list_list]
  rw [List.map_attachWith, List.pmap_map]
  simp

-- using the above, it's quite easy to prove theorems about `toChunks` from similar theorems about `flatten`!
theorem toChunks_push (m: ℕ+) {α : Type} (vs : Vector α (n*m)) (v : Vector α m) :
    have h : n * m + m = (n + 1) * m := by simp [add_mul];
    (vs.toChunks m).push v = ((vs ++ v).cast h).toChunks m := by
  simp only
  rw [Vector.eq_iff_flatten_eq, toChunks_flatten, flatten_push, toChunks_flatten]

theorem mapM_singleton (a : α) {m : Type → Type} [Monad m] [LawfulMonad m] (f : α → m β) :
    #v[a].mapM f = (do pure #v[←f a]) := by
  simp [mapM, mapM.go]

theorem mapM_push (as : Vector α n) {m : Type → Type} [Monad m] [LawfulMonad m] [Nonempty β] (f : α → m β) (a : α) :
    (as.push a).mapM f = (do
      let bs ← as.mapM f
      let b ← f a
      pure (bs.push b)) := by
  rw [←append_singleton, mapM_append, mapM_singleton]
  simp only [bind_pure_comp, Functor.map_map, append_singleton]
end Vector
