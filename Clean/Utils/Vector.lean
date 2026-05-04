import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.Enumerative.Composition
import Init.Data.List.Find

variable {α β : Type} {n m : ℕ}

open Vector (finRange)

namespace Vector
def fromList (l : List α) : Vector α l.length := ⟨ .mk l, rfl ⟩

def len (_ : Vector α n) : ℕ := n

-- Helper lemma: A vector of length 1 has toList = [v[0]]
theorem toList_length_one {α : Type} (v : Vector α 1) :
    v.toList = [v[0]] := by
  -- Try using cases on the vector
  cases v using Vector.casesOn with
  | mk arr h =>
      cases arr using Array.casesOn with
      | mk lst =>
        -- h says arr.size = 1, and arr = Array.mk lst
        -- So lst.length = 1
        simp only [List.size_toArray] at h
        -- Now we know lst has length 1, so it must be [x] for some x
        match lst with
        | [] => simp at h
        | [x] =>
          -- Goal: v.toList = [v.get 0]
          -- v.toList = arr.toList = lst = [x]
          -- v.get 0 = arr[0] = lst[0] = x
          rfl
        | _ :: _ :: _ => simp [List.length] at h

-- Helper lemma: A vector of length 2 has toList = [v[0], v[1]]
theorem toList_length_two {α : Type} (v : Vector α 2) :
    v.toList = [v[0], v[1]] := by
  -- Use the same approach as for length 1
  cases v using Vector.casesOn with
  | mk arr h =>
      cases arr using Array.casesOn with
      | mk lst =>
        simp only [List.size_toArray] at h
        match lst with
        | [] => simp at h
        | [_] => simp [List.length] at h
        | [x, y] => rfl
        | _ :: _ :: _ :: _ => simp [List.length] at h

def listCons (a : α) (v : Vector α n) : Vector α (n + 1) :=
  ⟨ .mk (a :: v.toList), by simp ⟩

theorem toList_listCons {a : α} {v : Vector α n} : (listCons a v).toList = a :: v.toList := by
  simp [listCons]

def set? (v : Vector α n) (i : ℕ) (a : α) : Vector α n :=
  ⟨ .mk <| v.toList.set i a, by rw [Array.size_eq_length_toList, List.length_set, length_toList] ⟩

def update (v : Vector α n) (i : Fin n) (f : α → α) : Vector α n :=
  v.set i (f (v.get i))

-- map over monad
def mapMonad {M : Type → Type} {n} [Monad M] (v : Vector (M α) n) : M (Vector α n) :=
  match (v : Vector (M α) n) with
  | ⟨ .mk [], h ⟩ => pure ⟨ #[], h ⟩
  | ⟨ .mk (a :: as), (h : as.length + 1 = n) ⟩ => do
    let hd ← a
    let tl ← mapMonad ⟨ .mk as, rfl ⟩
    pure ⟨ .mk <| hd :: tl.toList, by simpa using h⟩

theorem cast_heq {v : Vector α n} (h : n = m) : HEq (v.cast h) v := by
  subst h
  rw [heq_eq_eq, cast_rfl]

theorem heq_cast {v : Vector α n} (h : n = m) : HEq v (v.cast h) := by
  subst h
  rw [heq_eq_eq, cast_rfl]

/- induction principle for Vector.cons -/
universe u

def induct {motive : {n : ℕ} → Vector α n → Sort u}
    (nil : motive #v[])
    (cons: ∀ {n : ℕ} (a : α) (as : Vector α n), motive as → motive (listCons a as))
    {n : ℕ} (v : Vector α n) : motive v :=
  match v with
  | ⟨ .mk [], h ⟩ => by
    have : n = 0 := by rw [←h, List.size_toArray, List.length_nil]
    subst this
    congr
  | ⟨ .mk (a :: as), h ⟩ => by
    have : as.length + 1 = n := by rw [←h, List.size_toArray, List.length_cons]
    subst this
    have ih := induct (n:=as.length) nil cons ⟨ .mk as, rfl ⟩
    let h' : motive ⟨ .mk (a :: as), rfl ⟩ := cons a ⟨ as.toArray, rfl ⟩ ih
    congr

def toPush (v : Vector α (n + 1)) :
    (as : Vector α n) ×' (a : α) ×' (as.push a = v) :=
  ⟨ v.pop, v.back, v.push_pop_back ⟩

/- induction principle for Vector.push -/
def inductPush {motive : {n : ℕ} → Vector α n → Sort u}
  (nil : motive #v[])
  (push: ∀ {n : ℕ} (as : Vector α n) (a : α), motive as → motive (as.push a))
  {n : ℕ} (v : Vector α n) : motive v :=
  match v with
  | ⟨ .mk [], (h : 0 = n) ⟩ =>
    cast (by subst h; rfl) nil
  | ⟨ .mk (a :: as), h ⟩ =>
    have hlen : as.length + 1 = n := by rw [←h, List.size_toArray, List.length_cons]
    let ⟨ as', a', is_push ⟩ := toPush ⟨.mk (a :: as), rfl⟩
    cast (by subst hlen; rw [is_push]) (push as' a' (inductPush nil push as'))

theorem empty_push (x : α) : #v[].push x = #v[x] := by rfl

theorem listCons_push (x y : α) (xs : Vector α n) :
    (listCons x xs).push y = listCons x (xs.push y) := by rfl

theorem inductPush_nil {motive : {n : ℕ} → Vector α n → Sort u}
  {nil : motive #v[]}
  {push : ∀ {n : ℕ} (as : Vector α n) (a : α), motive as → motive (as.push a)} :
    inductPush nil push #v[] = nil := by simp only [inductPush]; rfl

lemma inductPush_listCons_push {motive : {n : ℕ} → Vector α n → Sort u}
  {nil : motive #v[]}
  {push' : ∀ {n : ℕ} (as : Vector α n) (a : α), motive as → motive (as.push a)}
  {n : ℕ} (xs : Vector α n) (x a : α) :
    inductPush nil push' (listCons x (xs.push a)) =
      push' (listCons x xs) a (inductPush nil push' (listCons x xs)) := by
  conv => lhs; simp only [listCons, inductPush]
  apply (cast_eq_iff_heq).mpr
  have h_push_len : (xs.push a).toList.length = n + 1 := by simp
  have h_to_push_cons :
      HEq (toPush ⟨.mk (x :: (xs.push a).toList), rfl⟩).1 (listCons x xs) := by
    have : (toPush ⟨.mk (x :: (xs.push a).toList), rfl⟩).1 =
        (listCons x xs).cast h_push_len.symm := by
      simp [listCons, toPush, toList_push, List.dropLast]
    rw [this]; apply cast_heq
  congr
  · have : (toPush ⟨.mk (x :: (xs.push a).toList), rfl⟩).2.1 = a := by
      simp [toPush, toList_push]
    rw [this]

theorem inductPush_push {motive : {n : ℕ} → Vector α n → Sort u}
  {nil : motive #v[]}
  {push : ∀ {n : ℕ} (as : Vector α n) (a : α), motive as → motive (as.push a)}
  {n : ℕ} (as : Vector α n) (a : α) :
    inductPush nil push (as.push a) = push as a (inductPush nil push as) := by
  induction as using Vector.induct
  case nil =>
    suffices inductPush nil push #v[a] = push #v[] a (inductPush nil push #v[]) by congr
    simp only [inductPush, List.length_nil, Nat.reduceAdd, toPush, cast_eq]
    congr
    exact inductPush_nil
  case cons x xs ih =>
    simp only [← inductPush_listCons_push]
    congr

theorem getElemFin_finRange {n} (i : Fin n) : (finRange n)[i] = i := by
  simp only [Fin.getElem_fin, getElem_finRange, Fin.eta]

def mapFinRange (n : ℕ) (create : Fin n → α) : Vector α n := finRange n |>.map create

theorem mapFinRange_zero {create : Fin 0 → α} : mapFinRange 0 create = #v[] := by aesop

theorem mapFinRange_succ {n : ℕ} {create : Fin (n + 1) → α} :
    mapFinRange (n + 1) create = (mapFinRange n (fun i => create i.castSucc)).push (create (.last n)) := by
  rw [mapFinRange, mapFinRange, finRange_succ_last]
  simp only [append_singleton, map_push, map_map]
  rfl

theorem cast_mapFinRange {n} {create : Fin n → α} (h : n = m) :
    mapFinRange n create = (mapFinRange m (fun i => create (i.cast h.symm))).cast h.symm := by
  subst h; simp

theorem getElemFin_mapFinRange {n} {create : Fin n → α} :
    ∀ i : Fin n, (mapFinRange n create)[i] = create i := by
  simp [mapFinRange, finRange]

theorem getElem_mapFinRange {n} {create : Fin n → α} :
    ∀ (i : ℕ) (hi : i < n), (mapFinRange n create)[i] = create ⟨ i, hi ⟩ := by
  simp [mapFinRange, finRange]

lemma mapFinRange_eq_map {n : ℕ} (v : Vector α n) (f : α → β) :
    Vector.mapFinRange n (fun i => f v[i]) = v.map f := by
  ext i
  simp only [Vector.getElem_mapFinRange, Vector.getElem_map]
  simp

def mapRange (n : ℕ) (create : ℕ → α) : Vector α n :=
  match n with
  | 0 => #v[]
  | k + 1 => mapRange k create |>.push (create k)

theorem mapRange_zero {create : ℕ → α} : mapRange 0 create = #v[] := rfl

theorem mapRange_succ {n} {create : ℕ → α} :
    mapRange (n + 1) create = (mapRange n create).push (create n) := rfl

theorem cast_mapRange {n} {create : ℕ → α} (h : n = m) :
    mapRange n create = (mapRange m create).cast h.symm := by
  subst h; simp

theorem getElem_mapRange {n} {create : ℕ → α} :
    ∀ (i : ℕ) (hi : i < n), (mapRange n create)[i] = create i := by
  intros i hi
  induction n
  case zero => simp at hi
  case succ n ih =>
    rw [mapRange_succ]
    by_cases hi' : i < n
    · rw [getElem_push_lt hi', ih hi']
    · have i_eq : n = i := by linarith
      subst i_eq
      rw [getElem_push_eq]

theorem map_mapRange {n} {create : ℕ → α} {f : α → β} :
  Vector.map f (Vector.mapRange n create) =
    Vector.mapRange n (fun i => f (create i)) := by
  rw [Vector.ext_iff]
  simp [getElem_mapRange, getElem_map]

theorem mapRange_add_eq_append {n m} (create : ℕ → α) :
    mapRange (n + m) create = mapRange n create ++ mapRange m (fun i => create (n + i)) := by
  induction m with
  | zero => simp only [Nat.add_zero, mapRange, append_empty]
  | succ m ih => simp only [mapRange, Nat.add_eq, append_push, ih]

def fill (n : ℕ) (a : α) : Vector α n :=
  match n with
  | 0 => #v[]
  | k + 1 => (fill k a).push a

theorem getElem_fill {n} {a : α} {i : ℕ} {hi : i < n} :
    (fill n a)[i] = a := by
  induction n with
  | zero => nomatch hi
  | succ => simp_all [fill, getElem_push]

instance [Inhabited α] {n : ℕ} : Inhabited (Vector α n) where
  default := fill n default

-- two complementary theorems about `Vector.take` and `Vector.drop` on appended vectors
theorem cast_take_append_of_eq_length {v : Vector α n} {w : Vector α m} :
    (v ++ w |>.take n |>.cast Nat.min_add_right_self) = v := by
  have hv_length : v.toArray.toList.length = n := by simp
  rw [cast_mk, ←toArray_inj, take_eq_extract, toArray_extract, toArray_append,
    List.extract_toArray, Array.toList_append,
    List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
    List.take_append_of_le_length (Nat.le_of_eq hv_length.symm),
    List.take_of_length_le (Nat.le_of_eq hv_length), Array.toArray_toList]

theorem cast_drop_append_of_eq_length {v : Vector α n} {w : Vector α m} :
    (v ++ w |>.drop n |>.cast (Nat.add_sub_self_left n m)) = w := by
  have hv_length : v.toArray.toList.length = n := by simp
  have hw_length : w.toArray.toList.length = m := by simp
  rw [drop_eq_cast_extract, cast_cast, cast_mk, ←toArray_inj, toArray_extract, toArray_append,
    List.extract_toArray, Array.toList_append,
    List.extract_eq_take_drop, Nat.add_sub_self_left,
    List.drop_append_of_le_length (Nat.le_of_eq hv_length.symm),
    List.drop_of_length_le (Nat.le_of_eq hv_length), List.nil_append,
    List.take_of_length_le (Nat.le_of_eq hw_length), Array.toArray_toList]

theorem append_take_drop {v : Vector α (n + m)} :
    (v.take n |>.cast Nat.min_add_right_self) ++ (v.drop n |>.cast (Nat.add_sub_self_left n m)) = v := by
  rw [take_eq_extract, drop_eq_cast_extract, cast_cast, Vector.ext_iff]
  intro i hi
  rw [getElem_append]
  by_cases hi' : i < n
  · have goal' : (v.extract 0 n)[i] = v[0 + i] := getElem_extract (by omega)
    simp_all [getElem_cast]
  simp only [hi', reduceDIte, getElem_cast, getElem_extract]
  congr
  omega

/-- map and take commute for vectors -/
lemma map_take {α β : Type} {n : ℕ} (f : α → β) (xs : Vector α n) (i : ℕ) :
    (xs.map f).take i = (xs.take i).map f := by
  ext j hj
  simp only [Vector.getElem_map, Vector.getElem_take]

/-- Split a vector into equally-sized chunks. -/
def toChunks {n : ℕ} (m : ℕ) {α : Type} (v : Vector α (n*m)) : Vector (Vector α m) n :=
  match n with
  | 0 => #v[]
  | n + 1 =>
    have h_head : (n + 1) * m - n * m = m := by grind
    have h_tail : min (n * m) ((n + 1) * m) = n * m := by grind
    let head : Vector α m := (v.drop (n*m)).cast h_head
    let tail : Vector α (n*m) := (v.take (n*m)).cast h_tail
    (tail.toChunks m).push head

theorem toChunks_push (m : ℕ) {α : Type} (vs : Vector α (n*m)) (v : Vector α m) :
    (vs.toChunks m).push v = ((vs ++ v).cast (by simp [add_mul])).toChunks m := by
  simp only [toChunks]
  nth_rw 1 [← cast_take_append_of_eq_length (v := vs) (w := v)]
  nth_rw 2 [← cast_drop_append_of_eq_length (v := vs) (w := v)]
  rfl

theorem toChunks_flatten {α : Type} (m : ℕ) (v : Vector α (n*m)) :
    (v.toChunks m).flatten = v := by
  induction n with
  | zero => simp [toChunks]
  | succ n ih =>
    simp only [toChunks, flatten_push, ih]
    rw [Vector.ext_iff]
    intro i hi
    rw [getElem_cast, getElem_append]
    by_cases hi' : i < n * m
    · simp only [hi', ↓reduceDIte, getElem_cast, getElem_take]
    · simp only [hi', reduceDIte, getElem_cast, getElem_drop]
      grind

theorem flatten_toChunks {α : Type} (m : ℕ) (v : Vector (Vector α m) n) :
    v.flatten.toChunks m = v := by
  induction v using Vector.inductPush with
  | nil => simp [toChunks]
  | push as a ih =>
    nth_rw 2 [← ih]
    simp only [flatten_push, toChunks_push]

theorem mapM_singleton (a : α) {m : Type → Type} [Monad m] [LawfulMonad m] (f : α → m β) :
    #v[a].mapM f = (do pure #v[←f a]) := by
  apply map_toArray_inj.mp
  simp

theorem mapM_push (as : Vector α n) {m : Type → Type} [Monad m] [LawfulMonad m] (f : α → m β) (a : α) :
    (as.push a).mapM f = (do
      let bs ← as.mapM f
      let b ← f a
      pure (bs.push b)) := by
  rw [←append_singleton, mapM_append, mapM_singleton]
  simp only [bind_pure_comp, Functor.map_map, append_singleton]

def mapRangeM (n : ℕ) {m : Type → Type} [Monad m] (f : ℕ → m β) : m (Vector β n) := (range n).mapM f

def mapFinRangeM (n : ℕ) {m : Type → Type} [Monad m] (f : Fin n → m β) : m (Vector β n) := (finRange n).mapM f

/--
rotates elements to the left by `off`.
-/
def rotate {α : Type} {n : ℕ} (v : Vector α n) (off : ℕ) : Vector α n :=
  ⟨(v.toList.rotate off).toArray, by simp⟩

theorem rotate_rotate {α : Type} {n : ℕ} (v : Vector α n) (off1 off2 : ℕ) :
    v.rotate (off1 + off2) = (v.rotate off1).rotate off2 := by
  simp only [rotate, toList_mk, List.rotate_rotate]

theorem getElem_rotate {α : Type} {n : ℕ} {v : Vector α n} {off : ℕ} {i : ℕ} (hi : i < n) :
    (v.rotate off)[i] = v[(i + off) % n]'(Nat.mod_lt _ (Nat.pos_iff_ne_zero.mpr (Nat.ne_zero_of_lt hi))) := by
  rcases v with ⟨ ⟨ xs ⟩ , h ⟩
  simp only [List.size_toArray] at h
  simp [rotate, toList_mk, List.getElem_rotate, h]

/-- A variant of `take` that doesn't introduce `min j n` in type -/
def takeShort {α : Type} {n : ℕ} (v : Vector α n) (j : ℕ) (h_j : j < n) : Vector α j :=
  (v.take j).cast (by omega)

lemma getElem_takeShort {α : Type} {n : ℕ} (v : Vector α n) (j : ℕ) (h_j : j < n) (i : ℕ) (h_i : i < j) :
    (v.takeShort j h_j)[i] = v[i] := by
  simp only [takeShort, getElem_cast, getElem_take]

lemma map_takeShort {α β : Type} (f : α → β) {j n : ℕ} (v : Vector α n) (h_j : j < n) :
    Vector.map f (v.takeShort j h_j) = (v.map f).takeShort j h_j := by
  simp only [Vector.takeShort]
  ext k h_k
  simp only [Vector.getElem_map, Vector.getElem_take, Vector.getElem_cast]

end Vector
