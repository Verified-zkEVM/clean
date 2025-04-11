import Clean.Circuit.Basic
variable {n m o : ℕ} {F : Type} [Field F] {α β : Type}

def Operations.append {m n: ℕ} (as : Operations F m) : (bs : Operations F n) → bs.initial_offset = m → Operations F n
  | empty n, (heq : n = _) => heq ▸ as
  | witness bs k c, heq => witness (append as bs heq) k c
  | assert bs e, heq => assert (append as bs heq) e
  | lookup bs l, heq => lookup (append as bs heq) l
  | subcircuit bs s, heq => subcircuit (append as bs heq) s

@[reducible] def OperationsFrom (F: Type) [Field F] (m: ℕ) (n : ℕ) :=
  { bs : Operations F n // bs.initial_offset = m }

instance (as : Operations F n) : CoeDep (Operations F n) (as) (OperationsFrom F (as.initial_offset) n) where
  coe := ⟨ as, rfl ⟩

-- constructors

def OperationsFrom.empty (n: ℕ) : OperationsFrom F n n := .mk (.empty n) rfl

def OperationsFrom.witness (as : OperationsFrom F m n) (k : ℕ) (c : Environment F → Vector F k) : OperationsFrom F m (n + k) :=
  .mk (.witness as.val k c) as.property

def OperationsFrom.assert (as : OperationsFrom F m n) (e : Expression F) : OperationsFrom F m n :=
  .mk (.assert as.val e) as.property

def OperationsFrom.lookup (as : OperationsFrom F m n) (l : Lookup F) : OperationsFrom F m n :=
  .mk (.lookup as.val l) as.property

def OperationsFrom.subcircuit (as : OperationsFrom F m n) (s : SubCircuit F n) : OperationsFrom F m (n + s.local_length) :=
  .mk (.subcircuit as.val s) as.property

-- induction principle for OperationsFrom
def OperationsFrom.induct' {F: Type} [Field F] {motive : {n m: ℕ} → OperationsFrom F m n → Prop}
  (empty : ∀ (n), motive (n:=n) (m:=n) (.empty n))
  (witness : ∀ {n m} (as : Operations F n) (k c) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (.witness as k c) ha))
  (assert : ∀ {n m} (as : Operations F n) (e) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (.assert as e) ha))
  (lookup : ∀ {n m} (as : Operations F n) (l) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (.lookup as l) ha))
  (subcircuit : ∀ {n m} (as : Operations F n) (s) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (.subcircuit as s) ha))
  {n m: ℕ} (as: OperationsFrom F m n) : motive as :=
  motive' as.val as.property
where
  motive' {n m} : (as : Operations F n) → (ha: as.initial_offset = m) → motive (.mk as ha)
  | .empty n, rfl => empty n
  | .witness _ _ _, _ => witness _ _ _ _ (motive' _ _)
  | .assert _ _, _ => assert _ _ _ (motive' _ _)
  | .lookup _ _, _ => lookup _ _ _ (motive' _ _)
  | .subcircuit _ _, _ => subcircuit _ _ _ (motive' _ _)

def OperationsFrom.induct {F: Type} [Field F] {motive : {n m: ℕ} → OperationsFrom F m n → Prop}
  (empty : ∀ (n), motive (n:=n) (m:=n) (.empty n))
  (witness : ∀ {n m} (as : OperationsFrom F m n) (k c), motive as → motive (.witness as k c))
  (assert : ∀ {n m} (as : OperationsFrom F m n) (e), motive as → motive (.assert as e))
  (lookup : ∀ {n m} (as : OperationsFrom F m n) (l), motive as → motive (.lookup as l))
  (subcircuit : ∀ {n m} (as : OperationsFrom F m n) (s), motive as → motive (.subcircuit as s))
    {n m: ℕ} (as: OperationsFrom F m n) : motive as := by
  induction as using OperationsFrom.induct' with
  | empty n => exact empty n
  | witness as k c ha ih => exact witness _ _ _ ih
  | assert as e ha ih => exact assert _ _ ih
  | lookup as l ha ih => exact lookup _ _ ih
  | subcircuit as s ha ih => exact subcircuit _ _ ih

namespace Operations
instance : HAppend (Operations F m) (OperationsFrom F m n) (Operations F n) where
  hAppend as bs := as.append bs.val bs.property

theorem append_empty (as : Operations F n) : as ++ (OperationsFrom.empty (F:=F) n) = as := rfl

theorem empty_append (as : OperationsFrom F n m) : empty (F:=F) n ++ as = as.val := by
  induction as using OperationsFrom.induct' with
  | empty n => rfl
  | witness | assert | lookup | subcircuit => simp_all only [HAppend.hAppend, append]

theorem append_witness (as : Operations F m) (bs : OperationsFrom F m n) (k : ℕ) (c : Environment F → Vector F k) :
  as ++ (OperationsFrom.witness bs k c) = .witness (as ++ bs) k c := by rfl

theorem append_assert (as : Operations F m) (bs : OperationsFrom F m n) (e : Expression F) :
  as ++ (OperationsFrom.assert bs e) = .assert (as ++ bs) e := by rfl

theorem append_lookup (as : Operations F m) (bs : OperationsFrom F m n) (l : Lookup F) :
  as ++ (OperationsFrom.lookup bs l) = .lookup (as ++ bs) l := by rfl

theorem append_subcircuit (as : Operations F m) (bs : OperationsFrom F m n) (s : SubCircuit F n) :
  as ++ (OperationsFrom.subcircuit bs s) = .subcircuit (as ++ bs) s := by rfl

theorem append_initial_offset {m n: ℕ} (as : Operations F m) (bs : OperationsFrom F m n) :
    (as ++ bs).initial_offset = as.initial_offset := by
  induction bs using OperationsFrom.induct with
  | empty n => rfl
  | witness bs _ _ ih | assert bs _ ih | lookup bs _ ih | subcircuit bs _ ih => exact ih as
end Operations

instance : HAppend (OperationsFrom F m n) (OperationsFrom F n o) (OperationsFrom F m o) where
  hAppend as bs := ⟨ as.val.append bs.val bs.property, by
    show (as.val ++ bs).initial_offset = m
    rw [Operations.append_initial_offset, as.property] ⟩

theorem Operations.append_assoc {m n o: ℕ} (as : Operations F m) (bs : OperationsFrom F m n) (cs : OperationsFrom F n o) :
  (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction cs using OperationsFrom.induct' with
  | empty n => rfl
  | witness _ _ _ _ ih | assert _ _ _ ih | lookup _ _ _ ih | subcircuit _ _ _ ih =>
    simp only [HAppend.hAppend, append, witness.injEq, assert.injEq, lookup.injEq, subcircuit.injEq, and_true]
    exact ih bs

namespace OperationsFrom
theorem append_val (as : OperationsFrom F m n) (bs : OperationsFrom F n o) :
    (as ++ bs).val = as.val ++ bs := by
  dsimp only [HAppend.hAppend]

theorem empty_val (n : ℕ) : (empty (F:=F) n).val = Operations.empty n := rfl

theorem self_val (as : Operations F n) : as = (⟨ as, rfl ⟩ : OperationsFrom F as.initial_offset n).val := rfl

theorem append_empty (as : OperationsFrom F m n) : as ++ empty (F:=F) n = as := rfl

theorem empty_append (as : OperationsFrom F m n) : empty (F:=F) m ++ as = as := by
  ext; rw [append_val, empty_val, Operations.empty_append]

theorem append_assoc {p: ℕ} (as : OperationsFrom F m n) (bs : OperationsFrom F n o) (cs : OperationsFrom F o p) :
  (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  ext; simp only [append_val, Operations.append_assoc]
end OperationsFrom
