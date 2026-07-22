import Clean.Ironwood.Specs.Sinsemilla

/-!
# Sinsemilla exceptional cases as computed break data

The Σ-refinement of the ⊥-propagating `hashToPoint` chain requested by
zcash/ironwood#45 (breaks-as-computed-data): instead of collapsing every
incomplete-addition escape to `none`, `hashToPointB` returns `Point ⊕ BreakData`,
where the break datum records *where* the escape fired (the consumed chunk prefix,
the escape chunk, the remaining suffix), the accumulator at that step, and *which*
escape condition held.

Fidelity to the specification's literal ⊥-model (§5.4.1.9) is the projection lemma
`getLeft?_hashToPointB`: mapping the break summand to `⊥` yields exactly
`hashToPoint`, so the Σ-form is a refinement — reviewers check the projection
against the spec text, and the refinement only adds the carried data.

`ValidBreak` is the exhibited relation: the prefix chain is honest
(`hashToPoint S Q pre = some acc` — so `acc` is the explicit generator combination
`2^n•Q + Σⱼ 2^(n−1−j)•S(mⱼ)`), and the escape equation holds at the resolved point
level (`acc = ±S(m)`, `acc + S(m) = 𝒪`, `2·acc + S(m) = 𝒪`, or an identity-operand
condition) — protocol-spec Theorem 5.4.4 made computational: a satisfying assignment
whose hash escapes yields a nontrivial discrete-log relation among `Q` and the
`S(mⱼ)` with coefficients read off `pre` (the `Q`-coefficient is a power of `2`,
nonzero mod the odd group order).
-/

namespace Zcash.Circuits.Specs.Sinsemilla


/-- Which incomplete-addition escape fired at the exceptional step. The step is
`(acc ⸭ S m) ⸭ acc` (§5.4.1.9); conditions are listed in evaluation order, so each
kind additionally certifies the *negations* of the earlier conditions. -/
inductive BreakKind
  /-- first addition, identity accumulator: `acc = 𝒪`. -/
  | accZero
  /-- first addition, identity generator: `S m = 𝒪`. -/
  | genZero
  /-- first addition, `x`-collision: `acc.x = (S m).x` — on-curve this resolves to
  `acc = S m` (`neg = false`) or `acc = −S m` (`neg = true`), recorded by comparing
  `y`-coordinates at emission. -/
  | collision (neg : Bool)
  /-- second addition, identity sum: `acc + S m = 𝒪`. -/
  | sumZero
  /-- second addition, `x`-collision: `(acc + S m).x = acc.x` — on-curve this
  resolves to `2·acc + S m = 𝒪`. -/
  | doubleCollision
deriving DecidableEq, Repr

/-- A Sinsemilla escape, as data: the message splits as `pre ++ chunk :: rest`, the
prefix chain is escape-free with accumulator `acc`, and the step at `chunk` fired
the `kind` escape. -/
structure BreakData where
  pre : List ℕ
  chunk : ℕ
  rest : List ℕ
  acc : Point Fp
  kind : BreakKind
deriving Repr

/-- One Σ-refined double-and-add step: the branch structure mirrors
`incompleteAdd`'s conditions in order, emitting the fired escape instead of `⊥`. -/
def stepB (S : ℕ → Point Fp) (m : ℕ) (acc : Point Fp) : Point Fp ⊕ BreakKind :=
  if acc = 0 then .inr .accZero
  else if S m = 0 then .inr .genZero
  else if acc.x = (S m).x then .inr (.collision (decide (acc.y ≠ (S m).y)))
  else if acc + S m = 0 then .inr .sumZero
  else if (acc + S m).x = acc.x then .inr .doubleCollision
  else .inl ((acc + S m) + acc)

/-- The Σ-refined chain: fold the message, carrying the consumed prefix; on the
first escape, return the break datum. -/
def hashToPointB.go (S : ℕ → Point Fp) (pre : List ℕ) (acc : Point Fp) :
    List ℕ → Point Fp ⊕ BreakData
  | [] => .inl acc
  | m :: rest =>
    match stepB S m acc with
    | .inl acc' => hashToPointB.go S (pre ++ [m]) acc' rest
    | .inr kind => .inr ⟨pre, m, rest, acc, kind⟩

/-- `SinsemillaHashToPoint`, refined: the hash point, or the escape as data. -/
def hashToPointB (S : ℕ → Point Fp) (Q : Point Fp) (chunks : List ℕ) :
    Point Fp ⊕ BreakData :=
  hashToPointB.go S [] Q chunks

/-! ## The projection to the specification's ⊥-model -/

/-- Step agreement: forgetting the break kind gives exactly the ⊥-propagating step. -/
theorem getLeft?_stepB (S : ℕ → Point Fp) (m : ℕ) (acc : Point Fp) :
    (stepB S m acc).getLeft? = step S m acc := by
  simp only [stepB, step, Point.doubleAndAdd, Point.incompleteAdd_def,
    Option.bind_eq_bind]
  split_ifs with h1 h2 h3 h4 h5 <;> simp_all

private theorem foldl_step_none (S : ℕ → Point Fp) (rest : List ℕ) :
    rest.foldl (fun acc m => acc.bind (step S m)) none = none := by
  induction rest with
  | nil => rfl
  | cons k rest ih => simpa using ih

private theorem go_getLeft? (S : ℕ → Point Fp) (rest : List ℕ) :
    ∀ (pre : List ℕ) (acc : Point Fp),
      (hashToPointB.go S pre acc rest).getLeft?
        = rest.foldl (fun acc m => acc.bind (step S m)) (some acc) := by
  induction rest with
  | nil => intro pre acc; rfl
  | cons m rest ih =>
    intro pre acc
    rw [hashToPointB.go]
    cases hs : stepB S m acc with
    | inl acc' =>
      have hstep : step S m acc = some acc' := by rw [← getLeft?_stepB, hs]; rfl
      rw [List.foldl_cons, show ((some acc).bind (step S m)) = step S m acc from rfl,
        hstep, ih]
    | inr kind =>
      have hstep : step S m acc = none := by rw [← getLeft?_stepB, hs]; rfl
      rw [List.foldl_cons, show ((some acc).bind (step S m)) = step S m acc from rfl,
        hstep, foldl_step_none]
      rfl

/-- **Projection lemma**: the Σ-refinement maps onto the specification's literal
⊥-model — `.inl B ↦ some B`, `.inr _ ↦ ⊥` recovers §5.4.1.9's `hashToPoint`. -/
theorem getLeft?_hashToPointB (S : ℕ → Point Fp) (Q : Point Fp) (chunks : List ℕ) :
    (hashToPointB S Q chunks).getLeft? = hashToPoint S Q chunks :=
  go_getLeft? S chunks [] Q

theorem hashToPointB_inl {S : ℕ → Point Fp} {Q : Point Fp} {chunks : List ℕ}
    {B : Point Fp} (h : hashToPointB S Q chunks = .inl B) :
    hashToPoint S Q chunks = some B := by
  rw [← getLeft?_hashToPointB, h]; rfl

/-- A defined hash forces the Σ-chain onto the value branch. -/
theorem hashToPointB_inl_of_some {S : ℕ → Point Fp} {Q : Point Fp} {chunks : List ℕ}
    {B : Point Fp} (h : hashToPoint S Q chunks = some B) :
    hashToPointB S Q chunks = .inl B := by
  have hp := getLeft?_hashToPointB S Q chunks
  rw [h] at hp
  cases hB : hashToPointB S Q chunks with
  | inl B' =>
    rw [hB] at hp
    simp only [Sum.getLeft?, Option.some.injEq] at hp
    rw [hp]
  | inr br => rw [hB] at hp; simp at hp

theorem hashToPoint_of_inr {S : ℕ → Point Fp} {Q : Point Fp} {chunks : List ℕ}
    {br : BreakData} (h : hashToPointB S Q chunks = .inr br) :
    hashToPoint S Q chunks = none := by
  rw [← getLeft?_hashToPointB, h]; rfl

/-! ## What each break certifies -/

/-- The raw escape condition of a break kind, together with the negations of the
conditions checked before it (the branch structure of `stepB`). -/
def BreakKind.Eq (kind : BreakKind) (acc P : Point Fp) : Prop :=
  match kind with
  | .accZero => acc = 0
  | .genZero => acc ≠ 0 ∧ P = 0
  | .collision neg =>
      acc ≠ 0 ∧ P ≠ 0 ∧ acc.x = P.x ∧ (neg = true ↔ acc.y ≠ P.y)
  | .sumZero => acc ≠ 0 ∧ P ≠ 0 ∧ acc.x ≠ P.x ∧ acc + P = 0
  | .doubleCollision =>
      acc ≠ 0 ∧ P ≠ 0 ∧ acc.x ≠ P.x ∧ acc + P ≠ 0 ∧ (acc + P).x = acc.x

theorem stepB_inr {S : ℕ → Point Fp} {m : ℕ} {acc : Point Fp} {kind : BreakKind}
    (h : stepB S m acc = .inr kind) : kind.Eq acc (S m) := by
  unfold stepB at h
  split_ifs at h with h1 h2 h3 h4 h5
  · cases h; exact h1
  · cases h; exact ⟨h1, h2⟩
  · cases h; exact ⟨h1, h2, h3, by simp⟩
  · cases h; exact ⟨h1, h2, h3, h4⟩
  · cases h; exact ⟨h1, h2, h3, h4, h5⟩

/-- The break invariant carried by `hashToPointB.go`. -/
private theorem go_inr {S : ℕ → Point Fp} {rest₀ : List ℕ} :
    ∀ {pre : List ℕ} {acc : Point Fp} {br : BreakData},
      hashToPointB.go S pre acc rest₀ = .inr br →
      ∀ {Q : Point Fp}, hashToPoint S Q pre = some acc →
      pre ++ rest₀ = br.pre ++ br.chunk :: br.rest ∧
        hashToPoint S Q br.pre = some br.acc ∧ br.kind.Eq br.acc (S br.chunk) := by
  induction rest₀ with
  | nil => intro pre acc br h; exact absurd h (by simp [hashToPointB.go])
  | cons m rest ih =>
    intro pre acc br h Q hpre
    rw [hashToPointB.go] at h
    cases hs : stepB S m acc with
    | inl acc' =>
      rw [hs] at h
      have hstep : step S m acc = some acc' := by rw [← getLeft?_stepB, hs]; rfl
      have hpre' : hashToPoint S Q (pre ++ [m]) = some acc' := by
        rw [hashToPoint_concat, hpre,
          show ((some acc).bind (step S m)) = step S m acc from rfl, hstep]
      have := ih h hpre'
      simpa [List.append_assoc] using this
    | inr kind =>
      rw [hs] at h
      cases h
      exact ⟨rfl, hpre, stepB_inr hs⟩

/-- A break datum's structural certificate: the message splits at the escape, the
prefix chain is honest, and the raw escape condition holds. -/
theorem hashToPointB_inr {S : ℕ → Point Fp} {Q : Point Fp} {chunks : List ℕ}
    {br : BreakData} (h : hashToPointB S Q chunks = .inr br) :
    chunks = br.pre ++ br.chunk :: br.rest ∧
      hashToPoint S Q br.pre = some br.acc ∧ br.kind.Eq br.acc (S br.chunk) := by
  have := go_inr (rest₀ := chunks) h (Q := Q) (by rfl)
  simpa using this

/-! ## Chain-value validity (raw-`S` variant of `hashToPoint_valid`) -/

private theorem step_valid_of_valid {S : ℕ → Point Fp} {m : ℕ} {A B : Point Fp}
    (hA : A.Valid) (hSm : (S m).Valid) (h : step S m A = some B) : B.Valid := by
  simp only [step, Point.doubleAndAdd, Option.bind_eq_bind] at h
  by_cases hc₁ : A = 0 ∨ S m = 0 ∨ A.x = (S m).x
  · rw [Point.incompleteAdd_def, if_pos hc₁] at h
    simp at h
  rw [Point.incompleteAdd_def, if_neg hc₁] at h
  rw [show ((some (A + S m)).bind fun t => Point.incompleteAdd t A)
    = Point.incompleteAdd (A + S m) A from rfl] at h
  by_cases hc₂ : A + S m = 0 ∨ A = 0 ∨ (A + S m).x = A.x
  · rw [Point.incompleteAdd_def, if_pos hc₂] at h
    simp at h
  rw [Point.incompleteAdd_def, if_neg hc₂] at h
  rw [Option.some.injEq] at h
  exact h ▸ Point.valid_add (Point.valid_add hA hSm) hA

/-- Every defined chain value is a valid group point (on-curve or the identity). -/
theorem hashToPoint_valid_of_mem {S : ℕ → Point Fp} {Q A : Point Fp}
    {chunks : List ℕ} (hQ : Q.Valid) (hS : ∀ m ∈ chunks, (S m).Valid)
    (h : hashToPoint S Q chunks = some A) : A.Valid := by
  induction chunks generalizing Q with
  | nil => rw [hashToPoint_nil, Option.some.injEq] at h; exact h ▸ hQ
  | cons m rest ih =>
    rw [hashToPoint_cons] at h
    cases hstep : step S m Q with
    | none => rw [hstep] at h; exact absurd h (by simp)
    | some acc =>
      rw [hstep] at h
      exact ih (step_valid_of_valid hQ (hS m List.mem_cons_self) hstep)
        (fun k hk => hS k (List.mem_cons_of_mem m hk)) h

/-! ## The exhibited relation (`ValidBreak`) -/

/-- The escape equation in resolved point language — the discrete-log-relation
exhibit of protocol-spec Theorem 5.4.4: with the prefix chain honest, `acc` is the
explicit combination `2^n•Q + Σⱼ 2^(n−1−j)•S(mⱼ)`, so each equation below is a
nontrivial relation among `Q` and the `S(mⱼ)` with coefficients read off `br.pre`. -/
def BreakData.PointEq (S : ℕ → Point Fp) (br : BreakData) : Prop :=
  match br.kind with
  | .accZero => br.acc = 0
  | .genZero => S br.chunk = 0
  | .collision neg => br.acc = if neg then -(S br.chunk) else S br.chunk
  | .sumZero => br.acc + S br.chunk = 0
  | .doubleCollision => (2 : ℕ) • br.acc + S br.chunk = 0

/-- The exhibited break: honest prefix chain plus the resolved escape equation. -/
def ValidBreak (S : ℕ → Point Fp) (Q : Point Fp) (br : BreakData) : Prop :=
  hashToPoint S Q br.pre = some br.acc ∧ br.PointEq S

private theorem x_ne_zero_of_onCurve {p : Point Fp} (hp : p.OnCurve) : p.x ≠ 0 := by
  intro hx
  rcases p with ⟨x, y⟩
  subst hx
  exact Point.no_onCurve_of_x_zero y hp

/-- Resolve a first-addition `x`-collision on-curve: the recorded `neg` flag picks
the sign, `acc = ±S m`. -/
private theorem collision_resolve {acc P : Point Fp} {neg : Bool}
    (hacc : acc.Valid) (hP : P.OnCurve)
    (h : (BreakKind.collision neg).Eq acc P) : acc = if neg then -P else P := by
  obtain ⟨haccNe, -, hx, hneg⟩ := h
  have haccC : acc.OnCurve := Point.onCurve_of_valid_of_ne_zero hacc haccNe
  have hy := Point.y_eq_or_neg_of_same_x (Or.inl hP) (Or.inl haccC)
    (x_ne_zero_of_onCurve hP) (x_ne_zero_of_onCurve haccC) hx
  cases neg with
  | false =>
    have hyy : acc.y = P.y := by
      by_contra hne
      exact absurd (hneg.mpr hne) (by simp)
    simp only [Bool.false_eq_true, if_false]
    rcases acc with ⟨ax, ay⟩; rcases P with ⟨px, py⟩
    simp_all
  | true =>
    have hne : acc.y ≠ P.y := hneg.mp rfl
    have hyy : acc.y = -P.y := hy.resolve_left hne
    simp only [if_true]
    apply Point.ext_coords
    simp only [Point.coords, Point.neg_x, Point.neg_y]
    rw [hx, hyy]

/-- Resolve a second-addition `x`-collision on-curve: `2·acc + S m = 𝒪`. -/
private theorem doubleCollision_resolve {acc P : Point Fp}
    (hacc : acc.Valid) (hP : P.OnCurve)
    (h : BreakKind.doubleCollision.Eq acc P) : (2 : ℕ) • acc + P = 0 := by
  obtain ⟨haccNe, hPNe, hxne, htNe, hx⟩ := h
  have haccC : acc.OnCurve := Point.onCurve_of_valid_of_ne_zero hacc haccNe
  have haccV : acc.Valid := Or.inl haccC
  have hPV : P.Valid := Or.inl hP
  have htV : (acc + P).Valid := Point.valid_add haccV hPV
  have htC : (acc + P).OnCurve := Point.onCurve_of_valid_of_ne_zero htV htNe
  -- `(acc + P) = acc` or `(acc + P) = −acc`
  have hy := Point.y_eq_or_neg_of_same_x (Or.inl haccC) (Or.inl htC)
    (x_ne_zero_of_onCurve haccC) (x_ne_zero_of_onCurve htC) hx
  have hcases : acc + P = acc ∨ acc + P = -acc := by
    rcases hy with hyy | hyy
    · exact Or.inl (Point.ext_coords (by simp_all [Point.coords]))
    · refine Or.inr (Point.ext_coords ?_)
      simp only [Point.coords, Point.neg_x, Point.neg_y]
      rw [hx, hyy]
  rcases hcases with hcase | hcase
  · -- `acc + P = acc` forces `P = 𝒪` — excluded
    exfalso
    apply hPNe
    have h1 := (Point.ext_toSW_iff (Point.valid_add haccV hPV) haccV).mp hcase
    rw [Point.toSW_add haccV hPV] at h1
    have hP0 : P.toSW hPV = 0 :=
      add_left_cancel (a := acc.toSW haccV) (by rw [add_zero]; exact h1)
    rw [Point.ext_toSW_iff hPV Point.valid_zero, hP0, Point.toSW_zero]
  · -- `acc + P = −acc` gives `2·acc + P = 𝒪`
    have h2V : ((2 : ℕ) • acc).Valid := Point.valid_nsmul haccV 2
    rw [Point.ext_toSW_iff (Point.valid_add h2V hPV) Point.valid_zero,
      Point.toSW_add h2V hPV, Point.toSW_nsmul haccV 2, Point.toSW_zero]
    have h1 := (Point.ext_toSW_iff (Point.valid_add haccV hPV)
      (Point.valid_neg haccV)).mp hcase
    rw [Point.toSW_add haccV hPV, Point.toSW_neg haccV] at h1
    have hPsw : P.toSW hPV = -(acc.toSW haccV) - acc.toSW haccV :=
      eq_sub_of_add_eq (by rwa [add_comm] at h1)
    rw [hPsw, two_nsmul]
    abel

/-- **Theorem 5.4.4, computational**: every break emitted by the Σ-chain is valid —
the prefix chain is honest and the resolved escape equation holds. Hypotheses are
the on-curve facts of the generators actually consumed. -/
theorem validBreak_of_inr {S : ℕ → Point Fp} {Q : Point Fp} {chunks : List ℕ}
    {br : BreakData} (hQ : Q.Valid) (hS : ∀ m ∈ chunks, (S m).OnCurve)
    (h : hashToPointB S Q chunks = .inr br) : ValidBreak S Q br := by
  obtain ⟨hsplit, hpre, hEq⟩ := hashToPointB_inr h
  refine ⟨hpre, ?_⟩
  have hSpre : ∀ m ∈ br.pre, (S m).Valid := fun m hm =>
    Or.inl (hS m (hsplit ▸ List.mem_append_left _ hm))
  have hchunk : (S br.chunk).OnCurve :=
    hS br.chunk (hsplit ▸ List.mem_append_right _ List.mem_cons_self)
  have haccV : br.acc.Valid := hashToPoint_valid_of_mem hQ hSpre hpre
  rw [BreakData.PointEq]
  rcases hkind : br.kind with _ | _ | neg | _ | _ <;> rw [hkind] at hEq <;>
    simp only []
  · exact hEq
  · exact hEq.2
  · exact collision_resolve haccV hchunk hEq
  · exact hEq.2.2.2
  · exact doubleCollision_resolve haccV hchunk hEq

/-! ## The breaks-as-data disjunction and the bridge from guarded conclusions -/

/-- The breaks-as-data disjunction: the payload predicate on the hash point, or a
valid exhibited break. Relation-layer specs are stated as
`SpecOrBreak S Q P (hashToPointB S Q chunks)`. -/
def SpecOrBreak (S : ℕ → Point Fp) (Q : Point Fp) (P : Point Fp → Prop) :
    Point Fp ⊕ BreakData → Prop
  | .inl B => P B
  | .inr br => ValidBreak S Q br

theorem SpecOrBreak.mono {S : ℕ → Point Fp} {Q : Point Fp}
    {P P' : Point Fp → Prop} (h : ∀ B, P B → P' B) :
    ∀ {v : Point Fp ⊕ BreakData}, SpecOrBreak S Q P v → SpecOrBreak S Q P' v
  | .inl B, hv => h B hv
  | .inr _, hv => hv

/-- Every `K`-bit chunk read off a value is in the generator table's index range. -/
theorem chunksOf_mem_lt {val n m : ℕ} (h : m ∈ chunksOf val n) : m < 2 ^ K := by
  simp only [chunksOf, List.mem_map, List.mem_range] at h
  obtain ⟨i, -, rfl⟩ := h
  exact bitrange_lt _ _ _

/-- The generator table is on-curve at every chunk of a `chunksOf` message. -/
theorem Generators.chunksOf_onCurve (G : Generators) (val n : ℕ) :
    ∀ m ∈ chunksOf val n, (G.S m).OnCurve := fun _ hm =>
  G.S_onCurve (chunksOf_mem_lt hm)

/-- Upgrade a guarded (`∀ B, hashToPoint … = some B → P B`) soundness conclusion to
the breaks-as-data disjunction: either the hash is defined and `P` holds of it, or
the escape is exhibited as a valid break. This is the one-line patch point for
composed circuit soundness proofs. -/
theorem breaksOfGuarded {S : ℕ → Point Fp} {Q : Point Fp} {chunks : List ℕ}
    (hQ : Q.Valid) (hS : ∀ m ∈ chunks, (S m).OnCurve)
    {P : Point Fp → Prop} (h : ∀ B, hashToPoint S Q chunks = some B → P B) :
    SpecOrBreak S Q P (hashToPointB S Q chunks) := by
  cases hB : hashToPointB S Q chunks with
  | inl B => exact h B (hashToPointB_inl hB)
  | inr br => exact validBreak_of_inr hQ hS hB

end Zcash.Circuits.Specs.Sinsemilla
