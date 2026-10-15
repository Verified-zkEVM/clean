/-
Phases: what a rare event may depend on, as a compositional contract.

A rare event is only rare if its committed values are fixed before the challenge is drawn. This
file makes that a contract of an implementation, stated on *values*, like soundness:

- An interface that takes a challenge says which part of its input is committed and which part is
  the challenge (`Interface.Phases`).
- `Impl.Phased impl ph`: every rare event of `impl` is *phased*: its committed values are
  determined by the committed part of the input, and the challenge of the input is determined by
  its challenge values (`RareEvent.Phased`).
- A parent proves its contract from its children's: per call, the child's committed part is
  determined by the parent's, and the child's challenge determines the parent's. These are facts
  about values, discharged like soundness obligations. Calls to implementations without rare
  events (`Impl.NoEvents`) cost nothing. The `phased` tactic does the bookkeeping.

Circuits without challenges never see any of this: `NoEvents` is all they need, and only when a
challenge-using parent calls them.
-/
module

public import Clean2.Core
public import Lean.Elab.Tactic
meta import Clean2.Core.Spatial

@[expose] public section

namespace Clean2

/-! ## Determined values -/

/-- `g` is determined by `f`: it takes the same value wherever `f` does. -/
def Determined {E X Y : Type} (f : E → X) (g : E → Y) : Prop :=
  ∀ e e', f e = f e' → g e = g e'

namespace Determined
variable {E X Y Z : Type} {f : E → X} {g : E → Y} {h : E → Z}

theorem refl (f : E → X) : Determined f f := fun _ _ h => h

theorem trans (h₁ : Determined f g) (h₂ : Determined g h) : Determined f h :=
  fun e e' hf => h₂ e e' (h₁ e e' hf)

/-- A function of a determined value is determined. -/
theorem comp (h₁ : Determined f g) (φ : Y → Z) : Determined f (fun e => φ (g e)) :=
  fun e e' hf => congrArg φ (h₁ e e' hf)

theorem const (f : E → X) (y : Y) : Determined f (fun _ => y) := fun _ _ _ => rfl

theorem pair (h₁ : Determined f g) (h₂ : Determined f h) : Determined f (fun e => (g e, h e)) :=
  fun e e' hf => Prod.ext (h₁ e e' hf) (h₂ e e' hf)

theorem fst {g : E → Y × Z} (h₁ : Determined f g) : Determined f (fun e => (g e).1) := h₁.comp _
theorem snd {g : E → Y × Z} (h₁ : Determined f g) : Determined f (fun e => (g e).2) := h₁.comp _

end Determined

variable {B : Backend}

/-! ## Phased rare events -/

/-- A rare event is *phased* with respect to a committed key `K` and a challenge `A`, both functions
of the assignment: its committed values are determined by `K`, and `A` is determined by its
challenge values. Then, with `K` fixed, it happens at no more than `bound` values of `A`
(`encard_le`). -/
def RareEvent.Phased {κ T : Type} (ev : RareEvent B) (K : (B.Cell → B.Native) → κ)
    (A : (B.Cell → B.Native) → T) : Prop :=
  Determined K (fun env => ev.committed.map (B.eval env)) ∧
    Determined (fun env => ev.challenge.map (B.eval env)) A

namespace RareEvent
variable {κ κ' T T' : Type} {ev : RareEvent B} {K : (B.Cell → B.Native) → κ} {A : (B.Cell → B.Native) → T}

theorem Phased.mono {K' : (B.Cell → B.Native) → κ'} {A' : (B.Cell → B.Native) → T'}
    (h : ev.Phased K' A') (hK : Determined K K') (hA : Determined A' A) : ev.Phased K A :=
  ⟨hK.trans h.1, h.2.trans hA⟩

/-- With the committed key fixed, a phased event happens at no more than `bound` challenges. -/
theorem Phased.encard_le (h : ev.Phased K A) (x : κ) :
    {a | ∃ env, K env = x ∧ A env = a ∧ ev.Happens env}.encard ≤ ev.bound := by
  classical
  by_cases hx : ∃ env₁, K env₁ = x
  · obtain ⟨env₁, rfl⟩ := hx
    -- the challenge values determine `A`: read it off any assignment that has them
    let φ : Vector B.Native ev.k → T := fun c =>
      if hc : ∃ env, ev.challenge.map (B.eval env) = c then A hc.choose else A env₁
    refine (Set.encard_le_encard fun a ha => ?_).trans
      ((Set.encard_image_le φ {c | ev.Bad (ev.committed.map (B.eval env₁)) c}).trans
        (ev.encard_bad_le _))
    obtain ⟨env, h_K, rfl, h_happens⟩ := ha
    have hc : ∃ env', ev.challenge.map (B.eval env') = ev.challenge.map (B.eval env) := ⟨env, rfl⟩
    refine ⟨ev.challenge.map (B.eval env), ?_, ?_⟩
    · have h_c : ev.committed.map (B.eval env) = ev.committed.map (B.eval env₁) := h.1 env env₁ h_K
      show ev.Bad _ _
      rw [← h_c]
      exact h_happens
    · show φ _ = A env
      simp only [φ]
      rw [dif_pos hc]
      exact h.2 _ _ hc.choose_spec
  · have h_empty : {a | ∃ env, K env = x ∧ A env = a ∧ ev.Happens env} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨env, h_K, -⟩
      exact hx ⟨env, h_K⟩
    simp [h_empty]

end RareEvent

/-- A rare event with a native challenge is phased if its committed values are determined by the
committed key, and its challenge determines the challenge `A`. -/
theorem RareEvent.ofNative_phased {κ T : Type} {K : (B.Cell → B.Native) → κ} {A : (B.Cell → B.Native) → T}
    {m : ℕ} (committed : Vector B.Var m) (α : B.Var) (Bad : Vector B.Native m → B.Native → Prop)
    (bound : ℕ) (h) (hK : Determined K (fun env => committed.map (B.eval env)))
    (hA : Determined (fun env => B.eval env α) A) :
    (RareEvent.ofNative committed α Bad bound h).Phased K A := by
  refine ⟨hK, fun e e' he => hA e e' ?_⟩
  have := congrArg (fun v : Vector B.Native 1 => v[0]) he
  simpa [RareEvent.ofNative] using this

/-- A layout of challenge values: without an invariant, and representing each value at most
once, so that counting layouts counts values. -/
class CType.Faithful {F T : Type} (t : CType F T) : Prop where
  valid : ∀ x, t.Valid x
  injective : Function.Injective t.decode

instance {F : Type} : (CType.native : CType F F).Faithful := ⟨fun _ => trivial, fun _ _ h => h⟩

@[circuit_norm]
theorem CType.Faithful.valid_eq {F T : Type} (t : CType F T) [h : t.Faithful] (x : t.Shape F) : t.Valid x = True :=
  eq_true (h.valid x)

/-! ## Rare events with a challenge in a field `K` -/

/-- A rare event whose challenge is a value of `K`, laid out by a faithful `kty`: it happens when the
layout of the challenge is that of a bad value. -/
def RareEvent.ofType {K : Type} (kty : CType B.Native K) [kty.Faithful] {m : ℕ} (committed : Vector B.Var m)
    (α : kty.Shape B.Var) (Bad : Vector B.Native m → K → Prop) (bound : ℕ)
    (encard_bad_le : ∀ v, {a | Bad v a}.encard ≤ bound) : RareEvent B where
  committed := committed
  challenge := toElements α
  Bad v a := ∃ y : kty.Shape B.Native, toElements y = a ∧ Bad v (kty.decode y)
  bound := bound
  encard_bad_le v := by
    have h_to : Function.Injective (toElements : kty.Shape B.Native → _) := fun x y h => by
      rw [← ProvableType.fromElements_toElements x, h, ProvableType.fromElements_toElements]
    calc {a | ∃ y : kty.Shape B.Native, toElements y = a ∧ Bad v (kty.decode y)}.encard
        = (toElements '' {y : kty.Shape B.Native | Bad v (kty.decode y)}).encard := by
          congr 1; ext a; simp [and_comm]
      _ = {y : kty.Shape B.Native | Bad v (kty.decode y)}.encard := h_to.encard_image _
      _ = (kty.decode '' {y : kty.Shape B.Native | Bad v (kty.decode y)}).encard :=
          (CType.Faithful.injective.encard_image _).symm
      _ ≤ {k | Bad v k}.encard := Set.encard_le_encard (by rintro _ ⟨a, ha, rfl⟩; exact ha)
      _ ≤ bound := encard_bad_le v

@[circuit_norm]
theorem RareEvent.ofType_bound {K : Type} (kty : CType B.Native K) [kty.Faithful] {m : ℕ}
    (committed : Vector B.Var m) (α : kty.Shape B.Var) (Bad : Vector B.Native m → K → Prop) (bound : ℕ) (h) :
    (RareEvent.ofType kty committed α Bad bound h).bound = bound := rfl

@[circuit_norm]
theorem RareEvent.ofType_happens {K : Type} (kty : CType B.Native K) [kty.Faithful] {m : ℕ}
    (committed : Vector B.Var m) (α : kty.Shape B.Var) (Bad : Vector B.Native m → K → Prop) (bound : ℕ) (h)
    (env : B.Cell → B.Native) :
    (RareEvent.ofType kty committed α Bad bound h).Happens env ↔
      Bad (committed.map (B.eval env)) (kty.decode (B.evalT env α)) := by
  simp only [RareEvent.Happens, RareEvent.ofType]
  constructor
  · rintro ⟨y, hy, h⟩
    have : y = B.evalT env α := by
      rw [← ProvableType.fromElements_toElements y, hy, ← Backend.evalT_eq_fromElements]
    rwa [← this]
  · intro h
    exact ⟨B.evalT env α, ProvableType.toElements_map _ _, h⟩

/-- A rare event with a challenge in `K` is phased if its committed values are determined by the
committed key, and the decoded challenge determines the challenge `A`. -/
theorem RareEvent.ofType_phased {κ T K : Type} {A' : (B.Cell → B.Native) → T} {K' : (B.Cell → B.Native) → κ}
    (kty : CType B.Native K) [kty.Faithful] {m : ℕ} (committed : Vector B.Var m) (α : kty.Shape B.Var)
    (Bad : Vector B.Native m → K → Prop) (bound : ℕ) (h)
    (hK : Determined K' (fun env => committed.map (B.eval env)))
    (hA : Determined (fun env => kty.decode (B.evalT env α)) A') :
    (RareEvent.ofType kty committed α Bad bound h).Phased K' A' := by
  refine ⟨hK, fun e e' he => hA e e' ?_⟩
  have he' : (toElements α).map (B.eval e) = (toElements α).map (B.eval e') := he
  simp only [Backend.evalT_eq_fromElements, he']

/-! ## Phased operations -/

/-- Every rare event of the operations, for soundness or completeness, is phased. -/
def Ops.Phased {κ T : Type} (K : (B.Cell → B.Native) → κ) (A : (B.Cell → B.Native) → T) (ops : Ops B) :
    Prop :=
  ∀ ev ∈ ops.events ++ ops.honestEvents, ev.Phased K A

/-- Every rare event of a call is phased. -/
def Subcircuit.Phased {κ T : Type} (K : (B.Cell → B.Native) → κ) (A : (B.Cell → B.Native) → T)
    {s : B.State} (sc : Subcircuit B s) : Prop :=
  ∀ ev ∈ sc.events ++ sc.honestEvents, ev.Phased K A

namespace Ops
variable {κ T : Type} {K : (B.Cell → B.Native) → κ} {A : (B.Cell → B.Native) → T}

theorem phased_nil : Ops.Phased K A ([] : Ops B) := by simp [Ops.Phased, events, honestEvents]

theorem phased_cons_native (op : B.Op) (ops : Ops B) :
    Ops.Phased K A (.native op :: ops) ↔ Ops.Phased K A ops := by
  simp [Ops.Phased, events, honestEvents]

theorem phased_cons_call {s : B.State} (sc : Subcircuit B s) (ops : Ops B) :
    Ops.Phased K A (.call sc :: ops) ↔ sc.Phased K A ∧ Ops.Phased K A ops := by
  simp only [Ops.Phased, Subcircuit.Phased, events, honestEvents, List.forall_mem_append]
  tauto

theorem phased_cons_rare (ev : RareEvent B) (ops : Ops B) :
    Ops.Phased K A (.rare ev :: ops) ↔ ev.Phased K A ∧ Ops.Phased K A ops := by
  simp only [Ops.Phased, events, honestEvents, List.forall_mem_append, List.forall_mem_cons]
  tauto

theorem phased_cons_rareHonest (ev : RareEvent B) (ops : Ops B) :
    Ops.Phased K A (.rareHonest ev :: ops) ↔ ev.Phased K A ∧ Ops.Phased K A ops := by
  simp only [Ops.Phased, events, honestEvents, List.forall_mem_append, List.forall_mem_cons]
  tauto

theorem phased_append (a b : Ops B) : Ops.Phased K A (a ++ b) ↔ Ops.Phased K A a ∧ Ops.Phased K A b := by
  simp only [Ops.Phased, events_append, honestEvents_append, List.forall_mem_append]
  tauto

theorem Phased.mono {κ' T' : Type} {K' : (B.Cell → B.Native) → κ'} {A' : (B.Cell → B.Native) → T'}
    {ops : Ops B} (h : Ops.Phased K' A' ops) (hK : Determined K K') (hA : Determined A' A) :
    Ops.Phased K A ops :=
  fun ev hev => (h ev hev).mono hK hA

end Ops

/-! ## Loops -/

namespace Circuit
variable {κ T : Type} {K : (B.Cell → B.Native) → κ} {A : (B.Cell → B.Native) → T}

/-- A loop is phased if every iteration is. -/
theorem foldr_phased {α : Type} {n : ℕ} (f : Fin n → α → Circuit B α) (z : α)
    (h : ∀ i acc s, Ops.Phased K A ((f i acc).operations s)) (s : B.State) :
    Ops.Phased K A ((foldr n f z).operations s) := by
  induction n generalizing z s with
  | zero => exact Ops.phased_nil
  | succ n ih =>
    simp only [circuit_norm]
    exact (Ops.phased_append _ _).mpr ⟨ih _ z (fun i => h i.succ) s, h 0 _ _⟩

theorem mapFin_phased {α : Type} {n : ℕ} (f : Fin n → Circuit B α)
    (h : ∀ i s, Ops.Phased K A ((f i).operations s)) (s : B.State) :
    Ops.Phased K A ((mapFin n f).operations s) := by
  induction n generalizing s with
  | zero => exact Ops.phased_nil
  | succ n ih =>
    simp only [circuit_norm]
    refine (Ops.phased_append _ _).mpr ⟨ih _ (fun i => h i.castSucc) s, ?_⟩
    simpa using h _ _

/-- A loop whose body assumes no rare event assumes none. -/
theorem foldr_events {α : Type} {n : ℕ} (f : Fin n → α → Circuit B α) (z : α)
    (h : ∀ i acc s, ((f i acc).operations s).events = []) (s : B.State) :
    ((foldr n f z).operations s).events = [] := by
  induction n generalizing z s with
  | zero => simp only [circuit_norm]
  | succ n ih => simp only [circuit_norm, Ops.events_append, ih _ z (fun i => h i.succ) s, h 0, List.append_nil]

theorem foldr_honestEvents {α : Type} {n : ℕ} (f : Fin n → α → Circuit B α) (z : α)
    (h : ∀ i acc s, ((f i acc).operations s).honestEvents = []) (s : B.State) :
    ((foldr n f z).operations s).honestEvents = [] := by
  induction n generalizing z s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm, Ops.honestEvents_append, ih _ z (fun i => h i.succ) s, h 0, List.append_nil]

theorem mapFin_events {α : Type} {n : ℕ} (f : Fin n → Circuit B α)
    (h : ∀ i s, ((f i).operations s).events = []) (s : B.State) :
    ((mapFin n f).operations s).events = [] := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm, Ops.events_append, ih _ (fun i => h i.castSucc) s, h, List.append_nil]

theorem mapFin_honestEvents {α : Type} {n : ℕ} (f : Fin n → Circuit B α)
    (h : ∀ i s, ((f i).operations s).honestEvents = []) (s : B.State) :
    ((mapFin n f).operations s).honestEvents = [] := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm, Ops.honestEvents_append, ih _ (fun i => h i.castSucc) s, h, List.append_nil]

end Circuit

/-! ## The contract of an implementation -/

/-- Which part of an interface's input is committed before the challenge is drawn, and which part
is the challenge. An annotation, given once per interface that takes a challenge. -/
structure Interface.Phases {Native : Type} (c : Interface Native) where
  Committed : Type
  committed : c.input → Committed
  Challenge : Type
  challenge : c.input → Challenge

namespace Interface.Phases
variable {c : Interface B.Native}

/-- The committed part of an input, as a function of the assignment. -/
@[reducible]
def key (ph : c.Phases) (input : c.Input B.Var) (env : B.Cell → B.Native) : ph.Committed :=
  ph.committed (c.inputCType.decode (B.evalT env input))

/-- The challenge of an input, as a function of the assignment. -/
@[reducible]
def chal (ph : c.Phases) (input : c.Input B.Var) (env : B.Cell → B.Native) : ph.Challenge :=
  ph.challenge (c.inputCType.decode (B.evalT env input))

end Interface.Phases

namespace Impl
variable {c : Interface B.Native}

/-- `impl` has no rare events: the case of every circuit that uses no challenge. -/
class NoEvents (impl : Impl B c) : Prop where
  events_eq : ∀ input s, ((impl.main input).operations s).events = []
  honestEvents_eq : ∀ input s, ((impl.main input).operations s).honestEvents = []

/-- The phase contract of `impl`, for the annotation `ph` of its interface: every rare event of
`impl` depends only on the committed part of the input, and determines the input's challenge. -/
class Phased (impl : Impl B c) (ph : outParam c.Phases) : Prop where
  phased : ∀ input s, ((impl.main input).operations s).Phased (ph.key input) (ph.chal input)

/-- A call to an implementation without rare events. -/
theorem phased_call_of_noEvents {κ T : Type} {K : (B.Cell → B.Native) → κ} {A : (B.Cell → B.Native) → T}
    (impl : Impl B c) [h : NoEvents impl] (s : B.State) (input : c.Input B.Var) :
    (impl.toSubcircuit s input).Phased K A := by
  intro ev hev
  change ev ∈ ((impl.main input).operations s).events ++ ((impl.main input).operations s).honestEvents at hev
  simp [h.events_eq, h.honestEvents_eq] at hev

/-- A call to a phased implementation: the caller's committed key determines the callee's, and
the callee's challenge determines the caller's. -/
theorem phased_call {κ T : Type} {K : (B.Cell → B.Native) → κ} {A : (B.Cell → B.Native) → T}
    {ph : c.Phases} (impl : Impl B c) [h : Phased impl ph] (s : B.State) (input : c.Input B.Var)
    (hK : Determined K (ph.key input)) (hA : Determined (ph.chal input) A) :
    (impl.toSubcircuit s input).Phased K A :=
  fun ev hev => (h.phased input s ev hev).mono hK hA

theorem noEvents_phased (impl : Impl B c) [h : NoEvents impl] (ph : c.Phases) :
    ∀ input s, ((impl.main input).operations s).Phased (ph.key input) (ph.chal input) := by
  intro input s ev hev
  simp [h.events_eq, h.honestEvents_eq] at hev

theorem events_call_of_noEvents (impl : Impl B c) [h : NoEvents impl] (s : B.State) (input : c.Input B.Var) :
    (impl.toSubcircuit s input).events = [] :=
  h.events_eq input s

theorem honestEvents_call_of_noEvents (impl : Impl B c) [h : NoEvents impl] (s : B.State)
    (input : c.Input B.Var) : (impl.toSubcircuit s input).honestEvents = [] :=
  h.honestEvents_eq input s

/-- Refinement does not change the circuit. -/
instance (impl : Impl B c) [h : NoEvents impl]
    {Assumptions : c.input → Prop} {Spec : c.input → c.output → Prop}
    {ProverAssumptions : c.input → Prop} {ProverSpec : c.input → c.output → Prop}
    (hr : c.Refines Assumptions Spec ProverAssumptions ProverSpec) :
    NoEvents (impl.refine hr) where
  events_eq := h.events_eq
  honestEvents_eq := h.honestEvents_eq

end Impl

/-! ## Tactics -/

/--
Discharge `Impl.NoEvents`: normalize the operations, where every call to an implementation
without rare events contributes none.
-/
syntax "no_events" (" [" term,* "]")? : tactic

/--
Reduce `Impl.Phased` to its real obligations. Normalizes the operations and splits them: calls to
implementations without rare events are discharged, a call to a phased implementation leaves two
`Determined` goals (the caller's committed key determines the callee's; the callee's challenge
determines the caller's), a rare event leaves `RareEvent.Phased`, and anything else (a loop, say)
is left as it is. Loops are split into their iterations. `phased [d₁, d₂]` also unfolds the
definitions `dᵢ`.
-/
syntax "phased" (" [" term,* "]")? : tactic

meta section
open Lean Elab Tactic Meta

/-- Split `Ops.Phased` goals along the operations, and discharge what is mechanical. -/
partial def phasedSplit : TacticM Unit := do
  let goals ← getUnsolvedGoals
  let mut rest := #[]
  for goal in goals do
    setGoals [goal]
    let ty ← instantiateMVars (← goal.getType)
    if ty.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| constructor))
      phasedSplit
      rest := rest ++ (← getUnsolvedGoals)
      continue
    let saved ← saveState
    try
      evalTactic (← `(tactic| first
        | exact Ops.phased_nil
        | rw [Ops.phased_cons_native]
        | rw [Ops.phased_cons_call]
        | rw [Ops.phased_cons_rare]
        | rw [Ops.phased_cons_rareHonest]))
      phasedSplit
      rest := rest ++ (← getUnsolvedGoals)
      continue
    catch _ => saved.restore
    if ty.isAppOf ``Determined then
      -- unfold the keys to values; close it if the values are literally the same
      evalTactic (← `(tactic| intro e₁ e₂ hd))
      evalTactic (← `(tactic| try
        simp only [Interface.Phases.key, Interface.Phases.chal, circuit_norm, Prod.mk.injEq] at hd ⊢))
      evalTactic (← `(tactic| try first
        | (simp_all; done)
        | (simp_all [Vector.ext_iff]; done)
        | (simp only [Vector.map_append, *]; done)))
      rest := rest ++ (← getUnsolvedGoals)
      continue
    let saved ← saveState
    try
      Term.withoutErrToSorry <| evalTactic (← `(tactic| exact Impl.phased_call_of_noEvents _ _ _))
      continue
    catch _ => saved.restore
    let saved ← saveState
    try
      -- a loop: every iteration
      evalTactic (← `(tactic| first
        | (refine Circuit.foldr_phased _ _ (fun _ _ _ => ?_) _; simp only [circuit_norm])
        | (refine Circuit.mapFin_phased _ (fun _ _ => ?_) _; simp only [circuit_norm])))
      phasedSplit
      rest := rest ++ (← getUnsolvedGoals)
      continue
    catch _ => saved.restore
    let saved ← saveState
    try
      Term.withoutErrToSorry <| evalTactic (← `(tactic| first
        | apply Impl.phased_call | apply RareEvent.ofNative_phased | apply RareEvent.ofType_phased))
      phasedSplit
      rest := rest ++ (← getUnsolvedGoals)
      continue
    catch _ => saved.restore
    rest := rest.push goal
  setGoals rest.toList

/-- Close `events = []` and `honestEvents = []` goals: normalize, split, and go into loops. -/
partial def noEventsSplit (lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  let goals ← getUnsolvedGoals
  for goal in goals do
    setGoals [goal]
    evalTactic (← `(tactic| try simp only [circuit_norm, Impl.events_call_of_noEvents,
      Impl.honestEvents_call_of_noEvents, Ops.events_append, Ops.honestEvents_append, List.append_eq_nil_iff,
      $lemmas,*]))
    for g in ← getUnsolvedGoals do
      setGoals [g]
      let ty ← instantiateMVars (← g.getType)
      if ty.isAppOfArity ``And 2 then
        evalTactic (← `(tactic| constructor))
        noEventsSplit lemmas
        continue
      evalTactic (← `(tactic| first
        | refine Circuit.foldr_events _ _ (fun _ _ _ => ?_) _
        | refine Circuit.foldr_honestEvents _ _ (fun _ _ _ => ?_) _
        | refine Circuit.mapFin_events _ (fun _ _ => ?_) _
        | refine Circuit.mapFin_honestEvents _ (fun _ _ => ?_) _))
      noEventsSplit lemmas

elab_rules : tactic
  | `(tactic| no_events $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let lemmas ← extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    evalTactic (← `(tactic| constructor))
    let goals ← getUnsolvedGoals
    for goal in goals do
      setGoals [goal]
      evalTactic (← `(tactic| intro input s))
      destructProds
      noEventsSplit lemmas

  | `(tactic| phased $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let lemmas ← extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    evalTactic (← `(tactic| constructor))
    evalTactic (← `(tactic| intro input s))
    destructProds
    evalTactic (← `(tactic| simp only [circuit_norm, $lemmas,*]))
    phasedSplit

end

end Clean2
