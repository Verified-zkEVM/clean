module

public import CleanCompStark.Soundness
public import CleanCompStark.Buses
public import CompStark.BatchSoundness
public import CompStark.BatchNonInteractive
public import CompStark.Sound.Inclusion

/-!
# An ensemble as a batch STARK

An ensemble's components become the instances of a CompStark batch (`toBatchSetup`), each with
its AIR (`toAir`). Their interactions are the batch's global lookups, one bus per channel name.
Traces satisfying the batch are a witness of the ensemble's statement (`statement_of_satisfied`):
the tables read off the traces (`toTable`) satisfy their constraints, and every channel balances
because its bus does. This needs, beyond `bridgeable` components, that the verifier has no
interactions, that channels are told apart by their names, and that the number of interactions
stays below the characteristic, as Clean's balance requires (`EnsembleBridgeable`).
-/

@[expose] public section

namespace CleanCompStark
open Air.Flat Backends CompStark CompStark.Stark CompStark.Iop

variable {F : Type} [FiniteField F] {K : Type} [BaseField K] {EF : Type} [Challenge K EF]
  (e : F ≃+* K) {PublicIO : TypeMap} [ProvableType PublicIO]

/-- What an ensemble needs for a batch of its components' AIRs to prove its statement: bridgeable
components, a verifier without interactions, and channels told apart by their names, which name
the buses. -/
structure EnsembleBridgeable (ens : Ensemble F PublicIO) : Prop where
  components : ∀ component ∈ ens.tables, bridgeable component = true
  verifier : ens.verifier = .empty F PublicIO
  names : (ens.channels.map (·.name)).Nodup
  channels : ∀ component ∈ ens.tables, ∀ i ∈ component.rowOperations.interactions,
    ∀ channel ∈ ens.channels, i.channel.name = channel.name → i.channel = channel

/-- Component `i` of an ensemble of `k` components. -/
abbrev componentAt (ens : Ensemble F PublicIO) {k : ℕ} (hk : ens.tables.length = k) (i : Fin k) :
    Component F :=
  ens.tables[i.val]'(Nat.lt_of_lt_of_eq i.isLt hk.symm)

/-- A batch proves an ensemble: one instance per component, with the component's AIR. -/
structure ProvesEnsemble (S : Batch.Setup EF) (ens : Ensemble F PublicIO) : Prop where
  length : ens.tables.length = S.k
  air : ∀ i : Fin S.k, S.air i = toAir e (componentAt ens length i) (S.logN i)

/-- The batch STARK of an ensemble on traces of `2 ^ logN i` rows: one instance per component, with
its AIR (`toAir`), given the batch's validity. -/
def toBatchSetup (ens : Ensemble F PublicIO) (params : Fri.Params)
    (logN : Fin ens.tables.length → ℕ)
    (valid : ∀ i, ValidConfig params (toAir e ens.tables[i] (logN i)) (logN i))
    (folds : ∀ i, params.logFinalPolyLen < logN i) (nonempty : 0 < ens.tables.length)
    (lookupsValid : ∀ i, LookupsValid params (toAir e ens.tables[i] (logN i)) (logN i)
      (Batch.instanceLookups true (toAir e ens.tables[i] (logN i)) (logN i)))
    (buses : Batch.BusesValid (List.ofFn fun i =>
      Batch.instanceLookups true (toAir e ens.tables[i] (logN i)) (logN i))) :
    Batch.Setup EF where
  params
  k := ens.tables.length
  air i := toAir e ens.tables[i] (logN i)
  logN
  valid
  folds
  nonempty
  lookupsValid
  buses

theorem provesEnsemble_toBatchSetup (ens : Ensemble F PublicIO) (params : Fri.Params)
    (logN : Fin ens.tables.length → ℕ) valid folds nonempty lookupsValid buses :
    ProvesEnsemble e (toBatchSetup (EF := EF) e ens params logN valid folds nonempty lookupsValid
      buses) ens :=
  ⟨rfl, fun _ => rfl⟩

/-- The number of interactions of the tables of an ensemble with `2 ^ logN i` rows. -/
def interactionCount (ens : Ensemble F PublicIO) {k : ℕ} (hk : ens.tables.length = k)
    (logN : Fin k → ℕ) : ℕ :=
  ((List.finRange k).map fun i =>
    2 ^ logN i * (componentAt ens hk i).rowOperations.interactions.length).sum

/-! ### Sums -/

theorem sum_filter_eq {α M : Type*} [AddCommMonoid M] (p : α → Bool) (f : α → M) :
    ∀ L : List α, ((L.filter p).map f).sum = (L.map fun a => if p a then f a else 0).sum
  | [] => rfl
  | a :: L => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← sum_filter_eq p f L]
    split <;> simp_all

theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (g : α → List β) (f : β → M) :
    ∀ L : List α, ((L.flatMap g).map f).sum = (L.map fun a => ((g a).map f).sum).sum
  | [] => rfl
  | a :: L => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_map_flatMap g f L, List.map_cons,
      List.sum_cons]

theorem balanceOf_flatMap {α : Type*} (g : α → List (Interaction F)) (msg : Array F) :
    ∀ L : List α, balanceOf (L.flatMap g) msg = (L.map fun a => balanceOf (g a) msg).sum
  | [] => by simp [balanceOf]
  | a :: L => by
    rw [List.flatMap_cons, balanceOf_append, balanceOf_flatMap g msg L, List.map_cons,
      List.sum_cons]

theorem balanceOf_eq_sum (L : List (Interaction F)) (msg : Array F) :
    balanceOf L msg = (L.map fun i => if i.msg = msg then i.mult else 0).sum := by
  rw [balanceOf, sum_filter_eq]
  simp only [decide_eq_true_eq]

theorem sum_map_eq_neg {α : Type*} (g : α → K) (h : α → F) :
    ∀ l : List α, (∀ a ∈ l, g a = -e (h a)) → (l.map g).sum = -e ((l.map h).sum)
  | [], _ => by simp
  | a :: l, hl => by
    rw [List.map_cons, List.sum_cons, hl a List.mem_cons_self,
      sum_map_eq_neg g h l fun b hb => hl b (List.mem_cons_of_mem _ hb), List.map_cons,
      List.sum_cons, map_add, neg_add]

/-! ### One row's balance -/

theorem eval_cellExpr_publicValues (component : Component F) (A : Air K) (logN : ℕ)
    (trace : Array K) (publicValues publicValues' : List K) (r j : ℕ) :
    (cellExpr component j).eval (Lookup.generationRow A logN trace publicValues r) =
      (cellExpr component j).eval (Lookup.generationRow A logN trace publicValues' r) := by
  unfold cellExpr
  split <;> dsimp only <;> split_ifs <;> rfl

theorem eval_toExpr_publicValues (component : Component F) (A : Air K) (logN : ℕ)
    (trace : Array K) (publicValues publicValues' : List K) (r : ℕ) :
    ∀ x : Expression F,
      (toExpr e component x).eval (Lookup.generationRow A logN trace publicValues r) =
        (toExpr e component x).eval (Lookup.generationRow A logN trace publicValues' r)
  | .var v => eval_cellExpr_publicValues component A logN trace publicValues publicValues' r _
  | .const _ => rfl
  | .add a b | .mul a b => by
    simp only [toExpr, Expr.eval]
    rw [eval_toExpr_publicValues component A logN trace publicValues publicValues' r a,
      eval_toExpr_publicValues component A logN trace publicValues publicValues' r b]

/-- An interaction expression on a row read off the trace, mapped to `K`, is its AIR expression on
the trace's row. -/
theorem eval_toExpr_interaction {component : Component F} (hc : bridgeable component = true)
    (logN : ℕ) (trace : Array K) (publicValues : List K) (r : ℕ) (data : ProverData F)
    {x : Expression F} {a : AbstractInteraction F} (ha : a ∈ component.rowOperations.interactions)
    (hx : x ∈ a.mult :: a.msg.toList) :
    (toExpr e component x).eval
        (Lookup.generationRow (toAir e component logN) logN trace publicValues r) =
      e (Expression.eval (Environment.fromArray (toRow e component logN trace r) data) x) := by
  have hcells := Bridgeable.cells_lt hc x
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hx⟩))
  rw [eval_toRow e logN trace component r data x hcells, RingEquiv.apply_symm_apply]
  exact eval_toExpr_publicValues e component _ logN trace publicValues [] r x

/-- **One row's balance.** On a row of a bridgeable component's AIR, the multiplicities of the
tuples with the values `msg` on the bus of a channel sum to the negated multiplicities of the
row's interactions with `msg` on the channel, given bus numbers `ids` that name the buses through
`N`. -/
theorem rowBalance {component : Component F} (hc : bridgeable component = true)
    {channel : RawChannel F}
    (hchannel : ∀ a ∈ component.rowOperations.interactions, a.channel.name = channel.name →
      a.channel = channel)
    (logN : ℕ) (trace : Array K) (publicValues : List K) (r : ℕ) (data : ProverData F)
    (budget : ℕ) (ids : List ℕ) (N : String → ℕ)
    (hlen : ids.length = (Lookup.packSameBus budget (toAir e component logN).lookups).length)
    (hids : ∀ x ∈ (Lookup.packSameBus budget (toAir e component logN).lookups).zip ids,
      ∀ name, x.1.bus = some name → x.2 = N name)
    (hinj : ∀ x ∈ (Lookup.packSameBus budget (toAir e component logN).lookups).zip ids,
      ∀ name, x.1.bus = some name → x.2 = N channel.name → channel.name = name)
    (msg : Array F) :
    ((((Lookup.packSameBus budget (toAir e component logN).lookups).zip ids).flatMap
      fun (x : CompStark.Stark.Lookup K × ℕ) => x.1.tuples.map
        fun (t : List (Expr K) × Expr K) =>
        ((x.2, t.1.map (·.eval (Lookup.generationRow (toAir e component logN) logN trace
          publicValues r))),
          t.2.eval (Lookup.generationRow (toAir e component logN) logN trace publicValues r))).map
      fun (x : (ℕ × List K) × K) =>
        if x.1 = (N channel.name, msg.toList.map e) then x.2 else 0).sum =
      -e (balanceOf (component.operations.interactionValuesWith channel
        (Environment.fromArray (toRow e component logN trace r) data)) msg) := by
  set A := toAir e component logN
  set gen := Lookup.generationRow A logN trace publicValues r
  set env := Environment.fromArray (toRow e component logN trace r) data
  set L := component.rowOperations.interactions
  -- the value of a tuple with the values `msg`
  let f : List (Expr K) × Count K → K := fun t =>
    if t.1.map (·.eval gen) = msg.toList.map e then t.2.expr.eval gen else 0
  have hglobal : ∀ l ∈ Lookup.packSameBus budget A.lookups, l.bus.isSome :=
    bus_isSome_packSameBus budget A.lookups (by
      intro m hm
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hm
      rfl)
  -- the bus numbers select the bus of the channel
  rw [sum_map_flatMap]
  have hrow : ∀ x ∈ (Lookup.packSameBus budget A.lookups).zip ids,
      ((x.1.tuples.map fun (t : List (Expr K) × Expr K) =>
          ((x.2, t.1.map (·.eval gen)), t.2.eval gen)).map
        fun (y : (ℕ × List K) × K) =>
          if y.1 = (N channel.name, msg.toList.map e) then y.2 else 0).sum =
      if x.1.bus == some channel.name then (x.1.entries.map f).sum else 0 := by
    intro x hx
    obtain ⟨name, hname⟩ := Option.isSome_iff_exists.mp (hglobal x.1 (List.of_mem_zip hx).1)
    rw [List.map_map, Stark.Lookup.tuples, List.map_map]
    by_cases hc' : channel.name = name
    · subst hc'
      simp only [hname, beq_self_eq_true, ↓reduceIte]
      rw [hids x hx _ hname]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Prod.mk.injEq, true_and, f]
    · have hne : (x.1.bus == some channel.name) = false := by
        rw [hname]; simpa using Ne.symm hc'
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hy
      simp only [Function.comp_apply, Prod.mk.injEq, ite_eq_right_iff, and_imp]
      intro hb _
      exact absurd (hinj x hx name hname hb) hc'
  have hzip : ∀ G : CompStark.Stark.Lookup K → K,
      (((Lookup.packSameBus budget A.lookups).zip ids).map fun x => G x.1) =
        (Lookup.packSameBus budget A.lookups).map G := fun G => by
    conv_rhs => rw [← List.map_fst_zip (l₁ := Lookup.packSameBus budget A.lookups) (l₂ := ids)
      (by omega)]
    rw [List.map_map]
    rfl
  rw [List.map_congr_left hrow, hzip (fun l =>
      if l.bus == some channel.name then (l.entries.map f).sum else 0), ← sum_filter_eq,
    ← sum_map_flatMap, flatMap_filter_packSameBus]
  -- the bus of the channel holds the row's interactions with it
  simp only [A, toAir, List.filter_map, List.flatMap_map, toLookup]
  rw [sum_map_flatMap]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [sum_filter_eq, Operations.interactionValuesWith_eq_map,
    Operations.interactionsWith, balanceOf_eq_sum, List.map_map, sum_filter_eq,
    Component.interactions_eq]
  refine sum_map_eq_neg e _ _ _ fun a ha => ?_
  simp only [Function.comp_apply, toLookup, beq_iff_eq, Option.some.injEq, decide_eq_true_eq]
  by_cases hca : a.channel = channel
  · simp only [hca, decide_true, ↓reduceIte, f]
    have hmsg : ∀ x ∈ a.msg.toList, (toExpr e component x).eval gen = e (env x) :=
      fun x hx => eval_toExpr_interaction e hc logN trace publicValues r data ha
        (List.mem_cons_of_mem _ hx)
    have hmult : (toExpr e component a.mult).eval gen = e (env a.mult) :=
      eval_toExpr_interaction e hc logN trace publicValues r data ha List.mem_cons_self
    rw [List.map_map, List.map_congr_left (g := fun x => e (env x)) (by simpa using hmsg)]
    have hiff : (a.msg.toList.map fun x => e (env x)) = msg.toList.map e ↔
        (AbstractInteraction.eval env a).msg = msg := by
      rw [show (a.msg.toList.map fun x => e (env x)) = (a.msg.toList.map fun x => env x).map e by
        rw [List.map_map]; rfl, (List.map_injective_iff.mpr e.injective).eq_iff]
      simp only [AbstractInteraction.eval, ← Array.toList_inj, Vector.toList_toArray,
        Vector.toList_map]
    by_cases hm : (AbstractInteraction.eval env a).msg = msg
    · simp only [hiff.mpr hm, hm, ↓reduceIte]
      show (0 : K) - (toExpr e component a.mult).eval gen = -e (env a.mult)
      rw [hmult, zero_sub]
    · simp only [mt hiff.mp hm, hm, ↓reduceIte, map_zero, neg_zero]
  · have hname : ¬ a.channel.name = channel.name := fun h => hca (hchannel a ha h)
    simp only [hca, hname, decide_false, Bool.false_eq_true, ↓reduceIte, map_zero, neg_zero]

/-! ### The witness -/

theorem toRows_eq_map_range (component : Component F) (logN : ℕ) (trace : Array K) :
    toRows e component logN trace = (List.range (2 ^ logN)).map (toRow e component logN trace) := by
  apply List.ext_getElem <;> simp [toRows]

variable {S : Batch.Setup EF} {ens : Ensemble F PublicIO}

/-- The tables read off traces of a batch that proves an ensemble, with the prover data derived
from them. -/
def toTables (h : ProvesEnsemble e S ens)
    (fits : ∀ i, Fits (K := K) (componentAt ens h.length i) (S.logN i))
    (traces : Fin S.k → Array K) : List (Table F) :=
  withDerivedData (List.ofFn fun i =>
    toTable e (S.logN i) (traces i) (componentAt ens h.length i) (fits i) fun _ _ => #[])

/-- The witness of an ensemble read off traces of a batch that proves it, with the public input
`publicInput`. -/
def toWitness (h : ProvesEnsemble e S ens)
    (fits : ∀ i, Fits (K := K) (componentAt ens h.length i) (S.logN i))
    (traces : Fin S.k → Array K) (publicInput : PublicIO F) : EnsembleWitness ens where
  tables := toTables e h fits traces
  publicInput
  same_length := by simp [toTables, withDerivedData, h.length]
  same_circuits i hi := by simp [toTables, withDerivedData, toTable, componentAt]
  same_data := withDerivedData_data _

theorem toWitness_tables (h : ProvesEnsemble e S ens)
    (fits : ∀ i, Fits (K := K) (componentAt ens h.length i) (S.logN i))
    (traces : Fin S.k → Array K) (publicInput : PublicIO F) :
    (toWitness e h fits traces publicInput).tables.map (·.table) =
      List.ofFn fun i => toRows e (componentAt ens h.length i) (S.logN i) (traces i) := by
  simp [toWitness, toTables, withDerivedData, toTable, List.map_ofFn, Function.comp_def]

/-- The tables read off traces satisfying the AIRs of a batch that proves an ensemble satisfy
their constraints. -/
theorem constraints_toWitness (h : ProvesEnsemble e S ens) (hb : EnsembleBridgeable ens)
    (fits : ∀ i, Fits (K := K) (componentAt ens h.length i) (S.logN i))
    {traces : Fin S.k → Array K} {publicValues : Fin S.k → List K}
    (hsat : ∀ i, (S.air i).Satisfied (S.logN i) (traces i) (publicValues i))
    (publicInput : PublicIO F) : (toWitness e h fits traces publicInput).Constraints := by
  intro table htable
  simp only [toWitness, toTables, withDerivedData, List.mem_map, List.mem_ofFn] at htable
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := htable
  have hi := hsat i
  rw [h.air i] at hi
  exact constraints_toTable e (S.logN i) (traces i)
    (hb.components _ (List.getElem_mem _)) (fits i) _ hi.vanish

theorem lookups_eq (h : ProvesEnsemble e S ens) (i : Fin S.k) :
    S.lookups i = Lookup.packSameBus
      (2 ^ (toAir e (componentAt ens h.length i) (S.logN i)).logQuotientChunksWith (S.logN i)
        (Lookup.logUpConstraints (toAir e (componentAt ens h.length i) (S.logN i)).lookups) + 1)
      (toAir e (componentAt ens h.length i) (S.logN i)).lookups := by
  simp only [Batch.Setup.lookups, Batch.instanceLookups, ↓reduceIte, h.air i]
  rfl

/-- The number of a row's interactions on a channel is at most the number of its interactions. -/
theorem length_interactionValuesWith_le (component : Component F) (channel : RawChannel F)
    (env : Environment F) :
    (component.operations.interactionValuesWith channel env).length ≤
      component.rowOperations.interactions.length := by
  rw [Operations.interactionValuesWith_eq_map, List.length_map, Operations.interactionsWith,
    Component.interactions_eq]
  exact List.length_filter_le _ _

/-- Every channel of an ensemble balances on the tables read off traces satisfying a batch that
proves it. -/
theorem balancedChannels_toWitness (h : ProvesEnsemble e S ens) (hb : EnsembleBridgeable ens)
    (fits : ∀ i, Fits (K := K) (componentAt ens h.length i) (S.logN i))
    (hcount : interactionCount ens h.length S.logN < ringChar F)
    {traces : Fin S.k → Array K} {publicValues : Fin S.k → List K}
    (hsat : S.Satisfied traces publicValues) (publicInput : PublicIO F) :
    (toWitness e h fits traces publicInput).BalancedChannels := by
  intro channel hchannel
  rw [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_of_verifier_empty hb.verifier]
  -- the tables' interactions on the channel, row by row
  obtain ⟨data, hflat⟩ : ∃ data : ProverData F,
      (toWitness e h fits traces publicInput).tables.flatMap (·.interactionsWith channel) =
        (List.finRange S.k).flatMap fun i => (List.range (2 ^ S.logN i)).flatMap fun r =>
          (componentAt ens h.length i).operations.interactionValuesWith channel
            (Environment.fromArray (toRow e (componentAt ens h.length i) (S.logN i) (traces i) r)
              data) := by
    refine ⟨deriveProverData (List.ofFn fun i =>
      toTable e (S.logN i) (traces i) (componentAt ens h.length i) (fits i) fun _ _ => #[]), ?_⟩
    simp only [toWitness, toTables, withDerivedData, List.flatMap_map, List.ofFn_eq_map]
    refine List.flatMap_congr fun i _ => ?_
    simp only [Table.interactionsWith, toTable, toRows_eq_map_range, List.flatMap_map,
      Table.environment]
  rw [hflat]
  constructor
  · left
    refine lt_of_le_of_lt ?_ hcount
    rw [List.length_flatMap, interactionCount]
    refine List.sum_le_sum fun i _ => ?_
    rw [List.length_flatMap]
    calc ((List.range (2 ^ S.logN i)).map fun r => _).sum
        ≤ ((List.range (2 ^ S.logN i)).map fun _ =>
            (componentAt ens h.length i).rowOperations.interactions.length).sum :=
          List.sum_le_sum fun r _ => length_interactionValuesWith_le _ _ _
      _ = _ := by simp
  · intro msg
    have hbal := hsat.balanced (busNumber (List.ofFn S.lookups) channel.name, msg.toList.map e)
    rw [Sound.Batch.sum_filter_key, Sound.Batch.messages_eq, sum_map_flatMap] at hbal
    rw [balanceOf_flatMap]
    apply e.injective
    rw [map_zero, ← neg_eq_zero, ← hbal]
    symm
    refine sum_map_eq_neg e _ _ _ fun i _ => ?_
    rw [balanceOf_flatMap, Sound.Batch.instanceMessages, sum_map_flatMap]
    refine sum_map_eq_neg e _ _ _ fun r _ => ?_
    have hmem : ∀ x ∈ (S.lookups i).zip (Sound.Batch.busNumbers S i),
        x ∈ ((List.ofFn S.lookups)[i.val]'(by simp)).zip
          ((Lookup.busIds (List.ofFn S.lookups)).getD i []) := by
      intro x hx
      simpa only [List.getElem_ofFn] using hx
    have hlen := Sound.Batch.length_busNumbers S i
    rw [lookups_eq e h i] at hmem hlen ⊢
    rw [h.air i]
    have hcomponent := List.getElem_mem (l := ens.tables) (Nat.lt_of_lt_of_eq i.isLt h.length.symm)
    exact rowBalance e (hb.components _ hcomponent)
      (fun a ha hname => hb.channels _ hcomponent a ha channel hchannel hname) (S.logN i)
      (traces i) (publicValues i) r data _ _ (busNumber (List.ofFn S.lookups)) hlen
      (fun x hx name hname => busIds_eq_busNumber _ i (by simp) x (hmem x hx) name hname)
      (fun x hx name hname hb' => busNumber_inj _ i (by simp) x (hmem x hx) name _ hname hb') msg

/-- **The transfer theorem for an ensemble.** Traces satisfying a batch that proves a bridgeable
ensemble, whose tables have fewer interactions than the characteristic, are a witness of the
ensemble's statement for every public input: the tables read off the traces (`toWitness`) satisfy
their constraints, and every channel balances. -/
theorem statement_of_satisfied (h : ProvesEnsemble e S ens) (hb : EnsembleBridgeable ens)
    (fits : ∀ i, Fits (K := K) (componentAt ens h.length i) (S.logN i))
    (hcount : interactionCount ens h.length S.logN < ringChar F)
    {traces : Fin S.k → Array K} {publicValues : Fin S.k → List K}
    (hsat : S.Satisfied traces publicValues) (publicInput : PublicIO F) :
    ens.Statement publicInput :=
  ⟨toWitness e h fits traces publicInput, rfl,
    constraints_toWitness e h hb fits hsat.air publicInput,
    balancedChannels_toWitness e h hb fits hcount hsat publicInput⟩

/-! ### Knowledge soundness -/

/-- A property of the tables of an ensemble's witnesses that its statement proves: the rows of
every witness whose constraints hold and whose channels balance satisfy `P`. -/
def WitnessSound (ens : Ensemble F PublicIO) (P : List (List (Array F)) → Prop) : Prop :=
  ∀ witness : EnsembleWitness ens, witness.Constraints → witness.BalancedChannels →
    P (witness.tables.map (·.table))

/-- **Knowledge soundness of an ensemble's batch STARK.** If a batch proves a bridgeable ensemble
and the ensemble proves `P` of its witnesses' tables, the verifier accepts a prover with
probability at most the knowledge error unless the rows read off some tuple of traces, each within
`δ'` of its instance's committed trace, satisfy `P`. -/
theorem batchKnowledgeSoundness_of_witnessSound (h : ProvesEnsemble e S ens)
    (hb : EnsembleBridgeable ens)
    (fits : ∀ i, Fits (K := K) (componentAt ens h.length i) (S.logN i))
    (hcount : interactionCount ens h.length S.logN < ringChar F) {P : List (List (Array F)) → Prop}
    (hP : WitnessSound ens P) (publicInput : PublicIO F) (publicValues : Fin S.k → List K)
    (prover : Batch.Prover S) (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) :
    (∀ traces ∈ Batch.closeTraces S δ' prover.trace,
      ¬ P (List.ofFn fun i => toRows e (componentAt ens h.length i) (S.logN i) (traces i))) →
      Batch.acceptance publicValues prover ≤ Batch.knowledgeError S δ δ' := fun hfar ↦
  batchKnowledgeSoundness S publicValues prover δ δ' hδ' fun traces ht hsat ↦ by
    have := hP (toWitness e h fits traces publicInput)
      (constraints_toWitness e h hb fits hsat.air publicInput)
      (balancedChannels_toWitness e h hb fits hcount hsat publicInput)
    rw [toWitness_tables] at this
    exact hfar traces ht this

/-- **Knowledge soundness of an ensemble's batch STARK, from the ensemble's soundness.** If a batch
proves a bridgeable ensemble that is sound for `Assumptions` and `Spec`, and a public input
satisfies the assumptions but not the spec, the verifier accepts a prover with probability at most
the knowledge error. -/
theorem batchKnowledgeSoundness_of_soundness (h : ProvesEnsemble e S ens)
    (hb : EnsembleBridgeable ens)
    (fits : ∀ i, Fits (K := K) (componentAt ens h.length i) (S.logN i))
    (hcount : interactionCount ens h.length S.logN < ringChar F)
    {Assumptions Spec : PublicIO F → Prop} (hsound : ens.Soundness Assumptions Spec)
    {publicInput : PublicIO F} (hassumptions : Assumptions publicInput)
    (hspec : ¬ Spec publicInput) (publicValues : Fin S.k → List K) (prover : Batch.Prover S)
    (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) :
    Batch.acceptance publicValues prover ≤ Batch.knowledgeError S δ δ' :=
  batchKnowledgeSoundness S publicValues prover δ δ' hδ' fun _ _ hsat ↦
    hspec (hsound publicInput hassumptions
      (statement_of_satisfied e h hb fits hcount hsat publicInput))

/-- **Knowledge soundness of an ensemble's batch STARK in the random-oracle model.** If a batch
proves a bridgeable ensemble and the ensemble proves `P` of its witnesses' tables, a prover making
at most `Q` oracle calls gets a proof accepted while the rows read off no tuple of traces close to
the ones it committed to satisfy `P` with probability at most `q · roundError + hashError q`,
`q = Q + verifierQueries`. -/
theorem batchKnowledgeSoundness_ro_of_witnessSound (h : ProvesEnsemble e S ens)
    (hb : EnsembleBridgeable ens)
    (fits : ∀ i, Fits (K := K) (componentAt ens h.length i) (S.logN i))
    (hcount : interactionCount ens h.length S.logN < ringChar F) {P : List (List (Array F)) → Prop}
    (hP : WitnessSound ens P) (publicInput : PublicIO F) (publicValues : Fin S.k → List K)
    (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : ℕ) (prover : Batch.NIProver S)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← Batch.run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn S.logN ∧
        ∀ traces ∈ Batch.closeTraces S δ' (Batch.committedTraces S log proof),
          ¬ P (List.ofFn fun i => toRows e (componentAt ens h.length i) (S.logN i) (traces i))] ≤
      (Q + S.verifierQueries) * Batch.roundError S δ δ' +
        hashError K (Q + S.verifierQueries) :=
  (prEvent_mono _ _ _ fun ⟨_, _, _⟩ hev ↦ ⟨hev.1, hev.2.1, fun traces ht hsat ↦ by
    have := hP (toWitness e h fits traces publicInput)
      (constraints_toWitness e h hb fits hsat.air publicInput)
      (balancedChannels_toWitness e h hb fits hcount hsat publicInput)
    rw [toWitness_tables] at this
    exact hev.2.2 traces ht this⟩).trans
    (Batch.batchKnowledgeSoundness_ro S publicValues δ δ' hδ' Q prover hQ)

end CleanCompStark
