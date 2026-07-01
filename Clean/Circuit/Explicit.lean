/-
This file introduces `ExplicitCircuit`, a variant of `ElaboratedCircuit` that can be auto-derived
using the `infer_explicit_circuit(s)` tactic.

This could be useful to simplify circuit statements with less user intervention.
-/
import Clean.Utils.Misc
import Clean.Circuit.Basic
import Clean.Circuit.ExplicitAttributes
import Lean.Elab.Tactic
import Mathlib.Lean.Meta.Simp

open Lean Meta Elab Tactic

register_option debug.elaborateCircuit : Bool := {
  defValue := false
  descr := "trace generated dsimp unfold sets used by elaborate_circuit"
}

variable {n : ℕ} {F : Type} [FiniteField F] {α β : Type}

class ExplicitCircuit (circuit : Circuit F α) where
  /-- an "explicit" circuit is encapsulated by three functions of the input offset -/
  output : ℕ → α
  localLength : ℕ → ℕ
  operations : ℕ → Operations F

  /-- the functions have to match the circuit -/
  output_eq : ∀ n : ℕ, circuit.output n = output n := by intro _; rfl
  localLength_eq : ∀ n : ℕ, circuit.localLength n = localLength n := by intro _; rfl
  operations_eq : ∀ n : ℕ, circuit.operations n = operations n := by intro _; rfl

  /-- same condition as in `ElaboratedCircuit`: subcircuits must be consistent with the current offset -/
  subcircuitsConsistent : ∀ n : ℕ, (circuit.operations n).SubcircuitsConsistent n := by
    intro _; and_intros <;> try first | ac_rfl | trivial
  /-- channel metadata explicitly collected from the circuit structure -/
  channelsWithGuarantees : ℕ → List (RawChannel F)
  channelsLawful : ∀ n : ℕ, (circuit.operations n).ChannelsLawful
      (channelsWithGuarantees n) := by
    intro n
    try rw [operations_eq n]
    try dsimp only [channelsWithGuarantees, operations]
    simp [circuit_norm]
    all_goals try first | ac_rfl | trivial | tauto

/-- family of explicit circuits -/
class ExplicitCircuits (circuit : α → Circuit F β) where
  output : α → ℕ → β
  localLength : α → ℕ → ℕ
  operations : α → ℕ → Operations F
  output_eq : ∀ (a : α) (n : ℕ), (circuit a).output n = output a n := by intro _ _; rfl
  localLength_eq : ∀ (a : α) (n : ℕ), (circuit a).localLength n = localLength a n := by intro _ _; rfl
  operations_eq : ∀ (a : α) (n : ℕ), (circuit a).operations n = operations a n := by intro _ _; rfl
  subcircuitsConsistent : ∀ (a : α) (n : ℕ), ((circuit a).operations n).SubcircuitsConsistent n := by
    intro _ _; and_intros <;> try first | ac_rfl | trivial
  /-- channel metadata explicitly collected from the circuit structure -/
  channelsWithGuarantees : α → ℕ → List (RawChannel F)
  channelsLawful : ∀ (a : α) (n : ℕ), ((circuit a).operations n).ChannelsLawful
      (channelsWithGuarantees a n) := by
    intro a n
    try rw [operations_eq a n]
    try dsimp only [channelsWithGuarantees, operations]
    simp [Operations.ChannelsLawful, circuit_norm]
    all_goals try first | ac_rfl | trivial | tauto

/-- From an `ExplicitCircuit`, we can usually derive an `ElaboratedCircuit` -/
class ExplicitCircuits.IsElaborated (circuit : α → Circuit F β) (explicit : ExplicitCircuits circuit) where
  localLength_eq : ∀ (a : α) (n m : ℕ),
    explicit.localLength a n = explicit.localLength a m := by intros; rfl
  channelsWithGuarantees_eq : ∀ (a a' : α) (n m : ℕ),
    explicit.channelsWithGuarantees a n = explicit.channelsWithGuarantees a' m := by intros; rfl

@[circuit_norm, explicit_circuit_norm]
def ExplicitCircuits.toElaborated {Input Output : TypeMap}
  [CircuitType Input] [CircuitType Output] [Inhabited (Var Input F)]
  (circuit : Var Input F → Circuit F (Var Output F))
  (explicit : ExplicitCircuits circuit)
  (explicit_elaborated : ExplicitCircuits.IsElaborated circuit explicit) :
    ElaboratedCircuit F Input Output circuit where
  localLength a := explicit.localLength a 0
  output a n := explicit.output a n
  localLength_eq a n := by
    rw [explicit.localLength_eq, explicit_elaborated.localLength_eq a n 0]
  output_eq a n := explicit.output_eq a n
  subcircuitsConsistent a n := explicit.subcircuitsConsistent a n
  channelsWithGuarantees := explicit.channelsWithGuarantees default 0
  channelsLawful a n := by
    convert explicit.channelsLawful a n using 1
    rw [explicit_elaborated.channelsWithGuarantees_eq]

@[circuit_norm, explicit_circuit_norm]
def ElaboratedCircuit.fromExplicit {Input Output : TypeMap}
  [CircuitType Input] [CircuitType Output] [Inhabited (Var Input F)]
  {circuit : Var Input F → Circuit F (Var Output F)}
  (explicit : ExplicitCircuits circuit)
  (explicit_elaborated : ExplicitCircuits.IsElaborated circuit explicit) :
    ElaboratedCircuit F Input Output circuit := explicit.toElaborated _ explicit_elaborated

theorem ExplicitCircuits.toElaborated_localLength {Input Output : TypeMap}
    [CircuitType Input] [CircuitType Output] [Inhabited (Var Input F)]
    {circuit : Var Input F → Circuit F (Var Output F)}
    (explicit : ExplicitCircuits circuit)
    (explicit_elaborated : ExplicitCircuits.IsElaborated circuit explicit) (a : Var Input F) :
    (ExplicitCircuits.toElaborated circuit explicit explicit_elaborated).localLength a =
      explicit.localLength a 0 := rfl

theorem ExplicitCircuits.toElaborated_output {Input Output : TypeMap}
    [CircuitType Input] [CircuitType Output] [Inhabited (Var Input F)]
    {circuit : Var Input F → Circuit F (Var Output F)}
    (explicit : ExplicitCircuits circuit)
    (explicit_elaborated : ExplicitCircuits.IsElaborated circuit explicit) (a : Var Input F) (n : ℕ) :
    (ExplicitCircuits.toElaborated circuit explicit explicit_elaborated).output a n =
      explicit.output a n := rfl

theorem ExplicitCircuits.toElaborated_channelsWithGuarantees {Input Output : TypeMap}
    [CircuitType Input] [CircuitType Output] [Inhabited (Var Input F)]
    {circuit : Var Input F → Circuit F (Var Output F)}
    (explicit : ExplicitCircuits circuit)
    (explicit_elaborated : ExplicitCircuits.IsElaborated circuit explicit) :
    (ExplicitCircuits.toElaborated circuit explicit explicit_elaborated).channelsWithGuarantees =
      explicit.channelsWithGuarantees default 0 := rfl

structure ElaboratedCircuit.Data {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    {circuit : Var Input F → Circuit F (Var Output F)} (elaborated : ElaboratedCircuit F Input Output circuit) where
  localLength : Var Input F → ℕ := elaborated.localLength
  output : Var Input F → ℕ → Var Output F := elaborated.output
  channelsWithGuarantees : List (RawChannel F) := elaborated.channelsWithGuarantees

@[circuit_norm, explicit_circuit_norm]
def ElaboratedCircuit.withData {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
  {circuit : Var Input F → Circuit F (Var Output F)}
  (derived : ElaboratedCircuit F Input Output circuit)
  (data : ElaboratedCircuit.Data derived)
  (data_eq :
    (∀ a, derived.localLength a = data.localLength a) ∧
    (∀ a n, derived.output a n = data.output a n) ∧
    (derived.channelsWithGuarantees ⊆ data.channelsWithGuarantees) := by
      and_intros
      · intro a; ac_rfl
      · intro a n; rfl
      · try simp only [circuit_norm]; try grind; done) :
    ElaboratedCircuit F Input Output circuit where
  localLength := data.localLength
  output := data.output
  localLength_eq a n := by
    rw [derived.localLength_eq, data_eq.1]
  output_eq a n := by
    rw [derived.output_eq, data_eq.2.1]
  subcircuitsConsistent := derived.subcircuitsConsistent
  channelsWithGuarantees := data.channelsWithGuarantees
  channelsLawful a n := by
    have h_lawful := derived.channelsLawful a n
    have channelsWithGuarantees_subset := data_eq.2.2
    dsimp only [Operations.ChannelsLawful] at h_lawful ⊢
    obtain ⟨h_g_sub, h_g, h_sub⟩ := h_lawful
    and_intros
    · exact List.Subset.trans h_g_sub channelsWithGuarantees_subset
    · intro env
      exact (h_g env).mono channelsWithGuarantees_subset
    · exact h_sub

theorem ElaboratedCircuit.withData_localLength {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    {circuit : Var Input F → Circuit F (Var Output F)}
    (derived : ElaboratedCircuit F Input Output circuit)
    (data : ElaboratedCircuit.Data derived) (data_eq) (a : Var Input F) :
    (ElaboratedCircuit.withData derived data data_eq).localLength a = data.localLength a := rfl

theorem ElaboratedCircuit.withData_output {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    {circuit : Var Input F → Circuit F (Var Output F)}
    (derived : ElaboratedCircuit F Input Output circuit)
    (data : ElaboratedCircuit.Data derived) (data_eq) (a : Var Input F) (n : ℕ) :
    (ElaboratedCircuit.withData derived data data_eq).output a n = data.output a n := rfl

theorem ElaboratedCircuit.withData_channelsWithGuarantees {Input Output : TypeMap}
    [CircuitType Input] [CircuitType Output]
    {circuit : Var Input F → Circuit F (Var Output F)}
    (derived : ElaboratedCircuit F Input Output circuit)
    (data : ElaboratedCircuit.Data derived) (data_eq) :
    (ElaboratedCircuit.withData derived data data_eq).channelsWithGuarantees = data.channelsWithGuarantees := rfl

-- move between family and single explicit circuit

def ExplicitCircuits.fromSingle {circuit : α → Circuit F β}
    (explicit : ∀ a, ExplicitCircuit (circuit a)) : ExplicitCircuits circuit where
  output a n := (explicit a).output n
  localLength a n := (explicit a).localLength n
  operations a n := (explicit a).operations n
  output_eq a n := (explicit a).output_eq n
  localLength_eq a n := (explicit a).localLength_eq n
  operations_eq a n := (explicit a).operations_eq n
  subcircuitsConsistent a n := (explicit a).subcircuitsConsistent n
  channelsWithGuarantees a n := (explicit a).channelsWithGuarantees n
  channelsLawful a n := (explicit a).channelsLawful n

instance ExplicitCircuits.toSingle (circuit : α → Circuit F β) (a : α)
    [explicit : ExplicitCircuits circuit] : ExplicitCircuit (circuit a) where
  output n := output circuit a n
  localLength n := explicit.localLength a n
  operations n := operations circuit a n
  output_eq n := output_eq a n
  localLength_eq n := localLength_eq a n
  operations_eq n := operations_eq a n
  subcircuitsConsistent n := subcircuitsConsistent a n
  channelsWithGuarantees n := channelsWithGuarantees circuit a n
  channelsLawful n := channelsLawful a n

instance ExplicitCircuits.fromProvableInputOutput {α β : TypeMap} [ProvableType α] [ProvableType β]
  {circuit : Var α F → Circuit F (Var β F)} [explicit : ExplicitCircuits circuit] :
  ExplicitCircuits (circuit : α (Expression F) → Circuit F (β (Expression F))) := explicit

-- `pure` is an explicit circuit
@[explicit_circuit_constructor]
instance ExplicitCircuit.from_pure {a : α} : ExplicitCircuit (pure a : Circuit F α) where
  output _ := a
  localLength _ := 0
  operations _ := []
  channelsWithGuarantees _ := []

instance ExplicitCircuits.from_pure {f : α → β} : ExplicitCircuits (fun a => pure (f a) : α → Circuit F β) where
  output a _ := f a
  localLength _ _ := 0
  operations _ _ := []
  channelsWithGuarantees _ _ := []

-- `bind` of two explicit circuits yields an explicit circuit
@[explicit_circuit_constructor]
instance ExplicitCircuit.from_bind {f : Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) : ExplicitCircuit (f >>= g) where
  output n :=
    let a := output f n
    output (g a) (n + localLength f n)

  localLength n :=
    let a := output f n
    localLength f n + localLength (g a) (n + localLength f n)

  operations n :=
    let a := output f n
    operations f n ++ operations (g a) (n + localLength f n)

  channelsWithGuarantees n :=
    let a := output f n
    channelsWithGuarantees f n ++ channelsWithGuarantees (g a) (n + localLength f n)

  output_eq n := by rw [Circuit.bind_output_eq, output_eq, output_eq, localLength_eq]
  localLength_eq n := by rw [Circuit.bind_localLength_eq, localLength_eq, output_eq, localLength_eq]
  operations_eq n := by rw [Circuit.bind_operations_eq, operations_eq, output_eq, localLength_eq, operations_eq]
  subcircuitsConsistent n := by
    rw [Operations.SubcircuitsConsistent, Circuit.bind_forAll]
    exact ⟨ f_explicit.subcircuitsConsistent .., (g_explicit _).subcircuitsConsistent .. ⟩
  channelsLawful n := by
    rw [Circuit.bind_operations_eq, output_eq, localLength_eq]
    apply Operations.channelsLawful_append_of_channelsLawful
    · exact f_explicit.channelsLawful n
    · exact (g_explicit (output f n)).channelsLawful (n + localLength f n)

instance ExplicitCircuit.from_bind_tc {f : Circuit F α} {g : α → Circuit F β}
    [f_explicit : ExplicitCircuit f] [g_explicit : ∀ a : α, ExplicitCircuit (g a)] :
    ExplicitCircuit (f >>= g) :=
  ExplicitCircuit.from_bind f_explicit g_explicit

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_bind_output {f : Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) (n : ℕ) :
    @ExplicitCircuit.output F _ β (f >>= g) (ExplicitCircuit.from_bind f_explicit g_explicit) n =
      ExplicitCircuit.output (g (ExplicitCircuit.output f n)) (n + ExplicitCircuit.localLength f n) := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_bind_localLength {f : Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) (n : ℕ) :
    @ExplicitCircuit.localLength F _ β (f >>= g) (ExplicitCircuit.from_bind f_explicit g_explicit) n =
      ExplicitCircuit.localLength f n +
        ExplicitCircuit.localLength (g (ExplicitCircuit.output f n)) (n + ExplicitCircuit.localLength f n) := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_bind_operations {f : Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) (n : ℕ) :
    @ExplicitCircuit.operations F _ β (f >>= g) (ExplicitCircuit.from_bind f_explicit g_explicit) n =
      ExplicitCircuit.operations f n ++
        ExplicitCircuit.operations (g (ExplicitCircuit.output f n)) (n + ExplicitCircuit.localLength f n) := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_bind_channelsWithGuarantees {f : Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) (n : ℕ) :
    @ExplicitCircuit.channelsWithGuarantees F _ β (f >>= g) (ExplicitCircuit.from_bind f_explicit g_explicit) n =
      ExplicitCircuit.channelsWithGuarantees f n ++
        ExplicitCircuit.channelsWithGuarantees (g (ExplicitCircuit.output f n)) (n + ExplicitCircuit.localLength f n) := rfl

-- `map` of an explicit circuit yields an explicit circuit
@[explicit_circuit_constructor]
instance ExplicitCircuit.from_map {f : α → β} {g : Circuit F α}
    (g_explicit : ExplicitCircuit g) : ExplicitCircuit (f <$> g) where
  output n := output g n |> f
  localLength n := localLength g n
  operations n := operations g n
  channelsWithGuarantees n := channelsWithGuarantees g n

  output_eq n := by rw [Circuit.map_output_eq, output_eq]
  localLength_eq n := by rw [Circuit.map_localLength_eq, localLength_eq]
  operations_eq n := by rw [Circuit.map_operations_eq, operations_eq]
  subcircuitsConsistent n := by
    rw [Circuit.map_operations_eq]
    exact g_explicit.subcircuitsConsistent n
  channelsLawful n := by
    rw [Circuit.map_operations_eq]
    exact g_explicit.channelsLawful n

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_map_output {f : α → β} {g : Circuit F α} (g_explicit : ExplicitCircuit g) (n : ℕ) :
    @ExplicitCircuit.output F _ β (f <$> g) (ExplicitCircuit.from_map g_explicit) n = f (ExplicitCircuit.output g n) := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_map_localLength {f : α → β} {g : Circuit F α} (g_explicit : ExplicitCircuit g) (n : ℕ) :
    @ExplicitCircuit.localLength F _ β (f <$> g) (ExplicitCircuit.from_map g_explicit) n = ExplicitCircuit.localLength g n := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_map_operations {f : α → β} {g : Circuit F α} (g_explicit : ExplicitCircuit g) (n : ℕ) :
    @ExplicitCircuit.operations F _ β (f <$> g) (ExplicitCircuit.from_map g_explicit) n = ExplicitCircuit.operations g n := rfl

@[circuit_norm, explicit_circuit_norm]
theorem ExplicitCircuit.from_map_channelsWithGuarantees {f : α → β} {g : Circuit F α} (g_explicit : ExplicitCircuit g) (n : ℕ) :
    @ExplicitCircuit.channelsWithGuarantees F _ β (f <$> g) (ExplicitCircuit.from_map g_explicit) n = ExplicitCircuit.channelsWithGuarantees g n := rfl

-- basic operations are explicit circuits

instance : ExplicitCircuits (F:=F) witnessVar where
  output _ n := ⟨ n ⟩
  localLength _ _ := 1
  operations c n := [.witness 1 c]
  channelsWithGuarantees _ _ := []

instance : ExplicitCircuits (F:=F) witnessField where
  output _ n := varFromOffset field n
  localLength _ _ := 1
  operations e n := [.witness 1 (.ofFExpr e)]
  channelsWithGuarantees _ _ := []

instance {k : ℕ} : ExplicitCircuits (F:=F) (witnessVector k) where
  output _ n := varFromOffset (fields k) n
  localLength _ _ := k
  operations out n := [.witness k (.ir [] out)]
  channelsWithGuarantees _ _ := []

instance {M : TypeMap} [ProvableType M] {ir : WitgenIR F (size M)} : ExplicitCircuit (witnessIR M ir) where
  localLength _ := size M
  output n := varFromOffset M n
  operations n := [.witness (size M) ir]
  channelsWithGuarantees _ := []

instance {m : ℕ} {c : Witgen.M F (Witgen.VExpr F m)} :
    ExplicitCircuit (witnessVectorProgram (F:=F) m c) :=
  inferInstanceAs (ExplicitCircuit (witnessIR (fields m) c.toIR))

/-- Bridge for scalar `witness` call sites (the family instance is keyed at
`field (FExpr F)` / `size field`, while call sites elaborate at the literal). -/
instance {e : Witgen.FExpr F} :
    ExplicitCircuit (witness (value := field) (var := Expression) e) :=
  inferInstanceAs (ExplicitCircuit (witnessField e))

/-- Bridge for vector `witness` call sites at literal length `m`. -/
instance {m : ℕ} {v : Vector (Witgen.FExpr F) m} :
    ExplicitCircuit (witness (value := (Vector · m)) (var := Var (fields m)) v) :=
  inferInstanceAs (ExplicitCircuit (witnessVector m (.lit v)))

instance {M : TypeMap} [ProvableType M] (c : Var (UnconstrainedDepNative M) F) :
    ExplicitCircuit (witnessNative c (inst := inferInstanceAs (Witnessable F M (Var M)))) where
  localLength _ := size M
  output offset := varFromOffset M offset
  operations _ := [.witness (size M) (.native (toElements ∘ c))]
  channelsWithGuarantees _ := []

instance {F : Type} [Field F] (x : Var (UnconstrainedDep field) F) : ExplicitCircuit (witnessVar x) :=
  ExplicitCircuits.toSingle _ _ (explicit := inferInstanceAs (ExplicitCircuits witnessVar))

instance {value var : TypeMap} [ProvableType value] [inst : Witnessable F value var] :
    ExplicitCircuits (witness (F:=F) (value:=value) (var:=var)) where
  output _ n := inst.var_eq ▸ varFromOffset value n
  output_eq c n := by
    rw [inst.witness_def]
    show _ = inst.var_eq ▸ (witnessIR value (.ofFExprs (toElements c))).output n
    rw [Circuit.output, Circuit.output, eqRec_eq_cast, eqRec_eq_cast,
      cast_fst, cast_apply (by rw [inst.var_eq])]

  localLength _ _ := size value
  localLength_eq c n := by
    rw [inst.witness_def, Circuit.localLength, eqRec_eq_cast,
      cast_apply (by rw [inst.var_eq]), snd_cast (by rw [inst.var_eq])]
    rfl

  operations c n := [.witness (size value) (.ofFExprs (toElements c))]
  operations_eq c n := by
    rw [inst.witness_def, Circuit.operations, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    rfl

  channelsWithGuarantees _ _ := []

  subcircuitsConsistent c n := by
    simp only [circuit_norm]
    rw [inst.witness_def, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    reduce
    trivial
  channelsLawful c n := by
    simp only [circuit_norm]
    rw [inst.witness_def, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    simp [circuit_norm]

instance {value var : TypeMap} [ProvableType value] [inst : Witnessable F value var] :
    ExplicitCircuits (inst.witnessIR (F:=F) (var:=var) (value := value)) where
  output _ n := inst.var_eq ▸ varFromOffset value n
  output_eq c n := by
    rw [inst.witnessIR_def]
    show _ = inst.var_eq ▸ (witnessIR value c).output n
    rw [Circuit.output, Circuit.output, eqRec_eq_cast, eqRec_eq_cast,
      cast_fst, cast_apply (by rw [inst.var_eq])]

  localLength _ _ := size value
  localLength_eq c n := by
    rw [inst.witnessIR_def, Circuit.localLength, eqRec_eq_cast,
      cast_apply (by rw [inst.var_eq]), snd_cast (by rw [inst.var_eq])]
    rfl

  operations c n := [.witness (size value) c]
  operations_eq c n := by
    rw [inst.witnessIR_def, Circuit.operations, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    rfl

  channelsWithGuarantees _ _ := []

  subcircuitsConsistent c n := by
    simp only [circuit_norm]
    rw [inst.witnessIR_def, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    reduce
    trivial
  channelsLawful c n := by
    simp only [circuit_norm]
    rw [inst.witnessIR_def, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    simp [circuit_norm]

instance {value var : TypeMap} [ProvableType value] [inst : Witnessable F value var]
    {c : Witgen.M F (value (Witgen.FExpr F))} :
    ExplicitCircuit (witnessProgram (F:=F) (value:=value) (var:=var) c) :=
  inferInstanceAs (ExplicitCircuit (inst.witnessIR (F:=F) (var:=var) (value := value) c.toIRLiteral))

instance {value var : TypeMap} [ProvableType value] [inst : Witnessable F value var] :
    ExplicitCircuits (witnessNative (F:=F) (value:=value) (var:=var)) where
  output _ n := inst.var_eq ▸ varFromOffset value n
  output_eq c n := by
    simp only [witnessNative]
    rw [inst.witnessIR_def]
    show _ = inst.var_eq ▸ (witnessIR value (.native (fun env => c env |> toElements))).output n
    rw [Circuit.output, Circuit.output, eqRec_eq_cast, eqRec_eq_cast,
      cast_fst, cast_apply (by rw [inst.var_eq])]

  localLength _ _ := size value
  localLength_eq c n := by
    simp only [witnessNative]
    rw [inst.witnessIR_def, Circuit.localLength, eqRec_eq_cast,
      cast_apply (by rw [inst.var_eq]), snd_cast (by rw [inst.var_eq])]
    rfl

  operations c n := [.witness (size value) (.native (toElements ∘ c))]
  operations_eq c n := by
    simp only [witnessNative]
    rw [inst.witnessIR_def, Circuit.operations, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    rfl

  channelsWithGuarantees _ _ := []
  subcircuitsConsistent c n := by
    simp only [circuit_norm]
    rw [inst.witnessIR_def, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    reduce
    trivial
  channelsLawful c n := by
    simp only [circuit_norm]
    rw [inst.witnessIR_def, eqRec_eq_cast, cast_apply (by rw [inst.var_eq]),
      snd_cast (by rw [inst.var_eq])]
    simp [circuit_norm]

instance : ExplicitCircuits (F:=F) assertZero where
  output _ _ := ()
  localLength _ _ := 0
  operations e n := [.assert e]
  channelsWithGuarantees _ _ := []

instance {α : TypeMap} [ProvableType α] {table : Table F α} : ExplicitCircuits (F:=F) (lookup table) where
  output _ _ := ()
  localLength _ _ := 0
  operations entry n := [.lookup { table := table.toRaw, entry := toElements entry }]
  channelsWithGuarantees _ _ := []

instance {Message : TypeMap} [ProvableType Message] {channel : Channel F Message}
    {mult : Expression F} :
    ExplicitCircuits (F:=F) (channel.emit mult) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.emitted mult msg).toRaw]
  channelsWithGuarantees _ _ := []

instance {Message : TypeMap} [ProvableType Message] {channel : Channel F Message} :
    ExplicitCircuits (F:=F) (channel.pull) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.pulled msg).toRaw]
  channelsWithGuarantees _ _ := [channel.toRaw]

instance {Message : TypeMap} [ProvableType Message] {channel : Channel F Message}
    {enabled : Expression F} :
    ExplicitCircuits (F:=F) (channel.pullIf enabled) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (pulledIf (channel:=channel) enabled msg).toRaw]
  channelsWithGuarantees _ _ := [channel.toRaw]

instance {Message : TypeMap} [ProvableType Message] {channel : Channel F Message} :
    ExplicitCircuits (F:=F) (channel.push) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.pushed msg).toRaw]
  channelsWithGuarantees _ _ := []

instance {Message : TypeMap} [ProvableType Message] {channel : Channel F Message}
    {enabled : Expression F} :
    ExplicitCircuits (F:=F) (channel.pushIf enabled) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (pushedIf (channel:=channel) enabled msg).toRaw]
  channelsWithGuarantees _ _ := []

attribute [explicit_circuit_unfold_type] Circuit

attribute [explicit_circuit_no_unfold] Circuit.bind witnessVar witnessField witnessVector
  witness witnessNative witnessIR witnessProgram witnessVectorProgram
  assertZero lookup Channel.emit Channel.pull Channel.push Channel.pullIf Channel.pushIf
  Pure.pure Bind.bind Functor.map

attribute [explicit_circuit_norm, circuit_norm] ExplicitCircuit.localLength ExplicitCircuit.operations ExplicitCircuit.output
  ExplicitCircuit.channelsWithGuarantees
attribute [explicit_circuit_norm, circuit_norm] ExplicitCircuits.localLength ExplicitCircuits.operations ExplicitCircuits.output
  ExplicitCircuits.channelsWithGuarantees
attribute [explicit_circuit_norm, circuit_norm] ExplicitCircuits.toSingle ExplicitCircuits.fromSingle
attribute [explicit_circuit_norm] ElaboratedCircuit.localLength ElaboratedCircuit.output
  ElaboratedCircuit.channelsWithGuarantees

-- simplification of terms coming from `bind` aggregation e.g. 8 + 0 + 1 + ...
attribute [explicit_circuit_norm] size Nat.add_zero Nat.zero_add Nat.mul_zero Nat.zero_mul
  Nat.mul_one Nat.one_mul Nat.sub_zero dif_pos dif_neg if_pos if_neg
  Nat.reduceAdd Nat.reduceMul Nat.reduceSub Nat.reduceLT Nat.reduceGT
  -- lists reduction, for channels
  List.nil_append List.append_nil
  List.cons_append
  List.ofFn_nil_flatten List.ofFn_singleton_flatten
  -- if-else
  dite_eq_ite ite_self reduceIte reduceDIte

syntax "infer_explicit_circuit" : tactic
syntax "infer_explicit_head" : tactic
syntax "unfold_explicit_circuits_head" : tactic
syntax "infer_explicit_circuits" : tactic

/-- The head of `type`, looking through `∀`/`let`/`mdata`. -/
private def resultTypeHead? : Expr → Option Name
  | .forallE _ _ body _ => resultTypeHead? body
  | .letE _ _ _ body _ => resultTypeHead? body
  | .mdata _ body => resultTypeHead? body
  | type => match type.getAppFn with
    | .const n _ => some n
    | _ => none

/-- A declaration is an *unfoldable circuit wrapper* when it is a definition (not tagged
`[explicit_circuit_no_unfold]`) whose result-type head is tagged `[explicit_circuit_unfold_type]`
(e.g. `Circuit`).  Pass `noUnfold?`/`unfoldType?` to reuse already-read label sets — e.g. when calling
this per `Expr` node — instead of re-reading them on every call. -/
def isUnfoldableCircuitDecl (declName : Name)
    (noUnfold? : Option (Array Name) := none) (unfoldType? : Option (Array Name) := none) :
    MetaM Bool := do
  let noUnfold ← match noUnfold? with
    | some s => pure s | none => labelled `explicit_circuit_no_unfold
  if noUnfold.contains declName then return false
  let unfoldType ← match unfoldType? with
    | some s => pure s | none => labelled `explicit_circuit_unfold_type
  let ok (type : Expr) : Bool := (resultTypeHead? type).any unfoldType.contains
  match (← getEnv).find? declName with
  | some (.defnInfo info) => return ok info.type
  | some (.opaqueInfo info) => return ok info.type
  | _ => return false

/-- Collect constants in an expression that are unfoldable circuit wrappers according to
`isUnfoldableCircuitDecl`. Pass already-read label sets to avoid re-reading attributes per node. -/
partial def collectUnfoldableCircuitDecls
    (e : Expr) (decls : Array Name := #[])
    (noUnfold? : Option (Array Name) := none) (unfoldType? : Option (Array Name) := none) :
    MetaM (Array Name) := do
  let noUnfold ← match noUnfold? with
    | some s => pure s | none => labelled `explicit_circuit_no_unfold
  let unfoldType ← match unfoldType? with
    | some s => pure s | none => labelled `explicit_circuit_unfold_type
  let rec go (e : Expr) (decls : Array Name) : MetaM (Array Name) := do
    match e with
    | .const declName _ =>
        if decls.contains declName ||
            !(← isUnfoldableCircuitDecl declName (some noUnfold) (some unfoldType)) then
          return decls
        else
          return decls.push declName
    | .app f a => go a (← go f decls)
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t decls)
    | .letE _ t v b _ => go b (← go v (← go t decls))
    | .mdata _ b => go b decls
    | .proj _ _ b => go b decls
    | _ => return decls
  go e decls

/-- The `@[explicit_circuit_constructor]` lemma whose conclusion `ExplicitCircuit <c>` keys on
`head` (the head constant of `<c>`), if any. -/
def explicitConstructorFor? (head : Name) : MetaM (Option Name) := do
  for lemmaName in (← labelled `explicit_circuit_constructor).toList do
    let some info := (← getEnv).find? lemmaName | continue
    let isMatch ← forallTelescopeReducing info.type fun _ concl => do
      let cargs := concl.getAppArgs
      if concl.getAppFn.isConstOf ``ExplicitCircuit && !cargs.isEmpty then
        return cargs[cargs.size - 1]!.getAppFn.constName? == some head
      else return false
    if isMatch then return some lemmaName
  return none

/-- If the head of `circuit` (the goal's last argument, application `target`/`args`) is an unfoldable
circuit wrapper, unfold it one step, `whnfCore` (no delta, so a loop `def` stays folded; sees through
`let`s/`match`es), `change` to the (defeq) reduced form, and return it — else `none`, no change.
Shared by `inferExplicitHead` and `unfold_explicit_circuits_head`. -/
def unfoldCircuitWrapperHead (target : Expr) (args : Array Expr) (circuit : Expr) :
    TacticM (Option Expr) := do
  let some head := circuit.getAppFn.constName? | return none
  unless ← isUnfoldableCircuitDecl head do return none
  let some unfolded ← withTransparency .default <| unfoldDefinition? circuit | return none
  let exposed ← whnfCore unfolded
  let newTarget := mkAppN target.getAppFn (args.set! (args.size - 1) exposed)
  replaceMainGoal [← (← getMainGoal).change newTarget (checkDefEq := false)]
  return some exposed

/--
Dispatch on the circuit's head constant in an `ExplicitCircuit` goal and `apply` the matching
`@[explicit_circuit_constructor]` lemma — O(1) per step, versus speculatively trying each `from_*`
(a failing `apply from_bind` does a deep unification whose cost scales with the circuit).

If the head is an unfoldable circuit wrapper instead, unfold it one step, `change` to the exposed
(defeq) form, and dispatch its head.
Bounded and non-recursive: a wrapper hiding a wrapper falls through to the caller's `apply from_bind`.
Side goals (loop bodies, `from_bind` parts) are left for the enclosing `infer_explicit_circuit` loop.
-/
def inferExplicitHead : TacticM Unit := withMainContext do
  let target ← getMainTarget
  let args := target.getAppArgs
  if !target.getAppFn.isConstOf ``ExplicitCircuit || args.isEmpty then
    throwError "target is not an ExplicitCircuit"
  -- Beta-reduce first: after `ExplicitCircuits.fromSingle; intro a` (and loop bodies),
  -- the circuit is often a redex like `(fun state => Circuit.foldl …) a`, whose `getAppFn`
  -- is the lambda.  Without this we'd miss the real head (`Circuit.foldl`, `subcircuit`, …).
  let circuit := args[args.size - 1]!.headBeta
  let some head := circuit.getAppFn.constName?
    | throwError "circuit head is not a constant"
  -- If `head` is an unfoldable wrapper, unfold once (changing the goal to the exposed form) and
  -- dispatch the exposed head; otherwise dispatch `head` directly.
  let head := ((← unfoldCircuitWrapperHead target args circuit).bind (·.getAppFn.constName?)).getD head
  let some lemmaName ← explicitConstructorFor? head
    | throwError "no explicit_circuit_constructor registered for head {head}"
  evalTactic (← `(tactic| apply $(mkIdent lemmaName)))

elab "infer_explicit_head" : tactic => inferExplicitHead

macro_rules
  | `(tactic|infer_explicit_circuit) => `(tactic|(
    try intros
    repeat (
      try intros
      first
        -- O(1) head dispatch via the `explicit_circuit_constructor` registry.
        | infer_explicit_head
        -- Fallback for heads that are user defs unfolding to a core constructor:
        -- prefer structural decomposition before typeclass search, so it doesn't
        -- `whnf` a large body and expand fixed-size `Vector.ofFn` witnesses.
        | apply ExplicitCircuit.from_bind
        | apply ExplicitCircuit.from_map
        | apply ExplicitCircuit.from_pure
        | infer_instance
      try infer_instance
    )
    done))

elab "unfold_explicit_circuits_head" : tactic => withMainContext do
  let target ← getMainTarget
  let args := target.getAppArgs
  if !target.getAppFn.isConstOf ``ExplicitCircuits || args.isEmpty then
    throwError "target is not ExplicitCircuits"
  if (← unfoldCircuitWrapperHead target args args[args.size - 1]!).isNone then
    throwError "failed to unfold target family head"

macro_rules
  | `(tactic|infer_explicit_circuits) => `(tactic|(
    try unfold_explicit_circuits_head
    try simp only
    apply ExplicitCircuits.fromSingle
    intro a
    infer_explicit_circuit
    ))

attribute [explicit_circuit_norm]
  -- `simp only` introduces `id`
  id_eq
  -- not sure why but `Ep.mpr` is introduced somewhere too and this helps
  eq_mpr_eq_cast cast_eq

syntax "elaborate_circuit_naive" : tactic
syntax "elaborate_circuit_naive_with" term : tactic
syntax "elaborate_circuit_naive_with" term " using " term : tactic

macro_rules
  | `(tactic|elaborate_circuit_naive) => `(tactic|(
    refine ExplicitCircuits.toElaborated _ ?explicit ?elaborated
    · infer_explicit_circuits
    · exact ExplicitCircuits.IsElaborated.mk
  ))

macro_rules
  | `(tactic|elaborate_circuit_naive_with $data:term using $data_eq:term) => `(tactic|(
    exact ElaboratedCircuit.withData (by elaborate_circuit_naive) $data $data_eq))
  | `(tactic|elaborate_circuit_naive_with $data:term) => `(tactic|(
    exact ElaboratedCircuit.withData (by elaborate_circuit_naive) $data))

/--
Derive an `ElaboratedCircuit` through `ExplicitCircuits`, but store normalized metadata fields.

Like `elaborate_circuit_naive`, this first runs `infer_explicit_circuits`.  Instead of returning the
`ExplicitCircuits.toElaborated` wrapper, it reads the explicit metadata projections and normalizes
selected fields before constructing the final record:

* `localLength`
* `output`
* `channelsWithGuarantees`
* `channelsWithRequirements`

Normalization is deliberately targeted.  It first performs one `dsimp` pass using
`explicit_circuit_norm` plus unfoldable circuit-family definitions found in the current metadata
expression.  Then it runs a `simp` pass using the same extensible `explicit_circuit_norm` theorem and
simproc sets.  This gives users a single place to add safe metadata-normalization rules while
avoiding broad `Meta.reduce`/`whnf` on large circuits.

The generated `localLength_eq` and `output_eq` proofs reuse the normalization proofs produced while
constructing the stored fields.  Structural consistency and channel-lawfulness proofs are delegated
directly to the inferred `ExplicitCircuits` proof using raw projection applications, avoiding
unnecessary type-directed reduction of the original circuit.

Set `set_option debug.elaborateCircuit true` to print the inferred explicit proof term and the
normalization passes used for each metadata field.
-/
elab "elaborate_circuit" : tactic => withMainContext do
  -- We are going to build an `ElaboratedCircuit` record directly.  First inspect the
  -- current goal and pull the important arguments out of
  --   ElaboratedCircuit F Input Output main
  -- so later code can construct the record fields explicitly.
  let goal ← getMainGoal
  let target ← whnf (← goal.getType)
  unless target.getAppFn.isConstOf ``ElaboratedCircuit do
    throwError "target is not an ElaboratedCircuit: {target}"
  let args := target.getAppArgs
  if args.size < 7 then
    throwError "unexpected ElaboratedCircuit target: {target}"
  let F := args[0]!
  let Input := args[1]!
  let Output := args[2]!
  let main := args[6]!

  -- Step 1: infer the explicit circuit metadata for `main`, exactly like the
  -- ordinary `elaborate_circuit_naive` tactic does.  The difference is that we
  -- keep this proof term around and read its projections below instead of
  -- returning `ExplicitCircuits.toElaborated` unchanged.
  let explicitType ← mkAppM ``ExplicitCircuits #[main]
  let explicit ← Lean.Elab.Term.elabTerm (← `(by infer_explicit_circuits)) (some explicitType)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let explicit ← instantiateMVars explicit
  let explicitProof := explicit
  if (← getOptions).getBool `debug.elaborateCircuit false then
    logInfo m!"elaborate_circuit explicit proof term:
  {explicit}"

  -- Useful object-language types for the lambdas we need to create.
  let varInputType ← mkAppM ``Var #[Input, F]
  let varOutputType ← mkAppM ``Var #[Output, F]
  let fieldInst := args[3]!
  let natType := mkConst ``Nat

  -- Read the simp theorem database tagged with `[explicit_circuit_norm]`.  These
  -- are mostly projection lemmas for `ExplicitCircuit.from_*` constructors, for
  -- example rewriting `(from_bind ...).localLength` to the corresponding explicit
  -- expression.  We use this as a targeted replacement for expensive `Meta.reduce`.
  let explicitThms ← do
    let some ext ← getSimpExtension? `explicit_circuit_norm
      | throwError "unknown simp attribute explicit_circuit_norm"
    ext.getTheorems
  let congrThms ← getSimpCongrTheorems

  -- Read the unfold-eligibility label sets once and pass them to `isUnfoldableCircuitDecl` below:
  -- `collectUnfoldable` checks it per `Expr` node, so we avoid re-reading the attributes each time.
  let unfoldTypeHeads ← labelled `explicit_circuit_unfold_type
  let noUnfoldHeads ← labelled `explicit_circuit_no_unfold

  -- Build a `dsimp` context from `[explicit_circuit_norm]` plus the user
  -- declarations found in the inferred explicit proof and the target circuit.
  let mkDsimpCtx (decls : Array Name) : MetaM Simp.Context := do
    let mut thms := explicitThms
    for decl in decls do
      thms ← thms.addDeclToUnfold decl
    Simp.mkContext { zeta := true, beta := true, proj := true, iota := true }
      (simpTheorems := #[thms]) congrThms

  -- Normalize the inferred explicit metadata once with the common unfold set.  The
  -- field projections below read from this pre-normalized term, avoiding four
  -- repeated reductions of the same explicit proof.
  let commonDecls ← collectUnfoldableCircuitDecls explicit
    (← collectUnfoldableCircuitDecls main #[] (some noUnfoldHeads) (some unfoldTypeHeads))
    (some noUnfoldHeads) (some unfoldTypeHeads)
  let commonDsimpCtx ← mkDsimpCtx commonDecls
  let explicitMetadata := (← dsimp explicit commonDsimpCtx).1

  let simpCtx ← Simp.mkContext { zeta := true, beta := true, proj := true, iota := true }
    (simpTheorems := #[explicitThms]) congrThms
  let simpProcs ← do
    let some ext ← Simp.getSimprocExtension? `explicit_circuit_norm
      | throwError "unknown simproc attribute explicit_circuit_norm"
    pure #[(← ext.getSimprocs)]

  -- Finish normalizing each metadata projection with the same targeted rules.  The
  -- common unfold set is also used for the debug output, which is copyable Lean
  -- syntax, e.g.
  --   dsimp only [explicit_circuit_norm, Foo.main, Bar.circuit]
  -- so a failing or slow normalization step can be replayed in a source file.
  let normalizeExplicit (label : String) (e : Expr) : TacticM Expr := do
    let debug := (← getOptions).getBool `debug.elaborateCircuit false
    if debug then
      let declNames := String.intercalate ", " (commonDecls.toList.map fun decl => toString decl)
      let simpArgs := if declNames.isEmpty then "explicit_circuit_norm" else s!"explicit_circuit_norm, {declNames}"
      logInfo m!"elaborate_circuit {label}:
  dsimp only [{simpArgs}]"
    return (← dsimp e commonDsimpCtx).1

  let normalizeExplicitSimp (label : String) (e : Expr) : TacticM (Expr × Expr) := do
    let e' ← normalizeExplicit label e
    let r ← Lean.Meta.simp e' simpCtx simpProcs
    let proof ← match r.1.proof? with
      | some proof => pure proof
      | none => mkEqRefl e'
    return (r.1.expr, proof)

  -- Store a simplified elaborated `localLength`.  We start from
  --   explicit.localLength input 0
  -- because an `ElaboratedCircuit` local length should not depend on the offset.
  -- The normalizer also returns a proof from the explicit metadata expression to
  -- the stored expression; keep it so the field proof does not normalize again.
  let (localLengthFun, localLengthNormProof) ← withLocalDeclD `input varInputType fun input => do
    let zero := mkNatLit 0
    let ll ←
      mkAppOptM ``ExplicitCircuits.localLength #[none, none, none, none, main, explicitMetadata, input, zero]
    let (ll, proof) ← normalizeExplicitSimp "localLength" ll
    let localLengthFun ← mkLambdaFVars #[input] ll
    let localLengthNormProof ← mkLambdaFVars #[input] proof
    return (localLengthFun, localLengthNormProof)

  -- Store a simplified elaborated `output`.  Unlike `localLength`, output is a
  -- function of both the input variables and the current offset.  Again, keep the
  -- normalization proof for the corresponding `output_eq` field.
  let (outputFun, outputNormProof) ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let out ←
        mkAppOptM ``ExplicitCircuits.output #[none, none, none, none, main, explicitMetadata, input, offset]
      let (out, proof) ← normalizeExplicitSimp "output" out
      let outputFun ← mkLambdaFVars #[input, offset] out
      let outputNormProof ← mkLambdaFVars #[input, offset] proof
      return (outputFun, outputNormProof)

  -- Prove the elaborated local-length equation by composing:
  --   circuit.localLength offset = explicit.localLength input offset
  -- with the proof that the explicit metadata expression at offset 0 normalizes to
  -- the stored field.  The latter proof was produced while constructing the field.
  let localLengthEq ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let p1 ← mkAppOptM ``ExplicitCircuits.localLength_eq #[none, none, none, none, main, explicitProof, input, offset]
      let p1Type ← inferType p1
      let some (_, _, mid) := p1Type.eq?
        | throwError "unexpected localLength_eq type: {p1Type}"
      let p2 := mkApp localLengthNormProof input
      let rhs := mkApp localLengthFun input
      let p2Type ← mkEq mid rhs
      let p2 ← mkExpectedTypeHint p2 p2Type
      let p ← mkAppM ``Eq.trans #[p1, p2]
      mkLambdaFVars #[input, offset] p

  -- Same proof pattern for output:
  --   circuit.output offset = explicit.output input offset = storedOutput input offset.
  let outputEq ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let p1 ← mkAppOptM ``ExplicitCircuits.output_eq #[none, none, none, none, main, explicitProof, input, offset]
      let p1Type ← inferType p1
      let some (_, _, mid) := p1Type.eq?
        | throwError "unexpected output_eq type: {p1Type}"
      let p2 := mkApp2 outputNormProof input offset
      let rhs := mkApp2 outputFun input offset
      let p2Type ← mkEq mid rhs
      let p2 ← mkExpectedTypeHint p2 p2Type
      let p ← mkAppM ``Eq.trans #[p1, p2]
      mkLambdaFVars #[input, offset] p

  -- Consistency proofs are not recomputed.  They are taken directly from the
  -- inferred explicit metadata, whose operations still match the real circuit.
  let subProof ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let p := mkAppN (mkConst ``ExplicitCircuits.subcircuitsConsistent)
        #[F, fieldInst, varInputType, varOutputType, main, explicitProof, input, offset]
      mkLambdaFVars #[input, offset] p

  -- Store simplified top-level channel metadata too.  The explicit metadata APIs
  -- expose channel lists as functions of input/offset, but these lists are intended
  -- to be circuit-level metadata.  Normalize them once as functions of input/offset,
  -- then store their value at a default input and offset 0.  The normalization proofs
  -- are reused below when transporting the delegated channel-lawfulness proof.
  let defaultInput ← mkAppOptM ``default #[varInputType, none]
  let zero := mkNatLit 0
  let (channelsWithGuaranteesFun, channelsWithGuaranteesNormProof) ←
      withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let ch ← mkAppOptM ``ExplicitCircuits.channelsWithGuarantees
        #[none, none, none, none, main, explicitMetadata, input, offset]
      let (ch, proof) ← normalizeExplicitSimp "channelsWithGuarantees" ch
      let channelsWithGuaranteesFun ← mkLambdaFVars #[input, offset] ch
      let channelsWithGuaranteesNormProof ← mkLambdaFVars #[input, offset] proof
      return (channelsWithGuaranteesFun, channelsWithGuaranteesNormProof)
  let channelsWithGuarantees := mkApp2 channelsWithGuaranteesFun defaultInput zero
  -- Channel lawfulness is delegated to the inferred explicit circuit proof.  If the
  -- stored channel metadata was simplified propositionally, transport the delegated
  -- proof across the corresponding channel-list equality.
  let channelsLawful ← withLocalDeclD `input varInputType fun input => do
    withLocalDeclD `offset natType fun offset => do
      let p := mkAppN (mkConst ``ExplicitCircuits.channelsLawful)
        #[F, fieldInst, varInputType, varOutputType, main, explicitProof, input, offset]
      let pType ← inferType p
      let pArgs := pType.getAppArgs
      if !pType.getAppFn.isConstOf ``Operations.ChannelsLawful || pArgs.size < 4 then
        throwError "unexpected channelsLawful type: {pType}"
      let ops := pArgs[2]!
      let actualGuarantees := pArgs[3]!
      let rawChannelType := mkApp (mkConst ``RawChannel) F
      let rawChannelListType := mkApp (mkConst ``List [levelZero]) rawChannelType
      let guaranteesProof := mkApp2 channelsWithGuaranteesNormProof input offset
      let currentGuarantees := mkApp2 channelsWithGuaranteesFun input offset
      let guaranteesProofType ← mkEq actualGuarantees currentGuarantees
      let guaranteesProof ← mkExpectedTypeHint guaranteesProof guaranteesProofType
      let guaranteesStoredType ← mkEq currentGuarantees channelsWithGuarantees
      let guaranteesStoredProof ← mkExpectedTypeHint (← mkEqRefl channelsWithGuarantees) guaranteesStoredType
      let guaranteesProof ← mkAppOptM ``Eq.trans
        #[none, actualGuarantees, currentGuarantees, channelsWithGuarantees, guaranteesProof, guaranteesStoredProof]
      let p ← withLocalDeclD `channelsWithGuarantees rawChannelListType fun normalizedGuarantees => do
        let prop := mkAppN (mkConst ``Operations.ChannelsLawful)
          #[F, fieldInst, ops, normalizedGuarantees]
        let motive ← mkLambdaFVars #[normalizedGuarantees] prop
        let propEq ← mkAppM ``congrArg #[motive, guaranteesProof]
        mkEqMP propEq p
      mkLambdaFVars #[input, offset] p

  -- Assemble the final `ElaboratedCircuit` record using the normalized fields and
  -- the delegated proofs, then close the user's goal.
  let val ← mkAppOptM ``ElaboratedCircuit.mk #[F, Input, Output, none, none, none, main,
    localLengthFun, localLengthEq, outputFun, outputEq, subProof, channelsWithGuarantees,
    channelsLawful]
  goal.assign val
  replaceMainGoal []

syntax "elaborate_circuit_with" term : tactic
syntax "elaborate_circuit_with" term " using " term : tactic

private def elaborateCircuitWith (dataStx : TSyntax `term) (dataEqStx? : Option (TSyntax `term)) :
    TacticM Unit := withMainContext do
  -- The tactic is used in goals of the form
  --   ElaboratedCircuit F Input Output main
  -- We unpack the target manually because the rest of the code constructs
  -- `ElaboratedCircuit.Data` and `.withData` terms with explicit arguments.  This
  -- avoids leaving Lean to infer expensive arguments in large generated circuits.
  let goal ← getMainGoal
  let target ← whnf (← goal.getType)
  unless target.getAppFn.isConstOf ``ElaboratedCircuit do
    throwError "target is not an ElaboratedCircuit: {target}"
  let args := target.getAppArgs
  if args.size < 7 then
    throwError "unexpected ElaboratedCircuit target: {target}"
  let F := args[0]!
  let Input := args[1]!
  let Output := args[2]!
  let fieldInst := args[3]!
  let inputCircuitTypeInst := args[4]!
  let outputCircuitTypeInst := args[5]!
  let main := args[6]!

  -- Build the base elaborated circuit as a real expression.  The `_with` tactic
  -- then wraps this expression in `.withData` and normalizes that wrapper.
  let derived ← Lean.Elab.Term.elabTerm (← `(by elaborate_circuit)) (some target)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let derived ← instantiateMVars derived

  let varInputType ← mkAppM ``Var #[Input, F]
  let natType := mkConst ``Nat

  -- Reconstruct the type of the user-supplied `using` proof:
  --   old derived fields = user data fields, plus channel subset obligations.
  -- Elaborating the proof against this type preserves the old surface behavior of
  -- `ElaboratedCircuit.withData (by elaborate_circuit) data data_eq`.
  let mkDataEqType (derived data : Expr) : MetaM Expr := do
    let localLengthEq ← withLocalDeclD `a varInputType fun a => do
      let lhs ← mkAppOptM ``ElaboratedCircuit.localLength
        #[F, Input, Output, fieldInst, inputCircuitTypeInst, outputCircuitTypeInst, main, derived, a]
      let rhs ← mkAppOptM ``ElaboratedCircuit.Data.localLength
        #[F, fieldInst, Input, Output, inputCircuitTypeInst, outputCircuitTypeInst, main, derived, data, a]
      mkForallFVars #[a] (← mkEq lhs rhs)
    let outputEq ← withLocalDeclD `a varInputType fun a => do
      withLocalDeclD `n natType fun n => do
        let lhs ← mkAppOptM ``ElaboratedCircuit.output
          #[F, Input, Output, fieldInst, inputCircuitTypeInst, outputCircuitTypeInst, main, derived, a, n]
        let rhs ← mkAppOptM ``ElaboratedCircuit.Data.output
          #[F, fieldInst, Input, Output, inputCircuitTypeInst, outputCircuitTypeInst, main, derived, data, a, n]
        mkForallFVars #[a, n] (← mkEq lhs rhs)
    let guaranteesSubset ← do
      let lhs ← mkAppOptM ``ElaboratedCircuit.channelsWithGuarantees
        #[F, Input, Output, fieldInst, inputCircuitTypeInst, outputCircuitTypeInst, main, derived]
      let rhs ← mkAppOptM ``ElaboratedCircuit.Data.channelsWithGuarantees
        #[F, fieldInst, Input, Output, inputCircuitTypeInst, outputCircuitTypeInst, main, derived, data]
      mkAppM ``HasSubset.Subset #[lhs, rhs]
    pure (mkAnd localLengthEq (mkAnd outputEq guaranteesSubset))

  let defaultDataEqStx : TacticM (TSyntax `term) :=
    `(by
      and_intros
      · intro a; ac_rfl
      · intro a n; rfl
      · try simp only [circuit_norm]; try grind; done)

  let elabDataEq (derived data : Expr) : TacticM (Expr × Expr) := do
    let dataEqType ← mkDataEqType derived data
    let dataEqStx ← match dataEqStx? with
      | some dataEqStx => pure dataEqStx
      | none => defaultDataEqStx
    let dataEq ← Lean.Elab.Term.elabTerm dataEqStx (some dataEqType)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    return (dataEqType, ← instantiateMVars dataEq)

  -- First elaborate the user's `data` and optional `using` proof against the
  -- inline base result. This yields the same ergonomic behavior as `.withData`:
  -- `using by ...` scripts only have to bridge the `elaborate_circuit` result to
  -- their `data` overrides.
  let inlineDataType ← mkAppOptM ``ElaboratedCircuit.Data
    #[F, fieldInst, Input, Output, inputCircuitTypeInst, outputCircuitTypeInst, main, derived]
  let inlineDataVal ← Lean.Elab.Term.elabTerm dataStx (some inlineDataType)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let inlineDataVal ← instantiateMVars inlineDataVal
  let (_inlineDataEqType, inlineDataEqVal) ← elabDataEq derived inlineDataVal

  -- The `_with` normalizer is intentionally much smaller than the base tactic's
  -- normalizer.  Its inputs are already projections from `ElaboratedCircuit.Data`
  -- or from `(derived.withData data data_eq)`, so reducing with only
  -- `[explicit_circuit_norm]` is enough to expose the final field expressions.
  let explicitThms ← do
    let some ext ← getSimpExtension? `explicit_circuit_norm
      | throwError "unknown simp attribute explicit_circuit_norm"
    ext.getTheorems
  let congrThms ← getSimpCongrTheorems
  let dsimpCtx ← Simp.mkContext { zeta := true, beta := true, proj := true, iota := true }
    (simpTheorems := #[explicitThms]) congrThms

  -- This is the core of the tactic: build the ordinary `.withData` expression and
  -- let `dsimp only [explicit_circuit_norm]` reduce its projections to the final
  -- record shape.  There is no separate field-by-field proof reconstruction here.
  let withData ← mkAppOptM ``ElaboratedCircuit.withData
    #[F, fieldInst, Input, Output, inputCircuitTypeInst, outputCircuitTypeInst, main,
      derived, inlineDataVal, inlineDataEqVal]
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let withData ← instantiateMVars withData
  let val := (← dsimp withData dsimpCtx).1
  goal.assign val
  replaceMainGoal []

elab_rules : tactic
  | `(tactic|elaborate_circuit_with $data:term using $data_eq:term) => do
      elaborateCircuitWith data (some data_eq)
  | `(tactic|elaborate_circuit_with $data:term) => do
      elaborateCircuitWith data none

-- this tactic is pretty good at inferring explicit circuits!
section

-- single
example : ExplicitCircuit (witness 0 : Circuit F (Expression F)) := by infer_explicit_circuit

example :
  let add := do
    let x : Expression F ← witness 0
    let y ← witness 1
    let z ← witness (x + y)
    assertZero (x + y - z)
    return z

  ExplicitCircuit add := by infer_explicit_circuit

-- family
example : ExplicitCircuits (witnessField (F:=F)) := by infer_explicit_circuits

example :
  let add (x : Expression F) := do
    let y : Expression F ← witness 1
    let z ← witness (x + y)
    assertZero (x + y - z)
    return z

  ExplicitCircuits add := by infer_explicit_circuits

-- elaborated
example :
  let add (x : Expression F) := do
    let y : Expression F ← witness 1
    let z ← witness (x + y)
    assertZero (x + y - z)
    return z

  ElaboratedCircuit F field field add := by elaborate_circuit_naive

-- bridge for `Var unit F` output type
instance {circuit : α → Circuit F (Var unit F)} [inst : ExplicitCircuits (β := Unit) circuit] :
  ExplicitCircuits circuit := inst

example : ElaboratedCircuit F field unit (fun x ↦ assertZero (x * (x - 1))) := by
  elaborate_circuit_naive

-- works with circuits hidden behind definitions
private def assertBool (x : Expression F) := do
  assertZero (x * (x - 1))

example : ElaboratedCircuit F field unit assertBool := by elaborate_circuit_naive

end
