import Clean.Halo2.Basic
import Clean.Circuit

namespace Halo2

abbrev LocalEnvironment (F : Type) := EnvironmentWithLocation F Query

def Constraint.Holds {F : Type} [Field F]
    (env : LocalEnvironment F) (constraint : Constraint F) : Prop :=
  env constraint.expression = 0

namespace GateBuilder

def constraints {F : Type} (build : VirtualCells F Unit) : Array (Constraint F) :=
  (build.run {}).2.constraints

end GateBuilder

def registerInputs {F : Type} {Inputs : TypeMap} [ProvableType Inputs]
    (inputs : Inputs (Expression F)) : VirtualCells F (Inputs (Expression F)) := fun state =>
  (inputs, { state with registeredInputs := some (toElements inputs).toArray })

namespace Gate

def evalInputs {F : Type} [Field F] {Inputs : TypeMap} [ProvableType Inputs]
    (env : LocalEnvironment F) (inputs : Inputs (Expression F)) : Inputs F :=
  fromElements <| (toElements inputs).map env

def empty {F : Type} : Gate F where
  name := "missing"
  constraints := #[]
  queriedSelectors := #[]
  queriedCells := #[]
  registeredInputs := none

def Constraints {F : Type} [Field F] (env : LocalEnvironment F) (gate : Gate F) : Prop :=
  ∀ constraint ∈ gate.constraints, constraint.Holds env

def registeredInputExpressions {F : Type} [Field F] {Inputs : TypeMap} [ProvableType Inputs]
    (gate : Gate F) : Inputs (Expression F) :=
  fromElements <| Vector.ofFn fun i =>
    (gate.registeredInputs.bind fun inputs => inputs[i]?).getD (.const 0)

end Gate

@[circuit_norm]
theorem Gate.registeredInputExpressions_of_toElements {F : Type} [Field F]
    {Inputs : TypeMap} [ProvableType Inputs] (gate : Gate F)
    (inputs : Inputs (Expression F)) :
    Gate.registeredInputExpressions (Inputs := Inputs)
      { gate with registeredInputs := some (toElements inputs).toArray } = inputs := by
  change fromElements (Vector.ofFn fun i =>
    ((some (toElements inputs).toArray).bind fun inputs => inputs[i]?).getD (.const 0)) = inputs
  rw [ProvableType.fromElements_eq_iff]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, Option.bind_some]
  have hIndex : i < (toElements inputs).toArray.size := by
    simpa [Vector.size_toArray] using hi
  change (toElements inputs).toArray[i]?.getD (.const 0) = (toElements inputs)[i]
  rw [Array.getElem?_eq_getElem hIndex, Option.getD_some]
  exact Vector.getElem_toArray hIndex

namespace Gate

def RegisteredInputs {F : Type} [Field F] {Inputs : TypeMap} [ProvableType Inputs]
    (env : LocalEnvironment F) (gate : Gate F) : Inputs F :=
  evalInputs env (gate.registeredInputExpressions (Inputs := Inputs))

end Gate

namespace Configure

def output {F Config : Type} (configure : Configure F Config) : Config :=
  (configure.run {}).1

def state {F Config : Type} (configure : Configure F Config) : ConfigureState F :=
  (configure.run {}).2

def gate {F Config : Type} (configure : Configure F Config) (index : ℕ) : Gate F :=
  (configure.state.gates[index]?).getD Gate.empty

end Configure

namespace FormalGate

def Soundness {F Config : Type} {Inputs : TypeMap} [Field F] [ProvableType Inputs]
    (configure : Configure F Config)
    (gateIndex : ℕ)
    (Assumptions Spec : Config → Inputs F → Prop) : Prop :=
  ∀ env,
    Assumptions configure.output ((configure.gate gateIndex).RegisteredInputs (Inputs := Inputs) env) →
    (configure.gate gateIndex).Constraints env →
    Spec configure.output ((configure.gate gateIndex).RegisteredInputs (Inputs := Inputs) env)

def Completeness {F Config : Type} {Inputs : TypeMap} [Field F] [ProvableType Inputs]
    (configure : Configure F Config)
    (gateIndex : ℕ)
    (Assumptions Spec : Config → Inputs F → Prop) : Prop :=
  ∀ env,
    Assumptions configure.output ((configure.gate gateIndex).RegisteredInputs (Inputs := Inputs) env) →
    Spec configure.output ((configure.gate gateIndex).RegisteredInputs (Inputs := Inputs) env) →
    (configure.gate gateIndex).Constraints env

end FormalGate

structure FormalGate (F : Type) [Field F] (Config : Type) (Inputs : TypeMap) [ProvableType Inputs] where
  name : String := "anonymous"
  configure : Configure F Config
  gateIndex : ℕ := 0
  Assumptions : Config → Inputs F → Prop := fun _ _ => True
  Spec : Config → Inputs F → Prop
  soundness : FormalGate.Soundness configure gateIndex Assumptions Spec
  completeness : FormalGate.Completeness configure gateIndex Assumptions Spec

end Halo2
