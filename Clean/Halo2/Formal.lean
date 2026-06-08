import Clean.Halo2.Basic

namespace Halo2

abbrev LocalEnvironment (F : Type) := EnvironmentWithLocation F Query

def Constraint.Holds {F : Type} [Field F]
    (env : LocalEnvironment F) (constraint : Constraint F) : Prop :=
  env constraint.expression = 0

namespace GateBuilder

def constraints {F : Type} (build : VirtualCells F Unit) : Array (Constraint F) :=
  (build.run {}).2.constraints

end GateBuilder

namespace Gate

def empty {F : Type} : Gate F where
  name := "missing"
  constraints := #[]
  queriedSelectors := #[]
  queriedCells := #[]

def Constraints {F : Type} [Field F] (env : LocalEnvironment F) (gate : Gate F) : Prop :=
  ∀ constraint ∈ gate.constraints, constraint.Holds env

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

def Soundness {F Config : Type} [Field F]
    (configure : Configure F Config)
    (gateIndex : ℕ)
    (Assumptions Spec : Config → LocalEnvironment F → Prop) : Prop :=
  ∀ env,
    Assumptions configure.output env →
    (configure.gate gateIndex).Constraints env →
    Spec configure.output env

def Completeness {F Config : Type} [Field F]
    (configure : Configure F Config)
    (gateIndex : ℕ)
    (Assumptions Spec : Config → LocalEnvironment F → Prop) : Prop :=
  ∀ env,
    Assumptions configure.output env →
    Spec configure.output env →
    (configure.gate gateIndex).Constraints env

end FormalGate

structure FormalGate (F : Type) [Field F] (Config : Type) where
  name : String := "anonymous"
  configure : Configure F Config
  gateIndex : ℕ := 0
  Assumptions : Config → LocalEnvironment F → Prop := fun _ _ => True
  Spec : Config → LocalEnvironment F → Prop
  soundness : FormalGate.Soundness configure gateIndex Assumptions Spec
  completeness : FormalGate.Completeness configure gateIndex Assumptions Spec

end Halo2
