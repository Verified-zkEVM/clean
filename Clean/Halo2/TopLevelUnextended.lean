import Clean.Halo2.TopLevel
import Clean.Halo2.Configure.Extensions

/-! The zcash compiler's domain: closed circuits recording no midnight-zk entry. Soundness does
not need it, since shadows carry every stated meaning; a claim that a zcash key is the key of
the whole circuit does. -/

namespace Halo2

variable {F : Type} [FiniteField F] {Config : Type}
  {PublicInput : TypeMap} [ProvableType PublicInput]

/-- The closed circuit records no midnight-zk extension entry. -/
class TopLevelCircuit.Unextended (top : TopLevelCircuit F Config PublicInput) : Prop where
  extensions_eq_nil : top.constraintSystem.extensions = []

/-- A circuit whose configure program is `Configure.Unextended` is unextended. -/
theorem TopLevelCircuit.Unextended.of_configure (top : TopLevelCircuit F Config PublicInput)
    [h : Configure.Unextended (top.formalCircuit.configure ())] : top.Unextended := by
  constructor
  change ([] : List (ConfigureExtension F)) ++ ConfigureExtension.rebase 0 0
    ((top.formalCircuit.configure ()).delta (ConfigureCounts.ofConstraintSystem {})).extensions =
      []
  rw [h.extensions_eq_nil]
  rfl

end Halo2
