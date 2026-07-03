import Clean.Circuit.Theorems

/-!
# Array-backed witness generation (witgen IR plan, phase 3)

`FlatOperation.dynamicWitnesses` is the semantic reference for witness generation, but
it is accidentally quadratic: the accumulator is a `List` (O(n) append per operation),
and the prover environment it builds is list-backed, so every `env.get` inside a
witness callback walks the list from the head (O(i) per read).

`FlatOperation.witgen` below is the runtime counterpart: a single linear fold over the
operations with an `Array` accumulator (amortized O(1) append, in-place when the array
is used linearly) and an array-backed environment (O(1) reads).

The theorem `witgen_eq_dynamicWitnesses` proves once, by induction, that it computes
exactly the same witnesses. Downstream corollaries transfer the existing
`UsesLocalWitnesses` result, so `Circuit.witgen` is a drop-in fast path for honest
witness generation — and the reference interpreter that the future Rust witgen
pipeline is differentially tested against.

Note: like `ProverEnvironment.fromList`, the environment used here has empty committed
`data`; circuits whose witnesses read `env.data` (e.g. FemtoCairo memory) need the
environment extended with that data, which applies to both interpreters equally and is
left to a later phase.
-/

variable {F : Type} [FiniteField F] {α : Type}

/-- Build a `ProverEnvironment` from a witness array (O(1) reads) and a prover hint.
Array-backed counterpart of `ProverEnvironment.fromList`. -/
def ProverEnvironment.fromArray (witnesses : Array F) (hint : ProverHint F) :
    ProverEnvironment F where
  get i := witnesses[i]?.getD 0
  data _ _ := #[]
  hint

theorem ProverEnvironment.fromArray_eq_fromList (witnesses : Array F) (hint : ProverHint F) :
    ProverEnvironment.fromArray witnesses hint = .fromList witnesses.toList hint := by
  simp only [ProverEnvironment.fromArray, ProverEnvironment.fromList, Array.getElem?_toList]

namespace FlatOperation

/-- One step of array-backed witness generation: a witness operation appends its
values, computed against the environment of all witnesses so far; other operations
leave the array unchanged. -/
def witgenStep (hint : ProverHint F) (acc : Array F) : FlatOperation F → Array F
  | .witness _ code => acc ++ (code.eval (.fromArray acc hint)).toArray
  | .assert _ | .lookup _ | .interact _ => acc

/--
Array-backed witness generation: a single linear fold over the operations.
Computes the same witnesses as `dynamicWitnesses` (theorem
`witgen_eq_dynamicWitnesses`), without the quadratic list overhead.
-/
def witgen (hint : ProverHint F) (ops : List (FlatOperation F)) (init : Array F) : Array F :=
  ops.foldl (witgenStep hint) init

lemma witgenStep_toList (hint : ProverHint F) (acc : Array F) (op : FlatOperation F) :
    (witgenStep hint acc op).toList = acc.toList ++ op.dynamicWitness hint acc.toList := by
  cases op <;>
    simp [witgenStep, dynamicWitness, ProverEnvironment.fromArray_eq_fromList, Vector.toList]

/-- The array-backed interpreter agrees with the list-backed reference semantics. -/
theorem witgen_eq_dynamicWitnesses (hint : ProverHint F) (ops : List (FlatOperation F))
    (init : Array F) :
    witgen hint ops init = (dynamicWitnesses ops hint init.toList).toArray := by
  induction ops generalizing init with
  | nil => simp [witgen, dynamicWitnesses]
  | cons op ops ih =>
    rw [witgen, List.foldl_cons, ← witgen, dynamicWitnesses_cons, ih, witgenStep_toList]

end FlatOperation

namespace Circuit

/--
Fast witness generation for a circuit: array-backed, single linear pass.

`init` provides the witnesses below the circuit's starting offset (typically the
inputs); the result extends it with all witnesses created by the circuit.
-/
def witgen (circuit : Circuit F α) (hint : ProverHint F) (init : Array F := #[]) : Array F :=
  FlatOperation.witgen hint (circuit.operations init.size).toFlat init

/-- `Circuit.witgen` builds exactly the environment of `Circuit.proverEnvironment`. -/
theorem witgen_proverEnvironment (circuit : Circuit F α) (hint : ProverHint F)
    (init : Array F) :
    ProverEnvironment.fromArray (circuit.witgen hint init) hint
      = circuit.proverEnvironment hint init.toList := by
  rw [proverEnvironment, witgen, ProverEnvironment.fromArray_eq_fromList,
    FlatOperation.witgen_eq_dynamicWitnesses]
  simp

/--
If a circuit has computable witnesses, the environment built from `Circuit.witgen`
uses the circuit's local witnesses — i.e., array-backed witness generation is honest.
-/
theorem witgen_usesLocalWitnesses (circuit : Circuit F α) (hint : ProverHint F)
    (init : Array F) (h_computable : circuit.ComputableWitnesses init.size) :
    (ProverEnvironment.fromArray (circuit.witgen hint init) hint).UsesLocalWitnesses
      init.size (circuit.operations init.size) := by
  rw [witgen_proverEnvironment]
  have h := circuit.proverEnvironment_usesLocalWitnesses hint init.toList
  simp only [Array.length_toList] at h
  exact h h_computable

end Circuit
