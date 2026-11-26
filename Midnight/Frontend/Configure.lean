import Midnight.Backend.Compile

/-! The Midnight frontend: Clean's own `Halo2.Configure` with the names midnight-zk's chips use,
so ports read like the Rust. Closures run in `Cells`, Clean's `VirtualCells`; the backend is
`Backend.compile`. -/
namespace Midnight.Frontend
open Halo2 (Column AnyColumn Selector ComplexSelector TableColumn Gate Rotation)
open Keygen (E)

abbrev Configure := Halo2.Configure F
abbrev Cells := Halo2.VirtualCells

/-- Lets chip ports index column arrays with `[i]!`, as the Rust does. -/
instance {kind : Halo2.ColumnKind} : Inhabited (Column kind) := ⟨⟨0⟩⟩

abbrev adviceColumn : Configure (Column .advice) := Halo2.adviceColumn

/-- Refused: Rust blinds unblinded advice differently from advice (`prover.rs:550-558`) but the
key is the same, so key equality could not catch it. Allocates as advice and records a `rejected`
entry, which the backend reports as an error. -/
def unblindedAdviceColumn : Configure (Column .advice) :=
  ⟨fun counts =>
    (⟨counts.numAdviceColumns⟩, { extensions := [.rejected "unblinded advice: unsupported"] },
      { numAdviceColumns := 1 })⟩

abbrev fixedColumn : Configure (Column .fixed) := Halo2.fixedColumn

abbrev instanceColumn : Configure (Column .instance) := Halo2.instanceColumn

abbrev lookupTableColumn : Configure TableColumn := Halo2.lookupTableColumn

abbrev selector : Configure Selector := Halo2.selector

abbrev complexSelector : Configure ComplexSelector := Halo2.complexSelector

abbrev enableEquality (c : AnyColumn) : Configure Unit := Halo2.enableEquality c

abbrev enableConstant (c : Column .fixed) : Configure Unit := Halo2.enableConstant c

abbrev setMinimumDegree (degree : Nat) : Configure Unit := Halo2.setMinimumDegree degree

def advice (c : Column .advice) (rotation : Rotation := 0) : Cells E :=
  Halo2.VirtualCells.queryAdvice c rotation

def fixed (c : Column .fixed) (rotation : Rotation := 0) : Cells E :=
  Halo2.VirtualCells.queryFixed c rotation

def inst (c : Column .instance) (rotation : Rotation := 0) : Cells E :=
  Halo2.VirtualCells.queryInstance c rotation

abbrev gate (name : String) (q : Selector) (body : Cells (Array (String × E))) : Configure Unit :=
  Halo2.Closure.gate name q (Array.toList <$> body)

abbrev additiveGate (name : String) (q : ComplexSelector) (body : Cells (Array (String × E))) :
    Configure Unit :=
  Halo2.Closure.additiveGate name q (Array.toList <$> body)

abbrev gateWithoutSelector (name : String) (body : Cells (Array (String × E))) : Configure Unit :=
  Halo2.Closure.gateWithoutSelector name (Array.toList <$> body)

abbrev batchedLookup (name : String) (q : Option ComplexSelector)
    (body : Cells (Array (Array E × TableColumn))) : Configure Unit :=
  Halo2.Closure.batchedLookup name q
    ((fun columns => columns.toList.map fun (xs, t) => (xs.toList, t)) <$> body)

/-- Rust `meta.query_selector(q)`, recorded in the closure's call order. -/
def querySelector (q : Selector) : Cells E := Halo2.VirtualCells.querySelector q

abbrev batchedLookupAny (name : String) (q : Option ComplexSelector)
    (body : Cells (Array (Array E × E))) : Configure Unit :=
  Halo2.Closure.batchedLookupAny name q
    ((fun columns => columns.toList.map fun (xs, t) => (xs.toList, t)) <$> body)

abbrev lookupAny (name : String) (q : Option ComplexSelector) (body : Cells (Array (E × E))) :
    Configure Unit :=
  Halo2.Closure.lookupAny name q (Array.toList <$> body)

/-- Clean's own gate, for gates written as `Gate` values. -/
abbrev createGate (g : Gate F) : Configure Unit := Halo2.createGate g

def compile : Configure Unit → Keygen.CS := Backend.compile

/-! ## Elaborated metadata for the loops ports use

Clean's `ElaboratedConfigure` instances cover the constructs and `for` over a list; these
reduce the other loops to it. `Configure` is not shown to be a `LawfulMonad`, so `Array.mapM`
goes by its own recursion rather than through `List.mapM`. -/

open Halo2 (ElaboratedConfigure)
open scoped Halo2.ElaboratedConfigure

/-- `ElaboratedConfigure` of a whole port, one `bind` at a time: instance search over the whole
program exceeds `synthInstance.maxSize`. Binds are matched reducibly, so a closure is never
evaluated to look for one. -/
macro "elaborate_configure" : tactic => `(tactic|
  repeat' first
    | with_reducible refine @Halo2.ElaboratedConfigure.bind _ _ _ _ ?_ _ ?_
    | intro _
    | infer_instance)

instance instForInArray {α β : Type} (xs : Array α) (init : β)
    (f : α → β → Configure (ForInStep β)) [∀ a b, ElaboratedConfigure (f a b)] :
    ElaboratedConfigure (forIn xs init f) := by
  rw [← Array.forIn_toList]
  infer_instance

instance instForInRange {β : Type} (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → Configure (ForInStep β)) [∀ i b, ElaboratedConfigure (f i b)] :
    ElaboratedConfigure (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  infer_instance

/-- `Array.mapM`'s loop from index `i`. -/
@[reducible] def mapMLoop {α β : Type} (f : α → Configure β) [∀ a, ElaboratedConfigure (f a)]
    (as : Array α) (i : Nat) (bs : Array β) :
    ElaboratedConfigure (Array.mapM.map f as i bs) := by
  rw [Array.mapM.map]
  by_cases h : i < as.size
  · rw [dite_eq_left h]
    refine @Halo2.ElaboratedConfigure.bind F _ _ (f as[i]) inferInstance _ ?_
    intro b
    exact mapMLoop f as (i + 1) (bs.push b)
  · rw [dite_eq_right h]
    exact Halo2.ElaboratedConfigure.pure bs
termination_by as.size - i

instance instMapM {α β : Type} (f : α → Configure β) [∀ a, ElaboratedConfigure (f a)]
    (as : Array α) : ElaboratedConfigure (as.mapM f) := by
  unfold Array.mapM
  exact mapMLoop f as 0 _

end Midnight.Frontend
