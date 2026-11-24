import Midnight.Math.Witness.DependencyPlan

/-! Proof-carrying snapshots of the ordered checker's prior-address set.
The tree data may be generated externally, but replacing a running state requires
an exact kernel-checked equality. Well-formedness is transported from that state;
it is never assumed for a generated tree. -/
namespace Midnight.Math.Witness.DependencySnapshot
attribute [local instance] lexOrd

abbrev Key := Nat × Nat × Int
abbrev Raw := Std.DTreeMap.Internal.Impl Key (fun _ => Unit)
abbrev State := Std.TreeSet Key

def raw (state : State) : Raw := state.inner.inner.inner

/-- Structural equality of snapshot data, including cached subtree sizes. -/
def equal : Raw → Raw → Bool
  | .leaf, .leaf => true
  | .inner ls lk _ ll lr, .inner rs rk _ rl rr =>
    (ls == rs) && (lk == rk) && equal ll rl && equal lr rr
  | _, _ => false

theorem equal_eq_true (left right : Raw) : equal left right = true ↔ left = right := by
  induction left generalizing right with
  | leaf => cases right <;> simp [equal]
  | inner size key value left right ihLeft ihRight =>
    cases right <;> simp_all [equal, and_assoc]

theorem raw_injective : Function.Injective raw := by
  rintro ⟨⟨⟨left,leftWF⟩⟩⟩ ⟨⟨⟨right,rightWF⟩⟩⟩ same
  cases same
  rfl

/-- Restore only the checked data, carrying the original invariant proof. -/
def restore (state : State) (data : Raw) (same : raw state = data) : State :=
  ⟨⟨⟨data, same ▸ state.inner.inner.wf⟩⟩⟩

theorem restore_eq (state : State) (data : Raw) (same : raw state = data) :
    restore state data same = state := raw_injective same.symm

end Midnight.Math.Witness.DependencySnapshot
