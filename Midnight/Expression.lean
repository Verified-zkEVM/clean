import Clean.Halo2.Expression.Checks

/-! Midnight gates are authored directly in Clean's `Halo2.Expression`. Rust's `Negated`
and `Scaled` nodes are the upstream marker shapes that `Halo2.eraseExpr` recognises when
the VK transcript is produced, so no separate literal AST is needed. What stays
Midnight-specific is selector handling: every selector becomes its own fixed column in
allocation order, with no Zcash selector compression. The executable predicates that decide
upstream's structural gate laws live in `Clean.Halo2.Expression.Checks`. -/

namespace Halo2.Expression
variable {F : Type}

instance (e : Expression F Query) : Decidable e.SelectorFree :=
  decidable_of_iff _ (free_iff e)

/-- All query atoms of an expression, selectors included. -/
def queryAtoms : Expression F Query → List Query
  | .var q => [q]
  | .const _ => []
  | .add a b | .mul a b => a.queryAtoms ++ b.queryAtoms

/-- Whether a simple selector occurs. -/
def hasSimple (e : Expression F Query) : Bool :=
  e.queryAtoms.any fun | .selector q => q.simple | _ => false

/-- Midnight assigns a separate fixed column to every selector, in allocation
order. It does not apply Zcash Halo2's selector compression. -/
def selectorToFixed (firstFixed : Nat) : Query → Query
  | .selector s => .fixed ⟨firstFixed + s.index⟩ 0
  | q => q

def replaceSelectors [Field F] (firstFixed : Nat) (e : Expression F Query) : Expression F Query :=
  e.mapVar (selectorToFixed firstFixed)

end Halo2.Expression
