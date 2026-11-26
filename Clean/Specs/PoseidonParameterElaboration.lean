/-
Term elaborator that runs the executable Poseidon parameter generator once and
emits ordinary typed vector syntax. This avoids runtime regeneration while
keeping the large numeric tables out of the checked-in source.
-/
module

public import Clean.Specs.PoseidonParameterGeneration

public meta import Lean.Elab.Term
public meta import Clean.Specs.PoseidonParameterGeneration

@[expose] public section

namespace Specs.Poseidon.ParameterGeneration

open Lean Elab Term

meta def vectorSyntax (values : Array ℕ) : TermElabM (TSyntax `term) := do
  let entries : Array (TSyntax `term) := values.map quote
  `(#v[$entries,*])

meta def matrixSyntax (matrix : Matrix) : TermElabM (TSyntax `term) := do
  let rows ← matrix.mapM vectorSyntax
  `(#v[$rows,*])

/-- Generate typed C/M/P/S vector literals while elaborating the surrounding
module. The generator executes once for this term; later uses see ordinary
vector data and do not rerun it. -/
elab "poseidon_parameters% " widthSyntax:num nPartialSyntax:num : term <= expectedType => do
  let some width := Syntax.isNatLit? widthSyntax
    | throwErrorAt widthSyntax "expected a literal state width"
  let some nPartial := Syntax.isNatLit? nPartialSyntax
    | throwErrorAt nPartialSyntax "expected a literal partial-round count"
  let generated := reproduce width nPartial
  let c ← vectorSyntax generated.C
  let m ← matrixSyntax generated.M
  let p ← matrixSyntax generated.P
  let s ← vectorSyntax generated.S
  let term ← `({ C := $c, M := $m, P := $p, S := $s })
  elabTerm term expectedType

end Specs.Poseidon.ParameterGeneration
