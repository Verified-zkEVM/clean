# Requirements for new code in the repo

**Uses Mathlib naming convention**. Names follow the [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html). In short:

- Types, structures and Prop-valued definitions and classes are `UpperCamelCase` (`FormalCircuit`, `SelectorFree`).
- Functions and other terms are `lowerCamelCase` (`localLength`, `fieldFromBits`).
- Theorems and proofs are `snake_case`, named after their statement: `_of_` separates the conclusion from the hypotheses, in order (`lt_of_succ_le`), and standard property names are used (`comm`, `assoc`, `inj`, `congr`, `ext`, `iff`, `mono`). Names of other declarations inside a theorem name are spelled as usual, e.g. `lowerCamelCase` (`eval_fromElements`).
- Each underscore-separated part of a theorem name should correspond to a declaration in its statement or a standard logical/property name (`iff`, `of`, `mem`, `comm`, …), not an invented English description.
- Spell namespace-qualified names in theorem names as one lowerCamelCase component: `RegionOperation.Constraints` becomes `regionOperationConstraints`, not `regionOperation_constraints`.
- Acronyms are treated as words (`HtmlParser`, not `HTMLParser`), and names use American English.
- Related declarations are grouped in namespaces that enable dot notation (`List.map`, then `l.map f`).

**No Lean namespace redundancy**. Inside a `namespace Foo`, there is no reference/opening that is unnecessarily qualified with `Foo.`, or (even worse) `_root_.Foo.`. Can be easily checked by grepping for `Foo` in the relevant files. This also applies to nested namespaces like `Foo.Bar`.

**Proofs use the library's normal forms, not framework internals**. A gadget proof's simp list shouldn't need raw typeclass projections, framework lemmas or `with_unfolding_all`; needing them signals a missing `circuit_norm` lemma, which belongs in the framework. When the framework introduces a new normal form, proofs and helpers are restated at it, not bridged back to the old spelling.

**Robust, explicit proof steps**. Targeted `simp only`/`rw` steps are preferred over defeq-based terms like `exact congrArg _ ih`. Concrete proofs contain no `try`: each case states the facts it needs, so the proof shows its dependencies (`grind`/`omega` as terminal closers are fine).

**Clean, efficient meta/tactic code**. Meta code inspects the goal and runs the matching stage instead of trying tactic sequences until one succeeds; backtracking is a last-resort failure path. Rewrite rules and simprocs live in labelled simp sets (e.g. `computable_witnesses`), not in lemma lists hard-coded in meta code. A tactic feature pays for itself across the corpus: deleting an already short manual proof or handling a rare, fully abstract composition doesn't justify it.
