# Requirements for new code in the repo

**Uses Mathlib naming convention**. Names follow the [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html). In short:

- Types, structures and Prop-valued definitions and classes are `UpperCamelCase` (`FormalCircuit`, `IsBool`); adjective-like Props take an `Is` prefix.
- Functions and other terms are `lowerCamelCase` (`localLength`, `fieldFromBits`).
- Theorems and proofs are `snake_case`, named after their statement: `_of_` separates the conclusion from the hypotheses, in order (`lt_of_succ_le`), and standard property names are used (`comm`, `assoc`, `inj`, `congr`, `ext`, `iff`, `mono`). Names of other declarations inside a theorem name are spelled as usual, e.g. `lowerCamelCase` (`eval_fromElements`).
- Acronyms are treated as words (`HtmlParser`, not `HTMLParser`), and names use American English.
- Related declarations are grouped in namespaces that enable dot notation (`List.map`, then `l.map f`).

**No Lean namespace redundancy**. Inside a `namespace Foo`, there is no reference/opening that is unnecessarily qualified with `Foo.`, or (even worse) `_root_.Foo.`. Can be easily checked by grepping for `Foo` in the relevant files. This also applies to nested namespaces like `Foo.Bar`.
