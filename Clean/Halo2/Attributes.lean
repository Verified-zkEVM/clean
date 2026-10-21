import Lean

open Lean

/-- Structural chunk-split set (the `infer_explicit_circuits` model: a handful of
special-cased constructor lemmas, extensible by tagging — nothing at the tactic layer
hard-codes the shapes). The lemmas decompose a raw step's `Constraints`/`ExtendsWitnesses`
chunk along the circuit CONSTRUCTORS only — region-level bind spines, `assignRegion`
wrappers, loop combinators — leaving every leaf untouched: gates, witness ops, and
especially folded `.call` boundaries keep their pristine spellings. The cps2 in-peel
engine fires exactly this set to expose embedded call chunks before converting them by
direct leaf application (`atomic-binds-design.md`, "The in-peel engine"); `circuit_norm`
(a superset) opens the remaining non-call leaves afterwards, in the landing.

Deliberately NOT members: the layouter spine lemmas (`Circuit.operations_bind`,
`Halo2.constraints_append`/`extendsWitnesses_append`) — the peel owns the layouter
spine, and their absence is what makes firing this set on a mid-peel goal safe.

To extend: tag a new combinator's `*_constraints` and `*_extendsWitnesses` split lemmas
(and any `*_operations` bridge they need to fire). -/
register_simp_attr chunk_split
