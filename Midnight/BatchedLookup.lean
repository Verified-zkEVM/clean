namespace Midnight

/-- Parallel input tuples sharing one selector and table. The expression type
can retain native syntax. Checked configuration supplies arity/selector proofs
and projects membership to existing Halo2 lookup arguments. -/
structure LookupBatch (Expression : Type) where
  name : String
  selector : Expression
  inputs : Array (Array Expression)
  table : Array Expression

end Midnight
