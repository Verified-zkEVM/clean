import Clean.Halo2.Basic

/-!
# Exact-ish Halo2 pinned constraint-system data

This module starts mirroring the part of `halo2_proofs` that determines
`VerifyingKey::pinned().cs`.  It is intentionally separate from the Clean
semantics in `Clean.Halo2.Basic`: this file is about reproducing Halo2's pinned
constraint-system artifact from idiomatic circuit-building code.
-/

namespace Halo2.Pinned

inductive Rotation where
  | rot : Int → Rotation
deriving Repr, DecidableEq, BEq

inductive ColumnKind where
  | Advice
  | Fixed
  | Instance
deriving Repr, DecidableEq, BEq, Inhabited

structure Column where
  index : Nat
  columnType : ColumnKind
deriving Repr, DecidableEq, BEq, Inhabited

namespace Column

def advice (i : Nat) : Column := ⟨i, .Advice⟩
def fixed (i : Nat) : Column := ⟨i, .Fixed⟩
def instanceCol (i : Nat) : Column := ⟨i, .Instance⟩

end Column

/-- Halo2 expression nodes as they appear in pinned CS debug output. -/
inductive Expression where
  | constant : String → Expression
  | selector : Nat → Expression
  | fixed : Nat → Nat → Rotation → Expression
  | advice : Nat → Nat → Rotation → Expression
  | instance : Nat → Nat → Rotation → Expression
  | negated : Expression → Expression
  | sum : Expression → Expression → Expression
  | product : Expression → Expression → Expression
  | scaled : Expression → String → Expression
deriving Repr, DecidableEq, BEq

namespace Expression

instance : Neg Expression where neg := Expression.negated
instance : Add Expression where add := Expression.sum
instance : Sub Expression where sub a b := a + (-b)
instance : Mul Expression where mul := Expression.product

def scale (e : Expression) (c : String) : Expression := .scaled e c

end Expression

structure LookupArgument where
  inputExpressions : List Expression
  tableExpressions : List Expression
deriving Repr, DecidableEq, BEq

structure PermutationArgument where
  columns : List Column
deriving Repr, DecidableEq, BEq

structure ConstraintSystem where
  numFixedColumns : Nat := 0
  numAdviceColumns : Nat := 0
  numInstanceColumns : Nat := 0
  numSelectors : Nat := 0
  gates : List Expression := []
  adviceQueries : List (Column × Rotation) := []
  instanceQueries : List (Column × Rotation) := []
  fixedQueries : List (Column × Rotation) := []
  permutation : PermutationArgument := ⟨[]⟩
  lookups : List LookupArgument := []
  constants : List Column := []
  minimumDegree : Option Nat := none
deriving Repr, DecidableEq, BEq

/-- Builder state, including Halo2's query-index allocation order. -/
inductive SelectorKind where
  | simple
  | complex
deriving Repr, DecidableEq, BEq

structure Builder where
  cs : ConstraintSystem := {}
  selectorKinds : List SelectorKind := []

def Builder.adviceColumn (b : Builder) : Column × Builder :=
  let col := Column.advice b.cs.numAdviceColumns
  (col, { b with cs.numAdviceColumns := b.cs.numAdviceColumns + 1 })

def Builder.fixedColumn (b : Builder) : Column × Builder :=
  let col := Column.fixed b.cs.numFixedColumns
  (col, { b with cs.numFixedColumns := b.cs.numFixedColumns + 1 })

def Builder.instanceColumn (b : Builder) : Column × Builder :=
  let col := Column.instanceCol b.cs.numInstanceColumns
  (col, { b with cs.numInstanceColumns := b.cs.numInstanceColumns + 1 })

private def queryIndexOf? (q : Column × Rotation) (qs : List (Column × Rotation)) : Option Nat :=
  qs.findIdx? (· == q)

def Builder.queryAdvice (b : Builder) (col : Column) (rot : Rotation) : Expression × Builder :=
  let q := (col, rot)
  match queryIndexOf? q b.cs.adviceQueries with
  | some idx => (.advice idx col.index rot, b)
  | none =>
      let idx := b.cs.adviceQueries.length
      (.advice idx col.index rot, { b with cs.adviceQueries := b.cs.adviceQueries ++ [q] })

def Builder.queryFixed (b : Builder) (col : Column) (rot : Rotation) : Expression × Builder :=
  let q := (col, rot)
  match queryIndexOf? q b.cs.fixedQueries with
  | some idx => (.fixed idx col.index rot, b)
  | none =>
      let idx := b.cs.fixedQueries.length
      (.fixed idx col.index rot, { b with cs.fixedQueries := b.cs.fixedQueries ++ [q] })

def Builder.queryInstance (b : Builder) (col : Column) (rot : Rotation) : Expression × Builder :=
  let q := (col, rot)
  match queryIndexOf? q b.cs.instanceQueries with
  | some idx => (.instance idx col.index rot, b)
  | none =>
      let idx := b.cs.instanceQueries.length
      (.instance idx col.index rot, { b with cs.instanceQueries := b.cs.instanceQueries ++ [q] })

/-- Halo2 selectors are virtual during configuration. They become fixed columns
when selector compression runs during keygen. -/
def Builder.selector (b : Builder) : Nat × Builder :=
  let index := b.cs.numSelectors
  let cs := { b.cs with numSelectors := index + 1 }
  (index, { b with cs := cs, selectorKinds := b.selectorKinds ++ [.simple] })

def Builder.complexSelector (b : Builder) : Nat × Builder :=
  let index := b.cs.numSelectors
  let cs := { b.cs with numSelectors := index + 1 }
  (index, { b with cs := cs, selectorKinds := b.selectorKinds ++ [.complex] })

def Builder.enableEquality (b : Builder) (col : Column) : Builder :=
  let b :=
    match col.columnType with
    | .Advice => (b.queryAdvice col (.rot 0)).2
    | .Fixed => (b.queryFixed col (.rot 0)).2
    | .Instance => (b.queryInstance col (.rot 0)).2
  if b.cs.permutation.columns.contains col then b else
    { b with cs.permutation.columns := b.cs.permutation.columns ++ [col] }

def Builder.enableConstant (b : Builder) (col : Column) : Builder :=
  let b := if b.cs.constants.contains col then b else { b with cs.constants := b.cs.constants ++ [col] }
  b.enableEquality col

def Builder.createGate (b : Builder) (polys : List Expression) : Builder :=
  { b with cs.gates := b.cs.gates ++ polys }

def Builder.lookup (b : Builder) (args : LookupArgument) : Builder :=
  { b with cs.lookups := b.cs.lookups ++ [args] }

def Builder.ensureNumSelectors (b : Builder) (n : Nat) : Builder :=
  if b.cs.numSelectors < n then { b with cs.numSelectors := n } else b

end Halo2.Pinned
