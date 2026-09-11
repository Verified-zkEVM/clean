module

public import Lean
public import Clean.Tables.Fibonacci8
public import Clean.Tables.Fibonacci32Inductive
public import Clean.Table.Json

@[expose] public section

-- serialize constraints of the Fibonacci8 table to JSON
def fib8json := Lean.toJson (Tables.Fibonacci8Table.fibTable (p:=pBabybear))
-- #eval fib8json

-- serialize constraints of the Fibonacci32 table to JSON
def fib32json := Lean.toJson ((Tables.Fibonacci32Inductive.table (p:=pBabybear)).tableConstraints
  { x := U32.fromByte 0, y := U32.fromByte 1 }
  { x := U32.fromByte 0, y := U32.fromByte 0 })
-- #eval fib32json
