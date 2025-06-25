import Lean
import Clean.Tables.Fibonacci8
import Clean.Tables.Fibonacci32Inductive
import Clean.Table.Json

-- serialize constraints of the Fibonacci8 table to JSON
def fib8json := Lean.toJson (Tables.Fibonacci8Table.fib_table (p:= pBabybear))
-- #eval fib8json

-- serialize constraints of the Fibonacci32 table to JSON
def fib32json := Lean.toJson ((Tables.Fibonacci32Inductive.table (p:= pBabybear)).tableConstraints
  { x := U32.from_byte 0, y:= U32.from_byte 1 }
  { x := U32.from_byte 0, y:= U32.from_byte 0 })
-- #eval fib32json
