import Lean
import Clean.Tables.Fibonacci8

-- serialize constraints of the Fibonacci8 table to JSON
#eval Lean.toJson (Tables.Fibonacci8Table.fib_table (p:= p_babybear))
