import Lean
import Clean.Tables.Fibonacci8
import Clean.Table.Json

open Tables.Fibonacci8Table


-- generate trace using the witness generators from `EveryRowExceptLast` table constraint
def fib_relation_babybear := fib_relation (p := p_babybear)
def init_row : RowType (F p_babybear) := { x := 0, y := 1 }

#eval witnesses fib_relation_babybear init_row 20
