import Lean
import Clean.Tables.Fibonacci8
import Clean.Table.WitnessGeneration
import Clean.Table.Json

open Tables.Fibonacci8Table

-- generate trace using the witness generators from `EveryRowExceptLast` table constraint
def fibRelationBabybear := fibRelation (p:=p_babybear)
def initRow : RowType (F p_babybear) := { x := 0, y := 1 }

#eval witnesses fibRelationBabybear initRow 20

-- def data := Lean.toJson (witnesses fibRelationBabybear initRow 1000000)

-- def dumpJson (j : Lean.Json) (path := "trace.json") : IO Unit := do
--   IO.FS.writeFile path j.compress   -- or `j.pretty`

-- #eval dumpJson data
