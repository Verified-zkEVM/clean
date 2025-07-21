import Clean.Utils.Tactics.DecomposeProvablePair
import Clean.Circuit.Provable
import Clean.Utils.Field

variable {p : ℕ} [Fact p.Prime]

-- Test the specific types involved
variable (p' : ℕ) [Fact p'.Prime]
def testType1 : Type := F p' × F p'
def testType2 : Type := (F p' × F p') × F p'

-- Check type equality
#check (testType1 p' : Type)
#check (fieldPair (F p') : Type)

-- Test nested pairs with decomposition
example (input : (F p × F p) × F p) (h : input.1.1 = 5) :
    input.1.2 + input.2 = input.1.1 + input.1.2 + input.2 - 5 := by
  decompose_provable_pair
