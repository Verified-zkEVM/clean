import Clean.Gadgets.Xor.Xor32
open Gadgets
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]
example (x : Var Xor.Xor32.Inputs (F p)) : (Xor.Xor32.circuit (p := p)).localLength x = 4 := rfl
