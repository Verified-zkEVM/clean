import Clean.Utils.Primes
import Clean.GadgetsNew.Add8.Addition8

section

#eval!
  let p := 1009
  let p_prime := Fact.mk prime_1009
  let p_non_zero := Fact.mk (by norm_num : p ≠ 0)
  let p_large_enough := Fact.mk (by norm_num : p > 512)
  let main := do
    let x ← witness (fun _ => 10)
    let y ← witness (fun _ => 20)
    let z ← Add8.add8 (p:=p) { x, y }
    Add8.add8 (p:=p) { x, y := z }
  main.operations
end
