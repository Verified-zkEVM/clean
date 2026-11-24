import Midnight.Frontend.Configure

/-! Native chip configuration shared by the stdlib examples, ported at midnight-zk
1e39c120d05200373285fba0e69766e40292b470: `circuits/src/field/native/native_chip.rs::configure`
and `circuits/src/field/decomposition/pow2range.rs::configure`. -/
namespace Midnight.Frontend
open scoped Halo2.ElaboratedConfigure
open Halo2 (Column)

def nativeConfigure (values : Array (Column .advice)) (fixeds : Array (Column .fixed))
    (instances : Array (Column .instance)) : Configure Unit := do
  let q_arith ← selector
  let q_12_minus_34 ← selector
  let q_par_add ← selector
  let q_next_col := fixeds[0]!
  let mul_ab_col := fixeds[1]!
  let mul_ac_col := fixeds[2]!
  let constant_col := fixeds[3]!
  let coeff_cols := fixeds.extract 4 fixeds.size
  let fixed_values_col ← fixedColumn
  enableEquality fixed_values_col
  for c in values do enableEquality c
  for c in instances do enableEquality c
  gate "arith_gate" q_arith do
    let vals ← values.mapM fun c => advice c
    let next_value ← advice values[0]! 1
    let coeffs ← coeff_cols.mapM fun c => fixed c
    let q_next_coeff ← fixed q_next_col
    let mul_ab_coeff ← fixed mul_ab_col
    let mul_ac_coeff ← fixed mul_ac_col
    let constant ← fixed constant_col
    let id := (vals.zip coeffs).foldl (fun acc (value, coeff) => acc + coeff * value) constant
      + q_next_coeff * next_value
      + mul_ab_coeff * vals[0]?.getD (.const 0) * vals[1]?.getD (.const 0)
      + mul_ac_coeff * vals[0]?.getD (.const 0) * vals[2]?.getD (.const 0)
    return #[("", id)]
  gate "12_minus_34" q_12_minus_34 do
    let v1 ← advice values[1]!
    let v2 ← advice values[2]!
    let v3 ← advice values[3]!
    let v4 ← advice values[4]!
    return #[("", v1 + v2 - v3 - v4)]
  gate "parallel_add_gate" q_par_add do
    let mut ids := #[]
    for i in [:3] do
      let val ← advice values[i]!
      let res ← advice values[i]! 1
      let c ← fixed coeff_cols[i]!
      ids := ids.push ("", val + c - res)
    return ids

def rangeConfigure (values : Array (Column .advice)) : Configure Unit := do
  let q_pow2range ← complexSelector
  let tag_col ← fixedColumn
  let t_tag ← lookupTableColumn
  let t_val ← lookupTableColumn
  batchedLookup "pow2range column check" (some q_pow2range) do
    let tag ← fixed tag_col
    let tags := Array.replicate values.size tag
    let vals ← values.mapM fun c => advice c
    return #[(tags, t_tag), (vals, t_val)]

instance (values : Array (Column .advice)) (fixeds : Array (Column .fixed))
    (instances : Array (Column .instance)) :
    Halo2.ElaboratedConfigure (nativeConfigure values fixeds instances) := by
  unfold nativeConfigure
  try dsimp only
  elaborate_configure

instance (values : Array (Column .advice)) :
    Halo2.ElaboratedConfigure (rangeConfigure values) := by
  unfold rangeConfigure
  try dsimp only
  elaborate_configure

end Midnight.Frontend
