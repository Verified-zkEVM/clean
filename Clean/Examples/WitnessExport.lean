import Clean.Circuit.WitnessExport
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.IsZeroField
import Clean.Gadgets.Bits
import Clean.Gadgets.Keccak.Permutation
import Clean.Utils.Primes

/-!
Exercises `#assert_exportable` and `#witgen_json` (witgen IR plan, phase 6) on ported
gadgets, including a guarded failure for a native-closure witness.
-/

namespace Examples.WitnessExport

/-- info: exportable ✓ (8 witness cells) -/
#guard_msgs in
#assert_exportable (Gadgets.Xor64.circuit (p := pBabybear))

/-- info: exportable ✓ (2 witness cells) -/
#guard_msgs in
#assert_exportable (Gadgets.IsZeroField.circuit (F := F pBabybear))

/-- info: exportable ✓ (16 witness cells) -/
#guard_msgs in
#assert_exportable (Gadgets.toBits (p := pBabybear) 16 (by native_decide))

/-- info: exportable ✓ (30912 witness cells) -/
#guard_msgs in
#assert_exportable (Gadgets.Keccak256.Permutation.circuit (p := pBabybear))

-- a native witness is rejected, with its location
def nativeCircuit : Circuit (F pBabybear) (Expression (F pBabybear)) :=
  witnessFieldNative fun _ => 42

/-- error: not exportable: witness operations at flat indices [0] are native closures -/
#guard_msgs in
#assert_exportable nativeCircuit

-- JSON schema golden test: the payload a Rust witgen interpreter consumes
/--
info: {"version": 1,
 "operations":
 [{"witness": 1,
   "code":
   {"steps": [],
    "output":
    {"type": "elements",
     "elements":
     [{"type": "ite",
       "then": {"value": 0, "type": "const"},
       "else":
       {"type": "inv",
        "arg": {"type": "expr", "expr": {"type": "var", "index": 0}}},
       "cond":
       {"type": "eq",
        "rhs": {"value": 0, "type": "const"},
        "lhs": {"type": "expr", "expr": {"type": "var", "index": 0}}}}]}}},
  {"witness": 1,
   "code":
   {"steps": [],
    "output":
    {"type": "elements",
     "elements":
     [{"type": "expr",
       "expr":
       {"type": "add",
        "rhs":
        {"type": "mul",
         "rhs":
         {"type": "mul",
          "rhs": {"type": "var", "index": 1},
          "lhs": {"type": "var", "index": 0}},
         "lhs": {"value": 2013265920, "type": "const"}},
        "lhs": {"value": 1, "type": "const"}}}]}}},
  {"assert":
   {"type": "add",
    "rhs":
    {"type": "mul",
     "rhs":
     {"type": "add",
      "rhs":
      {"type": "mul",
       "rhs":
       {"type": "mul",
        "rhs": {"type": "var", "index": 1},
        "lhs": {"type": "var", "index": 0}},
       "lhs": {"value": 2013265920, "type": "const"}},
      "lhs": {"value": 1, "type": "const"}},
     "lhs": {"value": 2013265920, "type": "const"}},
    "lhs": {"type": "var", "index": 2}}},
  {"assert":
   {"type": "add",
    "rhs":
    {"type": "mul",
     "rhs": {"value": 0, "type": "const"},
     "lhs": {"value": 2013265920, "type": "const"}},
    "lhs":
    {"type": "mul",
     "rhs": {"type": "var", "index": 0},
     "lhs": {"type": "var", "index": 2}}}}],
 "localLength": 2}
-/
#guard_msgs in
#witgen_json (Gadgets.IsZeroField.circuit (F := F pBabybear))

end Examples.WitnessExport
