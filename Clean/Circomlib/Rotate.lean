import Clean.Circuit

namespace Circomlib
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/sha256/rotate.circom
-/

namespace RotR

/-
template RotR(n, r) {
    signal input in[n];
    signal output out[n];

    for (var i = 0; i < n; i++) {
        out[i] <== in[ (i+r)%n ];
    }
}
-/

end RotR
end Circomlib
