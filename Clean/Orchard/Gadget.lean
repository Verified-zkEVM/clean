import Clean.Circuit

/-!
# Orchard source gadget APIs

TODO(source-conformance): implement the source-level Orchard gadget entry circuits in this
module.

The previous `value_commit_orchard`, `derive_nullifier`, and spend-authority wrappers
accepted fixed-base multiplication, Poseidon, and scalar-multiplication products as
inputs. That is not the source API and it hides the actual witness boundaries of the
Orchard circuits.

Rebuild these only after the required child entry circuits are available:
- fixed-base scalar multiplication for value commitments, nullifiers, note commitments,
  incoming viewing keys, and spend authority;
- Poseidon hash/permutation entry circuits for nullifier derivation;
- complete point addition composed through the real ECC entry API.
-/

namespace Orchard
namespace Gadget

/-!
TODO(source-conformance): `value_commit_orchard` is not implemented.

The replacement should witness the fixed-base products internally and expose the clean
source-level value-commitment API, instead of taking `valueProduct*` and `blindProduct*`
as row inputs.
-/

/-!
TODO(source-conformance): `derive_nullifier` is not implemented.

The replacement should compose the Poseidon hash, nullifier fixed-base multiplication,
and complete addition internally, instead of taking the Poseidon result and scalar-mul
product as row inputs.
-/

/-!
TODO(source-conformance): spend-authority key derivation is not implemented.

The replacement should witness `[alpha] SpendAuthG` internally and then compose complete
addition with `ak_P`, instead of taking the fixed-base product as a row input.
-/

end Gadget
end Orchard
