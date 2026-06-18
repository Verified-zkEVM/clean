import Clean.Orchard.Action.Canonicity
import Clean.Orchard.Action.CanonicityTheorems
import Clean.Orchard.Action.AddressIntegrity
import Clean.Orchard.Action.CommitIvk
import Clean.Orchard.Action.CommitIvkGate
import Clean.Orchard.Action.Decompose
import Clean.Orchard.Action.DeriveNullifier
import Clean.Orchard.Action.Gate
import Clean.Orchard.Action.NoteCommit
import Clean.Orchard.Action.SpendAuthority
import Clean.Orchard.Action.ValueCommit

/-!
# Orchard action circuits

Action-level Orchard circuits and mid-level components used by the final action synthesis
entry point.

TODO(source-conformance): implement the full action synthesis entry circuit that composes
Merkle, note-commitment, value-commitment, nullifier, spend-authority, and address
integrity sub-gadgets internally.

Public-instance and equality edges from `Circuit::synthesize` should be built inside the
final action circuit after the child gadgets compute their outputs.
-/

namespace Orchard.Action

/-!
TODO(source-conformance): action computed-output wiring is not implemented.

The replacement should compose source-conformant value-commitment, nullifier, and
spend-authority entry circuits.
-/

/-!
TODO(source-conformance): old/new note-commitment action wiring is not implemented.

The replacement should compose source-conformant `gadgets::note_commit` entry circuits
that compute Sinsemilla commitments and blinding scalar multiplications internally.
-/

/-!
TODO(source-conformance): Merkle-path action wiring is not implemented.

The replacement should compose the full `MerklePath::calculate_root` entry circuit inside
the final action synthesis circuit.
-/

end Orchard.Action
