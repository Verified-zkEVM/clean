import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Specs.Sinsemilla
import Clean.Ironwood.Sinsemilla.Basic
import Clean.Ironwood.Sinsemilla.HashPiece
import Clean.Ironwood.Sinsemilla.Chain

/-!
# Sinsemilla `hash_message` — the layouter-level hash region (Ironwood)

Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`
- `hash_message` (`hash_to_point.rs:37-67`) = `public_q_initialization` (`:122-175`, the
  `allow_init_from_private_point = false` branch) + `hash_all_pieces` (`:218-286`), in ONE
  `"hash_to_point"` region;
- `witness_message_piece` (`chip.rs:105-127` via `SinsemillaInstructions`): each message
  piece witnessed in its own `"witness message piece"` region, `witness_pieces` column,
  row 0.

`public_q_initialization` (public `Q`, the orchard branch): enable `q_sinsemilla4` on the
FIRST row, load `y_Q` into the `fixed_y_q` column at that row, and assign `x_Q` into `x_a`
from a constant (`assign_advice_from_constant` — an equality-constrained constants-column
copy). The hash (`Chain.circuit` = `hash_all_pieces`) starts at the SAME offset: the init
row is the first word row, and the `Initial y_Q` gate checks `2·y_Q = Y_A(row 0)` against
the first word's slopes.

The formal (proof-carrying) bundling of this wrapper — pinning `A = Q` through the constant
copy and the init gate against `Chain.circuit`'s entering-accumulator contract — is the
`CommitDomain`/`Merkle.HashLayer` composition layer.
-/

namespace Halo2.Ironwood.Sinsemilla.HashToPoint

open Orchard (Point)
open Orchard.Specs.Sinsemilla (Generators)

/-- Constant single-cell witness program. -/
def constWit (c : Fp) : WitgenIR Fp 1 := .native fun _ => #v[c]

@[circuit_norm]
theorem constWit_eval (c : Fp) (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((constWit c).eval env)[j] = c := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [constWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Rust `witness_message_piece`: one piece witnessed at `(witness_pieces, 0)` of its own
region, from the caller-supplied witness program. -/
def witnessMessagePiece (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1) :
    Circuit Fp (AssignedCell Fp) :=
  assignRegion "witness message piece" (assignAdvice cfg.witnessPieces 0 w)

/-- Rust `hash_message` (public `Q`): the `"hash_to_point"` region —
`public_q_initialization` at offset 0 (`q_s4` enable, the `fixed_y_q` load, `x_a` from the
constant `Q.x`), then `hash_all_pieces` (`Chain.circuit`) at the same offset. -/
def hashMessage (G : Generators) (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config) (Q : Point Fp)
    (pieces : Var (Sinsemilla.Chain.Inputs ns.length) Fp) : Circuit Fp (Var Sinsemilla.Chain.Output Fp) :=
  assignRegion "hash_to_point" (do
    -- public_q_initialization (hash_to_point.rs:148-175): q_s4 on the first row,
    -- y_Q into fixed_y_q there, x_Q into x_a from a constant
    (Sinsemilla.HashPiece.initialYQGate cfg).enable 0
    let _yq ← assignFixed cfg.fixedYQ 0 Q.y
    let xa ← assignAdvice cfg.xA 0 (constWit Q.x)
    constrainConstant xa Q.x
    -- hash_all_pieces (hash_to_point.rs:218-286) from the init offset
    (Sinsemilla.Chain.circuit G ns (fun _ => Q.y)).call cfg 0 pieces)

end Halo2.Ironwood.Sinsemilla.HashToPoint
