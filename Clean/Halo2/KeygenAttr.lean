import Lean.Meta.Tactic.Simp.RegisterCommand
import Batteries.Lean.TagAttribute

/-- Structural reductions used by the `keygen_registration` tactic. -/
register_simp_attr keygen_norm

/-- Cheap operation-spine reductions run before the broader keygen normalization set. -/
register_simp_attr keygen_spine

namespace Halo2

open Lean

initialize keygenCallAttr : TagAttribute ←
  registerTagAttribute `keygen_call
    "A folded circuit-call certificate used by keygen registration."

initialize keygenCallExpressionAttr : TagAttribute ←
  registerTagAttribute `keygen_call_expression
    "An opaque circuit-call expression recognized by keygen registration."

initialize keygenCallBundleAttr : TagAttribute ←
  registerTagAttribute `keygen_call_bundle
    "A formal-circuit bundle type carried by a keygen call expression."

initialize keygenConfiguredAttr : TagAttribute ←
  registerTagAttribute `keygen_configured
    "A constructor proving that a circuit config came from its configure program."

initialize keygenHelperAttr : TagAttribute ←
  registerTagAttribute `keygen_helper
    "A registration certificate for a raw circuit helper."

initialize keygenBundleProjectionAttr : TagAttribute ←
  registerTagAttribute `keygen_bundle_projection
    "A formal-circuit projection through which keygen registration finds a concrete bundle."

initialize keygenRequirementProjectionAttr : TagAttribute ←
  registerTagAttribute `keygen_requirement_projection
    "A keygen-requirement projection safe to reduce without exposing configure or synthesis."

initialize keygenMetadataProjectionAttr : TagAttribute ←
  registerTagAttribute `keygen_metadata_projection
    "A keygen metadata projection that may be unfolded without exposing synthesis operations."

end Halo2
