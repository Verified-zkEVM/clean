import Lean.Meta.Tactic.Simp.RegisterCommand
import Batteries.Lean.TagAttribute

/-- Structural reductions used by the `keygen_registration` tactic. -/
register_simp_attr keygen_norm

/-- Cheap operation-spine reductions run before the broader keygen normalization set. -/
register_simp_attr keygen_spine

/-- Reduced circuit-output projections used only while routing keygen call premises. -/
register_simp_attr keygen_output_norm

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

syntax (name := keygenConfiguredOutput) "keygen_configured_output" ident : attr

initialize keygenConfiguredOutputAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `keygenConfiguredOutput
    descr := "An output-configured constructor and its matching configure projection."
    getParam := fun _ stx => match stx with
      | `(attr| keygen_configured_output $projection:ident) =>
          pure projection.getId
      | _ => throwError "expected a configure projection" }

syntax (name := keygenConfiguredPure) "keygen_configured_pure" ident : attr

initialize keygenConfiguredPureAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `keygenConfiguredPure
    descr := "A pure-configured constructor and its matching configure projection."
    getParam := fun _ stx => match stx with
      | `(attr| keygen_configured_pure $projection:ident) =>
          pure projection.getId
      | _ => throwError "expected a configure projection" }

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

initialize keygenConfigureProjectionAttr : TagAttribute ←
  registerTagAttribute `keygen_configure_projection
    "The configure projection of a formal circuit bundle."

end Halo2
