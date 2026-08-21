import Clean.Ironwood.Action.SelectorPacking.Rows1

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_20 :
    selectorActivationRows actionReducedSelectorActivations
      20 = expandSelectorRowRuns (actionSelectorRowRuns 20) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_21 :
    selectorActivationRows actionReducedSelectorActivations
      21 = expandSelectorRowRuns (actionSelectorRowRuns 21) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_22 :
    selectorActivationRows actionReducedSelectorActivations
      22 = expandSelectorRowRuns (actionSelectorRowRuns 22) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_23 :
    selectorActivationRows actionReducedSelectorActivations
      23 = expandSelectorRowRuns (actionSelectorRowRuns 23) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_24 :
    selectorActivationRows actionReducedSelectorActivations
      24 = expandSelectorRowRuns (actionSelectorRowRuns 24) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_26 :
    selectorActivationRows actionReducedSelectorActivations
      26 = expandSelectorRowRuns (actionSelectorRowRuns 26) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_27 :
    selectorActivationRows actionReducedSelectorActivations
      27 = expandSelectorRowRuns (actionSelectorRowRuns 27) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_28 :
    selectorActivationRows actionReducedSelectorActivations
      28 = expandSelectorRowRuns (actionSelectorRowRuns 28) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_30 :
    selectorActivationRows actionReducedSelectorActivations
      30 = expandSelectorRowRuns (actionSelectorRowRuns 30) := by
  action_selector_rows

end Zcash.Circuits.Action
