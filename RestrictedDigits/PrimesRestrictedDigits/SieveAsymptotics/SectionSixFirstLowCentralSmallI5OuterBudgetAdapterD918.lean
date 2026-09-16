import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5OuterBudgetAdapterD916
import Mathlib.Tactic.Linarith

/-!
# replay-compatible P0/P2-to-I5 arithmetic adapter

This module consumes separate literal target caps for pair patterns 0 and 2 and returns the
relaxed fixed-delta I5 outer cap `5558 / 100000`. It feeds the existing target-budget adapter,
so no residual proof is duplicated here. It does not assert target transport, a cover, or
either numerical certificate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralSmallI5D918_outer_integral_lt_5558_of_replay_caps
    (hP0 :
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget (0 : Fin 4),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) <
      (2273 / 100000 : Real))
    (hP2 :
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget (2 : Fin 4),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) <
      (1427 / 50000 : Real)) :
    (∫ x in sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real),
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) <
      (5558 / 100000 : Real) := by
  have hBudget :
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget (0 : Fin 4),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget (2 : Fin 4),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) <
      (640911 / 12500000 : Real) := by
    linarith
  exact sectionSixFirstLowCentralSmallI5D916_outer_integral_lt_5558_of_target_budget
    hBudget

end
end PrimesRestrictedDigits
