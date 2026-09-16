import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1OuterResidualReductionD891
import Mathlib.Tactic.Linarith

/-!
# relaxed P0/P2-to-I5 arithmetic adapter

This module consumes a literal P0/P2 target budget at the relaxed threshold `640911 /
12500000` and returns the corresponding fixed-delta I5 outer cap `5558 / 100000`. It is
arithmetic only: no target transport or numerical certificate is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralSmallI5D916_outer_integral_lt_5558_of_target_budget
    (hBudget :
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget (0 : Fin 4),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget (2 : Fin 4),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) <
      (640911 / 12500000 : Real)) :
    (∫ x in sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real),
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) <
      (5558 / 100000 : Real) := by
  have hreduce :=
    sectionSixFirstLowCentralSmallI5D891_outer_integral_lt_p0_p2_reduced
  linarith

end
end PrimesRestrictedDigits
