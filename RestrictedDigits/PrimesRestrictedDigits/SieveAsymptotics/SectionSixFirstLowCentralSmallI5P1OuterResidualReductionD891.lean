import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1ResidualP3TightSubstitutionD778
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1ResidualCapD890
import Mathlib.Tactic.Linarith
/-! # SectionSixFirstLowCentralSmallI5P1OuterResidualReductionD891 -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

private theorem d891_residual_adapter :
    (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) <
      (2147 / 500000 : Real) := by
  simpa only [MeasureTheory.Measure.volume_eq_prod] using
    sectionSixFirstLowCentralSmallI5P1D890_residual_integral_lt

theorem sectionSixFirstLowCentralSmallI5D891_outer_integral_lt_p0_p2_reduced :
    (∫ x in sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real),
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) <
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget (0 : Fin 4),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget (2 : Fin 4),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (53839 / 12500000 : Real) := by
  have houter :=
    sectionSixFirstLowCentralSmallI5PairPatternTarget_setIntegral_le_p1Residual_p3_tight_substituted
  have hres := d891_residual_adapter
  linarith

end
end PrimesRestrictedDigits
