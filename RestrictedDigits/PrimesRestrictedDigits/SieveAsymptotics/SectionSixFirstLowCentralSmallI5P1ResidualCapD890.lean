import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TargetCapCompositionD889
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1FullResidualAssemblyD775
import Mathlib.Tactic.Linarith
/-! # SectionSixFirstLowCentralSmallI5P1ResidualCapD890 -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

private theorem d890_target_adapter :
    (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume))
      < (2147 / 500000 : Real) := by
  simpa only [sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target,
    sectionSixFirstLowCentralSmallI5PairPatternTarget,
    sectionSixFirstLowCentralSmallI5P1D807Target,
    sectionSixFirstLowCentralSmallI5P1D807Delta,
    MeasureTheory.Measure.volume_eq_prod] using
    sectionSixFirstLowCentralSmallI5P1D889_target_integral_lt

theorem sectionSixFirstLowCentralSmallI5P1D890_residual_integral_lt :
    (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume))
      < (2147 / 500000 : Real) := by
  have hdec := sectionSixFirstLowCentralSmallI5P1FullResidualD775_decomposition
  have hlocal0 : 0 ≤
      (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) := by
    apply setIntegral_nonneg
      sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_measurable
    intro x hx
    exact sectionSixFirstLowCentralSmallI5PairPatternTarget_nonneg 1 x
      (sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_subset_target hx)
  have htarget := d890_target_adapter
  linarith

end
end PrimesRestrictedDigits
