import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P3TightSubstitution
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1FullResidualAssemblyD775
import Mathlib.Tactic.Linarith
/-! # SectionSixFirstLowCentralSmallI5P1ResidualP3TightSubstitutionD778 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
# fixed-target P1 residual bookkeeping

Compose the tight P3 substitution with the four-cell P1 residual assembly. The P1 residual
remains an explicit symbolic term; this module proves no residual estimate, source equality,
or I5 cap.
-/

theorem sectionSixFirstLowCentralSmallI5PairPatternTarget_setIntegral_le_p1Residual_p3_tight_substituted :
    (∫ x in sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real),
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) ≤
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 0,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 2,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (41 / 3125000 : Real) := by
  have hagg :=
    sectionSixFirstLowCentralSmallI5PairPatternTarget_setIntegral_le_p3_tight_substituted
  have hp1 :
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 1,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) ≤
      (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (39 / 12500000 : Real) := by
    simpa [sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target,
      MeasureTheory.Measure.volume_eq_prod] using
      sectionSixFirstLowCentralSmallI5P1FullResidualD775_upper
  linarith


end
end PrimesRestrictedDigits
