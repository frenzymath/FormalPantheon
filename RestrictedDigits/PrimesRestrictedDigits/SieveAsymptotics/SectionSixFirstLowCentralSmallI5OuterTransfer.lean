import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5OuterIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exact-to-fixed-outer transfer for the low central-small I5 term

For nonnegative epsilon below the cutoff, the exact weak I5 carrier is contained in the fixed
mixed outer carrier. supplies the integrability and nonnegativity needed to compare the two
restricted integrals.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralSmallQuadrupleIntegral_le_fixed_outer
    {epsilon : Real}
    (hepsilonNonneg : 0 <= epsilon)
    (hepsilonUpper : epsilon <= 1 / 1000000) :
    sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon <=
      ∫ x in sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000),
        sectionSixFirstLowCentralSmallQuadrupleKernel x := by
  have hnonneg : 0 ≤ᵐ[volume.restrict
      (sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000))]
      sectionSixFirstLowCentralSmallQuadrupleKernel := by
    filter_upwards [ae_restrict_mem
      sectionSixFirstLowCentralSmallUniformOuterRegion_delta5_measurable] with x hx
    exact sectionSixFirstLowCentralSmallUniformOuterKernel_nonneg hx
  unfold sectionSixFirstLowCentralSmallQuadrupleIntegral
  exact setIntegral_mono_set
    sectionSixFirstLowCentralSmallUniformOuterKernel_integrable hnonneg
    (Filter.Eventually.of_forall
      (sectionSixFirstLowCentralSmallQuadrupleRegion_subset_uniformOuterRegion
        hepsilonNonneg hepsilonUpper))

end

end PrimesRestrictedDigits
