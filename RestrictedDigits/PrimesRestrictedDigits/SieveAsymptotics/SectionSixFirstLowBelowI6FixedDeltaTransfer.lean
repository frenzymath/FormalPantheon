import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6FixedDeltaRegularity
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exact-to-fixed-delta transfer for the low-below I6 term

The low-below exact regions are monotone in the epsilon parameter. This module uses that fact
and the fixed-delta regularity module to compare every smaller epsilon with the literal `delta
= 1 / 1000000` region.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowBelowQuadrupleIntegral_le_delta5
    {epsilon : Real} (hepsilonUpper : epsilon <= 1 / 1000000) :
    sectionSixFirstLowBelowQuadrupleIntegral epsilon <=
      ∫ x in sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000),
        sectionSixFirstLowBelowQuadrupleKernel x := by
  have hnonneg : 0 ≤ᵐ[volume.restrict
      (sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000))]
      sectionSixFirstLowBelowQuadrupleKernel := by
    filter_upwards [ae_restrict_mem
      sectionSixFirstLowBelowQuadrupleRegion_delta5_measurable] with x hx
    exact sectionSixFirstLowBelowQuadrupleKernel_nonneg_delta5 hx
  unfold sectionSixFirstLowBelowQuadrupleIntegral
  exact setIntegral_mono_set
    sectionSixFirstLowBelowQuadrupleKernel_integrable_delta5 hnonneg
    (Filter.Eventually.of_forall
      (sectionSixFirstLowBelowQuadrupleRegion_mono hepsilonUpper))

end

end PrimesRestrictedDigits
