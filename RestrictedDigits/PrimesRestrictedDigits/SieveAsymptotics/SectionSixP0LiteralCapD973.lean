import PrimesRestrictedDigits.BasicEstimates.CoordinateNestedEquivD905
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0ExactForestD972

/-!
# The literal P0 integral allocation

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12). The exact certificate is transported
by the existing volume-preserving coordinate equivalence.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

theorem sectionSixP0NestedProfile_integral_lt_D973 :
    (∫ x in sectionSixFirstLowCentralSmallI5P0RefinedBase,
      sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 x) <
        (2273 / 100000 : Real) := by
  have htransport := coordinateNestedEquiv_preserving.setIntegral_preimage_emb
    coordinateNestedEquiv.measurableEmbedding
    sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963
    sectionSixFirstLowCentralSmallI5P0RefinedBase
  rw [← htransport]
  simpa only [Set.preimage, coordinateNestedEquiv_apply] using
    sectionSixP0Profile_integral_lt_D972

theorem sectionSixP0Target_integral_lt_D973 :
    (∫ z in sectionSixFirstLowCentralSmallI5PairPatternTarget (0 : Fin 4),
      sectionSixFirstLowCentralSmallQuadrupleKernel z) < (2273 / 100000 : Real) :=
  sectionSixFirstLowCentralSmallI5P0Target_integral_le_twoCeilingProfile_D963.trans_lt
    sectionSixP0NestedProfile_integral_lt_D973

end PrimesRestrictedDigits
