import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0LiteralCapD973
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LiteralCapD992
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5OuterBudgetAdapterD918
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5OuterTransfer

/-!
# The uniform I5 integral allocation

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12). The relaxed project cap is uniform on
the closed epsilon interval; it is not the smaller limiting decimal in the paper's numerical
table.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

theorem sectionSixI5FixedOuter_integral_lt_D993 :
    (∫ z in sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real),
      sectionSixFirstLowCentralSmallQuadrupleKernel z) <
        (5558 / 100000 : Real) :=
  sectionSixFirstLowCentralSmallI5D918_outer_integral_lt_5558_of_replay_caps
    sectionSixP0Target_integral_lt_D973 sectionSixP2Target_integral_lt_D992

theorem sectionSixI5Integral_lt_D993 {epsilon : Real}
    (hepsilonNonneg : 0 <= epsilon)
    (hepsilonUpper : epsilon <= 1 / 1000000) :
    sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon <
      (5558 / 100000 : Real) :=
  (sectionSixFirstLowCentralSmallQuadrupleIntegral_le_fixed_outer
    hepsilonNonneg hepsilonUpper).trans_lt sectionSixI5FixedOuter_integral_lt_D993

end PrimesRestrictedDigits
