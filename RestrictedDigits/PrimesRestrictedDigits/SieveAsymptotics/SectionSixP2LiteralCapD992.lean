import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ExactForestD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2IntegratedProfileTransportD991

/-!
# The literal P2 integral allocation

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12). Compose the closed exact forest cap
with the existing native-profile transport.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

theorem sectionSixP2Target_integral_lt_D992 :
    (∫ z in sectionSixFirstLowCentralSmallI5PairPatternTarget (2 : Fin 4),
      sectionSixFirstLowCentralSmallQuadrupleKernel z) <
        (1427 / 50000 : Real) :=
  sectionSixP2Target_integral_le_nativeProfile_D991.trans_lt
    sectionSixP2Profile_integral_lt_D990

end PrimesRestrictedDigits
