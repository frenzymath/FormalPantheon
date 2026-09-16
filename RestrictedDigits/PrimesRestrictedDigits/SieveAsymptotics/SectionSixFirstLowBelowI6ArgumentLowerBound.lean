import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleRegions
import Mathlib.Tactic.Linarith

/-!
# Lower bound for the I6 Buchstab argument

For the fixed numerical parameter range, the strict `u+v` wall and the role order force the
Buchstab argument strictly above one. This is a pointwise geometry lemma only; it does not
identify the source region or bound the integral.
-/

namespace PrimesRestrictedDigits

theorem sectionSixFirstLowBelowQuadruple_argument_gt_one
    {epsilon : Real} (hepsilonUpper : epsilon <= 1 / 1000000)
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowBelowQuadrupleRegion epsilon) :
    1 < (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
  have hgap : 0 < sectionSixThetaGap epsilon := by
    simp only [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
    linarith
  have htPos : 0 < x.2 := hgap.trans hx.1
  have htheta : sectionSixThetaOne epsilon < (2 / 5 : Real) := by
    simp only [sectionSixThetaOne]
    linarith
  have hcap : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1 := by
    have htv := hx.2.1
    have hwv := hx.2.2.1
    have hvu := hx.2.2.2.1
    have huv := hx.2.2.2.2
    have hhalf : 2 * (x.1.1.1 + 4 * x.1.1.2) <=
        5 * (x.1.1.1 + x.1.1.2) := by
      linarith
    linarith
  apply (lt_div_iff₀ htPos).2
  linarith

end PrimesRestrictedDigits
