import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI5UniformCapD993
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6FixedDeltaIntegralCapD1011
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIReduction
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowFarIntegralBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalIntegralBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowIntegralBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveIntegralBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarIntegralBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralLargeIntegralBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9IntegralBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Closed positive reserve for the nine Section 6 losses

The actual I5 and I6 certificates discharge both central-small estimates. All nine source
losses remain, with a strict absolute positive reserve. Source: `MAYNARD-PRD-PUBLISHED`,
Section 6, p.146, after Eqs. (6.7)--(6.16).
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace PrimesRestrictedDigits

theorem sectionSixFirstIntegralSum_lt_D1012 {epsilon : Real}
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonUpper : epsilon ≤ 1 / 1000000000) :
    sectionSixFirstLowFarIntegral epsilon +
        sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
      sectionSixFirstLowCentralLargeBelowIntegral epsilon +
        sectionSixFirstLowCentralLargeAboveIntegral epsilon +
      sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
        sectionSixFirstLowBelowQuadrupleIntegral epsilon +
      sectionSixFirstHighFarIntegral epsilon +
        sectionSixFirstHighCentralLargeIntegral epsilon +
      sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon <
        (99968241 / 100000000 : Real) := by
  have hdelta : epsilon ≤ 1 / 1000000 := hepsilonUpper.trans (by norm_num)
  have hI1 := sectionSixFirstLowFarIntegral_lt hdelta
  have hI2 := sectionSixFirstLowCentralLargeTerminalIntegral_lt hdelta
  have hI3 := sectionSixFirstLowCentralLargeBelowIntegral_lt hdelta
  have hI4 := sectionSixFirstLowCentralLargeAboveIntegral_lt hdelta
  have hI5 := sectionSixI5Integral_lt_D993 hepsilonNonneg hdelta
  have hI6 := sectionSixFirstLowBelowQuadrupleIntegral_lt_D1011 hdelta
  have hI7 := sectionSixFirstHighFarIntegral_lt_exact hdelta
  have hI8 := sectionSixFirstHighCentralLargeIntegral_lt hepsilonUpper
  have hI9 := sectionSixFirstHighCentralSmallQuadrupleIntegral_lt
    hepsilonNonneg hepsilonUpper
  linarith

theorem exists_sectionSixFirstIntegralSum_lt_one_D1012 :
    ∃ epsilon : Real, 0 < epsilon ∧ epsilon ≤ 1 / 64 ∧
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) ≤ 1 ∧
      sectionSixFirstLowFarIntegral epsilon +
          sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
        sectionSixFirstLowCentralLargeBelowIntegral epsilon +
          sectionSixFirstLowCentralLargeAboveIntegral epsilon +
        sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
          sectionSixFirstLowBelowQuadrupleIntegral epsilon +
        sectionSixFirstHighFarIntegral epsilon +
          sectionSixFirstHighCentralLargeIntegral epsilon +
        sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon < 1 := by
  let eta : Real := 4 * (1 / 1000000000 : Real) ^ (4 : Nat)
  have heta : 0 < eta := by
    dsimp [eta]
    norm_num
  obtain ⟨epsilon, hepsilonPos, hepsilon64, hrosser, hfourth⟩ :=
    exists_admissibleFundamentalEpsilon_le_etaQuarter eta heta
  have hetaExpanded : eta / 4 = (1 / 1000000000 : Real) ^ (4 : Nat) := by
    dsimp [eta]
    ring
  have hfourth' : epsilon ^ (4 : Nat) ≤ (1 / 1000000000 : Real) ^ (4 : Nat) := by
    rw [← hetaExpanded]
    exact hfourth
  have hepsilonSmall : epsilon ≤ 1 / 1000000000 :=
    le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hfourth'
  exact ⟨epsilon, hepsilonPos, hepsilon64, hrosser,
    (sectionSixFirstIntegralSum_lt_D1012 hepsilonPos.le hepsilonSmall).trans
      (by norm_num)⟩

end PrimesRestrictedDigits
