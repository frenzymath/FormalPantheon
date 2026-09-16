import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2TransformedKernel
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2TransformedImageEquality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# P2 domain positivity and argument guards

This module records exact fixed-delta consequences of the P2 transformed domain. It makes no
Buchstab estimate, integral estimate, Jacobian, Fubini/Tonelli, or cap claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false

open Set
namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P2Argument
    (z : SectionSixAffineT) : Real :=
  (1 - sectionSixThetaTwo (1 / 1000000 : Real) -
      2 * z.1.1.1 - z.1.1.2 - z.1.2 - z.2) /
    (z.1.1.1 + z.2)

theorem p2_domain_denominator_pos {z : SectionSixAffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P2Domain) :
    0 < sectionSixThetaTwo (1 / 1000000 : Real) - z.1.1.1 ∧
      0 < z.1.1.1 + z.2 ∧
      0 < (sectionSixThetaTwo (1 / 1000000 : Real) - z.1.1.1) *
        (z.1.1.1 + z.1.1.2) * (z.1.1.1 + z.1.2) *
          (z.1.1.1 + z.2) ^ (2 : Nat) := by
  change sectionSixThetaGap (1 / 1000000 : Real) ≤ z.1.1.1 ∧
      z.1.1.1 < sectionSixThetaOne (1 / 1000000 : Real) / 2 ∧
      0 < z.1.1.2 ∧ 0 < z.2 ∧ z.2 ≤ z.1.2 ∧
      z.1.2 ≤ z.1.1.2 ∧ _ at hz
  rcases hz with ⟨hd, hdHalf, hr, hq, hqs, hsr, hlow, hsq, hcap⟩
  have hg : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hAβ : sectionSixThetaOne (1 / 1000000 : Real) <
      sectionSixThetaTwo (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaOne, sectionSixThetaTwo]
  have hbetaD : 0 < sectionSixThetaTwo (1 / 1000000 : Real) - z.1.1.1 := by
    have hdA : z.1.1.1 < sectionSixThetaOne (1 / 1000000 : Real) := by
      linarith [hdHalf]
    linarith
  have hdq : 0 < z.1.1.1 + z.2 := by linarith [hg, hd, hq]
  have hdr : 0 < z.1.1.1 + z.1.1.2 := by linarith [hg, hd, hr]
  have hds : 0 < z.1.1.1 + z.1.2 := by
    have hs : 0 < z.1.2 := lt_of_lt_of_le hq hqs
    linarith [hg, hd]
  refine ⟨hbetaD, hdq, ?_⟩
  positivity

theorem p2_domain_argument_eq_physical {z : SectionSixAffineT}
    (_hz : z ∈ sectionSixFirstLowCentralSmallI5P2Domain) :
    sectionSixFirstLowCentralSmallI5P2Argument z =
      (1 - (sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) z).1.1.1 -
        (sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) z).1.1.2 -
        (sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) z).1.2 -
        (sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) z).2) /
        (sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) z).2 := by
  simp [sectionSixFirstLowCentralSmallI5P2Argument, sectionSixP2Phi]
  ring

theorem p2_domain_argument_range {z : SectionSixAffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P2Domain) :
    1 ≤ sectionSixFirstLowCentralSmallI5P2Argument z ∧
      sectionSixFirstLowCentralSmallI5P2Argument z < 7 := by
  have htarget : sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) z ∈
      sectionSixFirstLowCentralSmallI5P2Target := by
    rw [← sectionSixFirstLowCentralSmallI5P2Phi_image_eq_target]
    exact ⟨z, hz, rfl⟩
  have hrange := sectionSixFirstLowCentralSmallI5P2_argument_range
    htarget.1 htarget.2
  rw [p2_domain_argument_eq_physical hz]
  exact hrange

theorem p2_domain_argument_ge_sharp_iff {z : SectionSixAffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P2Domain) :
    (25 / 8 : Real) ≤ sectionSixFirstLowCentralSmallI5P2Argument z ↔
      z.2 ≤
        (8 * (1 - sectionSixThetaTwo (1 / 1000000 : Real)) -
          41 * z.1.1.1 - 8 * z.1.1.2 - 8 * z.1.2) / 33 := by
  have hden := (p2_domain_denominator_pos hz).2.1
  have h33 : (0 : Real) < 33 := by norm_num
  constructor
  · intro h
    have h' : (25 / 8 : Real) * (z.1.1.1 + z.2) ≤
        1 - sectionSixThetaTwo (1 / 1000000 : Real) -
          2 * z.1.1.1 - z.1.1.2 - z.1.2 - z.2 := by
      apply (le_div_iff₀ hden).mp
      simpa [sectionSixFirstLowCentralSmallI5P2Argument] using h
    apply (le_div_iff₀ h33).2
    nlinarith
  · intro h
    have h' : (33 : Real) * z.2 ≤
        8 * (1 - sectionSixThetaTwo (1 / 1000000 : Real)) -
          41 * z.1.1.1 - 8 * z.1.1.2 - 8 * z.1.2 := by
      simpa [mul_comm] using (le_div_iff₀ h33).mp h
    apply (le_div_iff₀ hden).2
    nlinarith [h']

end
end PrimesRestrictedDigits
