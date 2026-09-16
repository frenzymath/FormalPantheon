import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceJointLedger
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceProfileShell

/-!
# Source-normalized recurrence targets

This module defines the source profile targets and drops the nonnegative top-coordinate model
term from the joint ledger. It does not prove the inner source hypotheses.
-/

namespace PrimesRestrictedDigits

/-- Source-normalized upper target. -/
def dimensionOneRosserSourceUpperTarget
    (P : Finset Nat) (D : Real) (R : Nat) (level z s : Real) : Prop :=
  upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z R <
    sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
      (dimensionOneRosserModelPlusPartialSum R s +
        D * dimensionOneRosserSourcePlusProfile (Real.log level) s)

/-- Source-normalized lower target. -/
def dimensionOneRosserSourceLowerTarget
    (P : Finset Nat) (D : Real) (R : Nat) (level z s : Real) : Prop :=
  lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z R <
    sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
      (dimensionOneRosserModelMinusPartialSum R s +
        D * dimensionOneRosserSourceMinusProfile (Real.log level) s)

private theorem sourceTarget_profile_nonneg_plus
    {L s : Real} (hL : 0 < L) (hs : 0 < s) :
    0 <= dimensionOneRosserSourcePlusProfile L s := by
  unfold dimensionOneRosserSourcePlusProfile
  exact mul_nonneg (Real.rpow_pos_of_pos hL _).le
    (dimensionOneRosserPlusArtificialAux_pos hL hs).le

private theorem sourceTarget_profile_nonneg_minus
    {L s : Real} (hL : 0 < L) (hs : 0 < s) :
    0 <= dimensionOneRosserSourceMinusProfile L s := by
  unfold dimensionOneRosserSourceMinusProfile
  exact mul_nonneg (Real.rpow_pos_of_pos hL _).le
    (dimensionOneRosserMinusArtificialAux_pos hL hs).le

private theorem sourceTarget_coefficient_le_one
    {s0 : Real} (hs0 : 1 <= s0) :
    0 <= 1 - 1 / (2 * s0) ∧ 1 - 1 / (2 * s0) <= (1 : Real) := by
  have hs0Pos : 0 < s0 := by linarith
  have hdiv : 1 / (2 * s0) <= (1 : Real) := by
    apply (div_le_one (by positivity)).2
    linarith
  have hnonneg : 0 <= 1 / (2 * s0) := by positivity
  constructor <;> linarith

/--
Convert a plus ledger and its exact shell inequality to the source upper target.
-/
theorem dimensionOneRosserSourceUpperTarget_of_jointLedger
    (P : Finset Nat) (R : Nat) {D level z s s0 : Real}
    (hD : 0 <= D) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (_hz : 2 <= z)
    (_hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hs0 : 1 <= s0)
    (hshell :
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z R <=
        upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
          D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z)
    (hledger :
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R +
        dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusPartialSum R s -
            dimensionOneRosserModelPlusPartialSum R s0 +
          D * (1 - 1 / (2 * s0)) *
            dimensionOneRosserSourcePlusProfile (Real.log level) s)) :
    dimensionOneRosserSourceUpperTarget P D R level z s := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hscale : 0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg hV.le hsPos.le
  have hprofile := sourceTarget_profile_nonneg_plus hL hsPos
  have hmodel0 : 0 <= dimensionOneRosserModelPlusPartialSum R s0 :=
    dimensionOneRosserModelPlusPartialSum_nonneg R s0
  rcases sourceTarget_coefficient_le_one hs0 with ⟨hcoeff, hcoeffLe⟩
  have hterm := mul_le_mul_of_nonneg_left hcoeffLe hD
  have hterm' := mul_le_mul_of_nonneg_right hterm hprofile
  have hinner :
      dimensionOneRosserModelPlusPartialSum R s -
          dimensionOneRosserModelPlusPartialSum R s0 +
        D * (1 - 1 / (2 * s0)) *
          dimensionOneRosserSourcePlusProfile (Real.log level) s <=
      dimensionOneRosserModelPlusPartialSum R s +
        D * dimensionOneRosserSourcePlusProfile (Real.log level) s := by
    nlinarith [hmodel0, hterm']
  unfold dimensionOneRosserSourceUpperTarget
  exact hshell.trans_lt (hledger.trans_le
    (mul_le_mul_of_nonneg_left hinner hscale))

/--
Convert a minus ledger and its exact shell inequality to the source lower target.
-/
theorem dimensionOneRosserSourceLowerTarget_of_jointLedger
    (P : Finset Nat) (R : Nat) {D level z s s0 : Real}
    (hD : 0 <= D) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (_hz : 2 <= z)
    (_hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hs0 : 1 <= s0)
    (hshell :
      lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z (R + 1) <=
        lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) (R + 1) +
          dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
          D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z)
    (hledger :
      lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) (R + 1) +
        dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelMinusPartialSum (R + 1) s -
            dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
          D * (1 - 1 / (2 * s0)) *
            dimensionOneRosserSourceMinusProfile (Real.log level) s)) :
    dimensionOneRosserSourceLowerTarget P D (R + 1) level z s := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hscale : 0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg hV.le hsPos.le
  have hprofile := sourceTarget_profile_nonneg_minus hL hsPos
  have hmodel0 : 0 <=
      dimensionOneRosserModelMinusPartialSum (R + 1) s0 :=
    dimensionOneRosserModelMinusPartialSum_nonneg (R + 1) s0
  rcases sourceTarget_coefficient_le_one hs0 with ⟨hcoeff, hcoeffLe⟩
  have hterm := mul_le_mul_of_nonneg_left hcoeffLe hD
  have hterm' := mul_le_mul_of_nonneg_right hterm hprofile
  have hinner :
      dimensionOneRosserModelMinusPartialSum (R + 1) s -
          dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
        D * (1 - 1 / (2 * s0)) *
          dimensionOneRosserSourceMinusProfile (Real.log level) s <=
      dimensionOneRosserModelMinusPartialSum (R + 1) s +
        D * dimensionOneRosserSourceMinusProfile (Real.log level) s := by
    nlinarith [hmodel0, hterm']
  unfold dimensionOneRosserSourceLowerTarget
  exact hshell.trans_lt (hledger.trans_le
    (mul_le_mul_of_nonneg_left hinner hscale))

end PrimesRestrictedDigits
