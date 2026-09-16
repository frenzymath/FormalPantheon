import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondBoundedWeightedSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondEndpoint

/-!
# Source-domain absorption of the second Rosser endpoint

This file absorbs the explicit endpoint terms in the natural-domain second weighted estimates.
-/

namespace PrimesRestrictedDigits

private theorem secondRawPrimeSum_lt_absorbed_sourceDomain
    {raw scale main endpoint artificial profile error coefficient : Real}
    (hraw : raw < scale * (main * artificial * profile + endpoint))
    (hscale : 0 <= scale) (hartificialProfile : 0 <= artificial * profile)
    (hendpoint : endpoint <= error * artificial * profile)
    (hcoefficient : main + error <= coefficient) :
    raw < scale * (coefficient * artificial * profile) := by
  apply hraw.trans_le
  apply mul_le_mul_of_nonneg_left _ hscale
  calc
    main * artificial * profile + endpoint <=
        main * artificial * profile + error * artificial * profile :=
      add_le_add le_rfl hendpoint
    _ = (main + error) * (artificial * profile) := by ring
    _ <= coefficient * (artificial * profile) :=
      mul_le_mul_of_nonneg_right hcoefficient hartificialProfile
    _ = coefficient * artificial * profile := by ring

/-- The target-plus raw second sum after source-domain endpoint absorption. -/
theorem dimensionOneRosserPlusSecondRawPrimeSum_lt_absorbed_of_ratio_sourceDomain
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= Real.log level)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= s0 ^ 46)
    (hRatio : forall u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        ((1 - 1 / (2 * s0)) *
          (1 + s ^ 50 / Real.log level) ^ s *
            dimensionOneDelayScaledPlus s) := by
  have hsPos : 0 < s := by linarith
  have hs0One : 1 <= s0 := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hscale : 0 <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (Real.log level) ^ (-1 / 3 : Real) :=
    mul_nonneg (div_nonneg hV.le hsPos.le)
      (Real.rpow_pos_of_pos hL _).le
  have hA : 0 <= (1 + s ^ 50 / Real.log level) ^ s := by
    apply Real.rpow_nonneg
    positivity
  have hscaled : 0 <= dimensionOneDelayScaledPlus s := by
    rw [<- sq_mul_dimensionOneDelayQPlus hsPos.ne']
    exact mul_nonneg (sq_nonneg _) (dimensionOneDelayQPlus_pos hsPos).le
  exact secondRawPrimeSum_lt_absorbed_sourceDomain
    (dimensionOneRosserPlusSecondRawPrimeSum_lt_of_ratio_sourceDomain P hK
      hprime hlevel hz hs hsLower hss0 hcutoff hsplice hcap hgrowth hRatio)
    hscale (mul_nonneg hA hscaled)
    (dimensionOneRosserPlusSecondEndpoint_le hK (by linarith) hss0 hcap)
    (dimensionOneRosserSecondCoefficient_contraction hs0One hdom)

/-- The target-minus raw second sum after source-domain endpoint absorption. -/
theorem dimensionOneRosserMinusSecondRawPrimeSum_lt_absorbed_of_ratio_sourceDomain
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= Real.log level)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= s0 ^ 46)
    (hRatio : forall u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        ((1 - 1 / (2 * s0)) *
          (1 + s ^ 50 / Real.log level) ^ s *
            dimensionOneDelayScaledMinus s) := by
  have hsPos : 0 < s := by linarith
  have hs0One : 1 <= s0 := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hscale : 0 <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (Real.log level) ^ (-1 / 3 : Real) :=
    mul_nonneg (div_nonneg hV.le hsPos.le)
      (Real.rpow_pos_of_pos hL _).le
  have hA : 0 <= (1 + s ^ 50 / Real.log level) ^ s := by
    apply Real.rpow_nonneg
    positivity
  have hscaled : 0 <= dimensionOneDelayScaledMinus s := by
    rw [<- sq_mul_dimensionOneDelayQMinus hsPos.ne']
    exact mul_nonneg (sq_nonneg _) (dimensionOneDelayQMinus_pos hsPos).le
  exact secondRawPrimeSum_lt_absorbed_sourceDomain
    (dimensionOneRosserMinusSecondRawPrimeSum_lt_of_ratio_sourceDomain P hK
      hprime hlevel hz hs hsLower hss0 hcutoff hsplice hcap hgrowth hRatio)
    hscale (mul_nonneg hA hscaled)
    (dimensionOneRosserMinusSecondEndpoint_le hK hsLower hss0 hcap)
    (dimensionOneRosserSecondCoefficient_contraction hs0One hdom)

end PrimesRestrictedDigits
