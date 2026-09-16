import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceFixedSpliceWeightedSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceRecurrenceReserve

/-!
# Source fixed-splice endpoint absorption

This file combines strict second-sum estimate, explicit endpoint, and W5's scalar reserve.
-/

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace PrimesRestrictedDigits

/-- Fully absorbed source second-sum bound for the target-plus recurrence. -/
theorem dimensionOneRosserSourcePlusSecondRelaxedPrimeSum_lt_absorbed
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsource : s0 ^ 50 = Real.log level *
      (Real.log (Real.log level)) ^ 3)
    (hLExp : Real.exp 1 <= Real.log level)
    (hgate : 124800 + 14400 * Real.log (Real.log (Real.log level)) <=
      Real.log (Real.log level))
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= (Real.log level) ^ (1 / 24 : Real))
    (hRatio : ∀ u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserPlusSecondRelaxedPrimeSum P level s0 z <
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (Real.log level) ^ (-1 / 3 : Real)) *
        ((1 - 1 / (2 * s0)) *
          (1 + s ^ 50 / Real.log level) ^ s *
            dimensionOneDelayScaledPlus s) := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hscale : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
      (Real.log level) ^ (-1 / 3 : Real) :=
    mul_pos (div_pos hV hsPos) (Real.rpow_pos_of_pos hL _)
  have hA : 0 <= (1 + s ^ 50 / Real.log level) ^ s *
      dimensionOneDelayScaledPlus s := by
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · rw [<- sq_mul_dimensionOneDelayQPlus (by linarith : s ≠ 0)]
      exact mul_nonneg (sq_nonneg _) (dimensionOneDelayQPlus_pos hsPos).le
  have hraw :=
    dimensionOneRosserSourcePlusSecondRelaxedPrimeSum_lt_fixedSplice
      P hK hprime hlevel hz hs hsLower hss0 hcutoff hsource hLExp hgate
        hgrowth hRatio
  have hend := dimensionOneRosserPlusSecondEndpoint_le_sourceCutoff
    hK hLExp (by linarith) hss0 (by simpa using hsource)
      (by simpa using hgate)
  have hreserve :
      (1 - 1 / s0) ^ (2 / 3 : Real) +
          (2304 * K) / s0 * (Real.log level) ^ (-1 / 24 : Real) <=
        1 - 1 / (2 * s0) := by
    have hLOne : 1 <= Real.log level :=
      (Real.one_le_exp (by norm_num : (0 : Real) <= 1)).trans hLExp
    have hs0One : 1 <= s0 := by linarith
    apply dimensionOneRosserSourceRecurrenceReserve_le
    · positivity
    · exact hLOne
    · exact hs0One
    · nlinarith [hdom]
  have hsum :
      (1 - 1 / s0) ^ (2 / 3 : Real) *
          (1 + s ^ 50 / Real.log level) ^ s *
            dimensionOneDelayScaledPlus s +
          (2 * K * s0 / Real.log level) *
            dimensionOneRosserPlusSecondKernel (Real.log level) s <=
        (1 - 1 / (2 * s0)) *
          (1 + s ^ 50 / Real.log level) ^ s *
            dimensionOneDelayScaledPlus s := by
    calc
      _ <= ((1 - 1 / s0) ^ (2 / 3 : Real) +
          (2304 * K / s0) * (Real.log level) ^ (-1 / 24 : Real)) *
            ((1 + s ^ 50 / Real.log level) ^ s *
              dimensionOneDelayScaledPlus s) := by
        rw [show (2304 * K / s0) * (Real.log level) ^ (-1 / 24 : Real) =
          (2304 * K) / s0 * (Real.log level) ^ (-1 / 24 : Real) by ring]
        nlinarith [hend]
      _ <= _ := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_right hreserve hA)
  exact hraw.trans_le (mul_le_mul_of_nonneg_left hsum hscale.le)

/-- Fully absorbed source second-sum bound for the target-minus recurrence. -/
theorem dimensionOneRosserSourceMinusSecondRelaxedPrimeSum_lt_absorbed
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsource : s0 ^ 50 = Real.log level *
      (Real.log (Real.log level)) ^ 3)
    (hLExp : Real.exp 1 <= Real.log level)
    (hgate : 124800 + 14400 * Real.log (Real.log (Real.log level)) <=
      Real.log (Real.log level))
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= (Real.log level) ^ (1 / 24 : Real))
    (hRatio : ∀ u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserMinusSecondRelaxedPrimeSum P level s0 z <
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (Real.log level) ^ (-1 / 3 : Real)) *
        ((1 - 1 / (2 * s0)) *
          (1 + s ^ 50 / Real.log level) ^ s *
            dimensionOneDelayScaledMinus s) := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hscale : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
      (Real.log level) ^ (-1 / 3 : Real) :=
    mul_pos (div_pos hV hsPos) (Real.rpow_pos_of_pos hL _)
  have hA : 0 <= (1 + s ^ 50 / Real.log level) ^ s *
      dimensionOneDelayScaledMinus s := by
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · rw [<- sq_mul_dimensionOneDelayQMinus (by linarith : s ≠ 0)]
      exact mul_nonneg (sq_nonneg _) (dimensionOneDelayQMinus_pos hsPos).le
  have hraw :=
    dimensionOneRosserSourceMinusSecondRelaxedPrimeSum_lt_fixedSplice
      P hK hprime hlevel hz hs hsLower hss0 hcutoff hsource hLExp hgate
        hgrowth hRatio
  have hend := dimensionOneRosserMinusSecondEndpoint_le_sourceCutoff
    hK hLExp hsLower hss0 (by simpa using hsource)
      (by simpa using hgate)
  have hreserve :
      (1 - 1 / s0) ^ (2 / 3 : Real) +
          (2304 * K) / s0 * (Real.log level) ^ (-1 / 24 : Real) <=
        1 - 1 / (2 * s0) := by
    have hLOne : 1 <= Real.log level :=
      (Real.one_le_exp (by norm_num : (0 : Real) <= 1)).trans hLExp
    have hs0One : 1 <= s0 := by linarith
    apply dimensionOneRosserSourceRecurrenceReserve_le
    · positivity
    · exact hLOne
    · exact hs0One
    · nlinarith [hdom]
  have hsum :
      (1 - 1 / s0) ^ (2 / 3 : Real) *
          (1 + s ^ 50 / Real.log level) ^ s *
            dimensionOneDelayScaledMinus s +
          (2 * K * s0 / Real.log level) *
            dimensionOneRosserMinusSecondKernel (Real.log level) s <=
        (1 - 1 / (2 * s0)) *
          (1 + s ^ 50 / Real.log level) ^ s *
            dimensionOneDelayScaledMinus s := by
    calc
      _ <= ((1 - 1 / s0) ^ (2 / 3 : Real) +
          (2304 * K / s0) * (Real.log level) ^ (-1 / 24 : Real)) *
            ((1 + s ^ 50 / Real.log level) ^ s *
              dimensionOneDelayScaledMinus s) := by
        rw [show (2304 * K / s0) * (Real.log level) ^ (-1 / 24 : Real) =
          (2304 * K) / s0 * (Real.log level) ^ (-1 / 24 : Real) by ring]
        nlinarith [hend]
      _ <= _ := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_right hreserve hA)
  exact hraw.trans_le (mul_le_mul_of_nonneg_left hsum hscale.le)

end PrimesRestrictedDigits
