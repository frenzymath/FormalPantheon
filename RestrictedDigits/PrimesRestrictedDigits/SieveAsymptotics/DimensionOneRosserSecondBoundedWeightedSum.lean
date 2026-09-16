import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondWeightedSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondBoundedIntegral
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondBoundedWeight

/-!
# Source-domain second weighted Rosser sums

This file assembles the natural-domain second-weight estimates from the bounded integral and
weight continuations.
-/

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace PrimesRestrictedDigits

/-- Lemma 21 for the target-plus second sum on its full source domain. -/
theorem dimensionOneRosserPlusSecondRelaxedPrimeSum_le_of_ratio_sourceDomain
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= Real.log level)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hRatio : forall u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserPlusSecondRelaxedPrimeSum P level s0 z <=
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        ((∫ t in s..s0,
            dimensionOneRosserPlusSecondKernel (Real.log level) t / t) +
          (2 * K * s0 / Real.log level) *
            dimensionOneRosserPlusSecondKernel (Real.log level) s) := by
  rcases dimensionOneRosserPlusSecondWeight_properties_sourceDomain
    hlevel hz hs hsLower hss0 hsplice hcap hgrowth with
      ⟨hB0, hBcont, hBmono⟩
  unfold dimensionOneRosserPlusSecondRelaxedPrimeSum
  apply dimensionOneRosserSecondRelaxedPrimeSum_le_of_properties P
    (dimensionOneRosserPlusSecondWeight level)
    dimensionOneRosserPlusSecondKernel hK hprime hlevel hz hs
      (by linarith) hss0 hcutoff hRatio hB0 hBcont hBmono
    (integral_dimensionOneRosserPlusSecondWeight_div_eq_of_two_le
      hlevel hz hs (by linarith) hss0)
  unfold dimensionOneRosserPlusSecondWeight
  rw [buchstabArgument_eq_sub_one_of_log_ratio hs]
  ring_nf

/-- Lemma 21 for the target-minus second sum on its full source domain. -/
theorem dimensionOneRosserMinusSecondRelaxedPrimeSum_le_of_ratio_sourceDomain
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= Real.log level)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hRatio : forall u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserMinusSecondRelaxedPrimeSum P level s0 z <=
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        ((∫ t in s..s0,
            dimensionOneRosserMinusSecondKernel (Real.log level) t / t) +
          (2 * K * s0 / Real.log level) *
            dimensionOneRosserMinusSecondKernel (Real.log level) s) := by
  rcases dimensionOneRosserMinusSecondWeight_properties_sourceDomain
    hlevel hz hs hsLower hss0 hsplice hcap hgrowth with
      ⟨hB0, hBcont, hBmono⟩
  unfold dimensionOneRosserMinusSecondRelaxedPrimeSum
  apply dimensionOneRosserSecondRelaxedPrimeSum_le_of_properties P
    (dimensionOneRosserMinusSecondWeight level)
    dimensionOneRosserMinusSecondKernel hK hprime hlevel hz hs
      hsLower hss0 hcutoff hRatio hB0 hBcont hBmono
    (integral_dimensionOneRosserMinusSecondWeight_div_eq_of_two_le
      hlevel hz hs hsLower hss0)
  unfold dimensionOneRosserMinusSecondWeight
  rw [buchstabArgument_eq_sub_one_of_log_ratio hs]
  ring_nf

/-- Restricted Eq. (8.10) inserted into the target-plus relaxed sum. -/
theorem dimensionOneRosserPlusSecondRelaxedPrimeSum_lt_of_ratio_sourceDomain
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= Real.log level)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hRatio : forall u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserPlusSecondRelaxedPrimeSum P level s0 z <
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        ((1 - 1 / s0) ^ (2 / 3 : Real) *
            (1 + s ^ 50 / Real.log level) ^ s *
              dimensionOneDelayScaledPlus s +
          (2 * K * s0 / Real.log level) *
            dimensionOneRosserPlusSecondKernel (Real.log level) s) := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hle := dimensionOneRosserPlusSecondRelaxedPrimeSum_le_of_ratio_sourceDomain
    P hK hprime hlevel hz hs hsLower hss0 hcutoff hsplice hcap hgrowth hRatio
  have hint := integral_dimensionOneRosserPlusSecondKernel_div_lt_sourceDomain
    hsLower hss0 hsplice hcap hgrowth
  apply hle.trans_lt
  apply mul_lt_mul_of_pos_left _
    (mul_pos (div_pos hV hsPos) (Real.rpow_pos_of_pos hL _))
  simpa only [add_comm] using add_lt_add_right hint
    ((2 * K * s0 / Real.log level) *
      dimensionOneRosserPlusSecondKernel (Real.log level) s)

/-- Restricted Eq. (8.10) inserted into the target-minus relaxed sum. -/
theorem dimensionOneRosserMinusSecondRelaxedPrimeSum_lt_of_ratio_sourceDomain
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= Real.log level)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hRatio : forall u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserMinusSecondRelaxedPrimeSum P level s0 z <
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        ((1 - 1 / s0) ^ (2 / 3 : Real) *
            (1 + s ^ 50 / Real.log level) ^ s *
              dimensionOneDelayScaledMinus s +
          (2 * K * s0 / Real.log level) *
            dimensionOneRosserMinusSecondKernel (Real.log level) s) := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hle := dimensionOneRosserMinusSecondRelaxedPrimeSum_le_of_ratio_sourceDomain
    P hK hprime hlevel hz hs hsLower hss0 hcutoff hsplice hcap hgrowth hRatio
  have hint := integral_dimensionOneRosserMinusSecondKernel_div_lt_sourceDomain
    hsLower hss0 hsplice hcap hgrowth
  apply hle.trans_lt
  apply mul_lt_mul_of_pos_left _
    (mul_pos (div_pos hV hsPos) (Real.rpow_pos_of_pos hL _))
  simpa only [add_comm] using add_lt_add_right hint
    ((2 * K * s0 / Real.log level) *
      dimensionOneRosserMinusSecondKernel (Real.log level) s)

/-- The literal target-plus second sum on its full source domain. -/
theorem dimensionOneRosserPlusSecondRawPrimeSum_lt_of_ratio_sourceDomain
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= Real.log level)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hRatio : forall u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        ((1 - 1 / s0) ^ (2 / 3 : Real) *
            (1 + s ^ 50 / Real.log level) ^ s *
              dimensionOneDelayScaledPlus s +
          (2 * K * s0 / Real.log level) *
            dimensionOneRosserPlusSecondKernel (Real.log level) s) := by
  exact (dimensionOneRosserPlusSecondRawPrimeSum_le_relaxed_of_two_le P hprime
    hlevel hz hs (by linarith) hcutoff).trans_lt
      (dimensionOneRosserPlusSecondRelaxedPrimeSum_lt_of_ratio_sourceDomain P
        hK hprime hlevel hz hs hsLower hss0 hcutoff hsplice hcap hgrowth hRatio)

/-- The literal target-minus second sum on its full source domain. -/
theorem dimensionOneRosserMinusSecondRawPrimeSum_lt_of_ratio_sourceDomain
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= Real.log level)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hRatio : forall u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        ((1 - 1 / s0) ^ (2 / 3 : Real) *
            (1 + s ^ 50 / Real.log level) ^ s *
              dimensionOneDelayScaledMinus s +
          (2 * K * s0 / Real.log level) *
            dimensionOneRosserMinusSecondKernel (Real.log level) s) := by
  exact (dimensionOneRosserMinusSecondRawPrimeSum_le_relaxed_of_two_le P hprime
    hlevel hz hs hsLower hcutoff).trans_lt
      (dimensionOneRosserMinusSecondRelaxedPrimeSum_lt_of_ratio_sourceDomain P
        hK hprime hlevel hz hs hsLower hss0 hcutoff hsplice hcap hgrowth hRatio)

end PrimesRestrictedDigits
