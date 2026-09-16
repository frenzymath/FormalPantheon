import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceFixedSpliceWeight
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceFixedSpliceIntegral
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondWeightedSum

/-!
# Source fixed-splice weighted second sums

This file applies Lemma 21 using full source weight regularity and then inserts strict
fixed-splice integral.
-/

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace PrimesRestrictedDigits

/-- Full-range source Lemma 21 bound for the target-plus second sum. -/
theorem dimensionOneRosserSourcePlusSecondRelaxedPrimeSum_le_fixedSplice
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
    (hRatio : ∀ u : Real,
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
  rcases dimensionOneRosserPlusSecondWeight_properties_sourceCutoff
    hlevel hz hs hsLower hss0 hsource hLExp hgate hgrowth with
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

/-- Full-range source Lemma 21 bound for the target-minus second sum. -/
theorem dimensionOneRosserSourceMinusSecondRelaxedPrimeSum_le_fixedSplice
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
    (hRatio : ∀ u : Real,
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
  rcases dimensionOneRosserMinusSecondWeight_properties_sourceCutoff
    hlevel hz hs hsLower hss0 hsource hLExp hgate hgrowth with
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

/-- Full-range strict pre-endpoint source bound for the target-plus sum. -/
theorem dimensionOneRosserSourcePlusSecondRelaxedPrimeSum_lt_fixedSplice
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
    (hRatio : ∀ u : Real,
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
  have hle :=
    dimensionOneRosserSourcePlusSecondRelaxedPrimeSum_le_fixedSplice
      P hK hprime hlevel hz hs hsLower hss0 hcutoff hsource hLExp hgate
        hgrowth hRatio
  have hsTwo : 2 <= s := by linarith
  have hsplice := dimensionOneRosserSourceSplice_twice_le hsTwo hss0
    hsource hLExp hgate hgrowth
  have hint := integral_dimensionOneRosserPlusSecondKernel_div_lt_sourceCutoff
    hsLower hss0 hsplice (by simpa using hsource) hLExp
      (by simpa using hgate) hgrowth
  apply hle.trans_lt
  apply mul_lt_mul_of_pos_left _
    (mul_pos (div_pos hV hsPos) (Real.rpow_pos_of_pos hL _))
  simpa only [add_comm] using add_lt_add_right hint
    ((2 * K * s0 / Real.log level) *
      dimensionOneRosserPlusSecondKernel (Real.log level) s)

/-- Full-range strict pre-endpoint source bound for the target-minus sum. -/
theorem dimensionOneRosserSourceMinusSecondRelaxedPrimeSum_lt_fixedSplice
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
    (hRatio : ∀ u : Real,
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
  have hle :=
    dimensionOneRosserSourceMinusSecondRelaxedPrimeSum_le_fixedSplice
      P hK hprime hlevel hz hs hsLower hss0 hcutoff hsource hLExp hgate
        hgrowth hRatio
  have hsplice := dimensionOneRosserSourceSplice_twice_le hsLower hss0
    hsource hLExp hgate hgrowth
  have hint := integral_dimensionOneRosserMinusSecondKernel_div_lt_sourceCutoff
    hsLower hss0 hsplice (by simpa using hsource) hLExp
      (by simpa using hgate) hgrowth
  apply hle.trans_lt
  apply mul_lt_mul_of_pos_left _
    (mul_pos (div_pos hV hsPos) (Real.rpow_pos_of_pos hL _))
  simpa only [add_comm] using add_lt_add_right hint
    ((2 * K * s0 / Real.log level) *
      dimensionOneRosserMinusSecondKernel (Real.log level) s)

end PrimesRestrictedDigits
