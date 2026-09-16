import PrimesRestrictedDigits.SieveAsymptotics.DecimalIwaniecWeightedDensity
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondIntegral
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondLogTransform
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondRawPrimeSum

/-!
# The second weighted dimension-one Rosser recurrence term

This file applies Iwaniec's weighted density estimate to the relaxed second weights and then
inserts the restricted Eq. (8.10) integral bounds. See `IWANIEC-ROSSER-SIEVE-1980`, Eqs.
(8.10)--(8.12).
-/

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace PrimesRestrictedDigits

private theorem dimensionOneRosserSecondRelaxedPrimeSum_eq_scaled
    (P : Finset Nat) (B : Real -> Real) {level s0 z s : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsPos : 0 < s) :
    (∑ p ∈ P.filter (fun p : Nat =>
        level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
      (Real.log level) ^ (-1 / 3 : Real) * (p : Real)⁻¹ *
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
        (Real.log (p : Real) / Real.log level) * B (p : Real)) =
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        (∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
          (p : Real)⁻¹ *
            (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
              sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
            (Real.log (p : Real) / Real.log z) * B (p : Real)) := by
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogIdentity : Real.log level = s * Real.log z := by
    rw [hs]
    field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hlogIdentity]
  field_simp [hV.ne', hlogz.ne', hsPos.ne']

/-- Lemma 21 for a generic relaxed second weight on the natural recurrence
domain, after exact logarithmic normalization. -/
theorem dimensionOneRosserSecondRelaxedPrimeSum_le_of_properties
    (P : Finset Nat) (B : Real -> Real) (kernel : Real -> Real -> Real)
    {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsTwo : 2 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hRatio : forall u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u))
    (hB0 : ∀ x ∈ Icc (level ^ (1 / s0)) z, 0 <= B x)
    (hBcont : ContinuousOn B (Icc (level ^ (1 / s0)) z))
    (hBmono : MonotoneOn B (Icc (level ^ (1 / s0)) z))
    (hIntegral :
      (∫ x in (level ^ (1 / s0))..z, B x / (x * Real.log x)) =
        ∫ t in s..s0, kernel (Real.log level) t / t)
    (hBz : B z = kernel (Real.log level) s) :
    (∑ p ∈ P.filter (fun p : Nat =>
        level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
      (Real.log level) ^ (-1 / 3 : Real) * (p : Real)⁻¹ *
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
        (Real.log (p : Real) / Real.log level) * B (p : Real)) <=
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        ((∫ t in s..s0, kernel (Real.log level) t / t) +
          (2 * K * s0 / Real.log level) * kernel (Real.log level) s) := by
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hscale : 0 <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (Real.log level) ^ (-1 / 3 : Real) :=
    mul_nonneg (div_nonneg hV.le hsPos.le)
      (Real.rpow_pos_of_pos hL _).le
  have hcutoffz : level ^ (1 / s0) < z :=
    dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 hsTwo
  have hWeighted := iwaniecWeightedDensitySum_le_of_ratio
    P B hK hprime hcutoff hcutoffz hRatio hBcont hBmono hB0
  have hScaled := mul_le_mul_of_nonneg_left hWeighted hscale
  rw [← dimensionOneRosserSecondRelaxedPrimeSum_eq_scaled
    P B hprime hz hs hsPos, hIntegral, hBz,
    log_rpow_one_div (by linarith)] at hScaled
  have hendpoint :
      2 * K * kernel (Real.log level) s / (Real.log level / s0) =
        (2 * K * s0 / Real.log level) * kernel (Real.log level) s := by
    field_simp [hL.ne', hs0Pos.ne']
  rwa [hendpoint] at hScaled

/-- Lemma 21 applied to the relaxed target-plus second prime sum, with the
lower-cutoff logarithm evaluated exactly. -/
theorem dimensionOneRosserPlusSecondRelaxedPrimeSum_le_of_ratio
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
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
  have hsTwo : 2 <= s := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  rcases dimensionOneRosserPlusSecondWeight_properties
    hlevel hz hs hsLarge hss0 hcap with ⟨hB0, hBcont, hBmono⟩
  unfold dimensionOneRosserPlusSecondRelaxedPrimeSum
  apply dimensionOneRosserSecondRelaxedPrimeSum_le_of_properties P
    (dimensionOneRosserPlusSecondWeight level)
    dimensionOneRosserPlusSecondKernel hK hprime hlevel hz hs hsTwo hss0
      hcutoff hRatio hB0 hBcont hBmono
    (integral_dimensionOneRosserPlusSecondWeight_div_eq_of_two_le
      hlevel hz hs hsTwo hss0)
  unfold dimensionOneRosserPlusSecondWeight
  rw [buchstabArgument_eq_sub_one_of_log_ratio hs]
  ring_nf

/-- Lemma 21 applied to the relaxed target-minus second prime sum, with the
lower-cutoff logarithm evaluated exactly. -/
theorem dimensionOneRosserMinusSecondRelaxedPrimeSum_le_of_ratio
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
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
  have hsTwo : 2 <= s := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  rcases dimensionOneRosserMinusSecondWeight_properties
    hlevel hz hs hsLarge hss0 hcap with ⟨hB0, hBcont, hBmono⟩
  unfold dimensionOneRosserMinusSecondRelaxedPrimeSum
  apply dimensionOneRosserSecondRelaxedPrimeSum_le_of_properties P
    (dimensionOneRosserMinusSecondWeight level)
    dimensionOneRosserMinusSecondKernel hK hprime hlevel hz hs hsTwo hss0
      hcutoff hRatio hB0 hBcont hBmono
    (integral_dimensionOneRosserMinusSecondWeight_div_eq_of_two_le
      hlevel hz hs hsTwo hss0)
  unfold dimensionOneRosserMinusSecondWeight
  rw [buchstabArgument_eq_sub_one_of_log_ratio hs]
  ring_nf

/-- The target-plus relaxed sum after inserting restricted Eq. (8.10). -/
theorem dimensionOneRosserPlusSecondRelaxedPrimeSum_lt_of_ratio
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
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
  have hsPos : 0 < s := by
    nlinarith [Real.exp_pos (5000 : Real)]
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hle := dimensionOneRosserPlusSecondRelaxedPrimeSum_le_of_ratio
    P hK hprime hlevel hz hs hsLarge hss0 hcutoff hcap hRatio
  have hint := integral_dimensionOneRosserPlusSecondKernel_div_lt
    hL hsLarge hss0 hcap
  apply hle.trans_lt
  apply mul_lt_mul_of_pos_left _
    (mul_pos (div_pos hV hsPos) (Real.rpow_pos_of_pos hL _))
  simpa only [add_comm] using add_lt_add_right hint
    ((2 * K * s0 / Real.log level) *
      dimensionOneRosserPlusSecondKernel (Real.log level) s)

/-- The target-minus relaxed sum after inserting restricted Eq. (8.10). -/
theorem dimensionOneRosserMinusSecondRelaxedPrimeSum_lt_of_ratio
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
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
  have hsPos : 0 < s := by
    nlinarith [Real.exp_pos (5000 : Real)]
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hle := dimensionOneRosserMinusSecondRelaxedPrimeSum_le_of_ratio
    P hK hprime hlevel hz hs hsLarge hss0 hcutoff hcap hRatio
  have hint := integral_dimensionOneRosserMinusSecondKernel_div_lt
    hL hsLarge hss0 hcap
  apply hle.trans_lt
  apply mul_lt_mul_of_pos_left _
    (mul_pos (div_pos hV hsPos) (Real.rpow_pos_of_pos hL _))
  simpa only [add_comm] using add_lt_add_right hint
    ((2 * K * s0 / Real.log level) *
      dimensionOneRosserMinusSecondKernel (Real.log level) s)

/-- The strict pre-`O` estimate for the literal target-plus second profile.
The common induction multiplier remains outside this rank-free sum. -/
theorem dimensionOneRosserPlusSecondRawPrimeSum_lt_of_ratio
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
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
  exact (dimensionOneRosserPlusSecondRawPrimeSum_le_relaxed P hprime hlevel
    hz hs hsLarge hcutoff).trans_lt
      (dimensionOneRosserPlusSecondRelaxedPrimeSum_lt_of_ratio P hK hprime
        hlevel hz hs hsLarge hss0 hcutoff hcap hRatio)

/-- The strict pre-`O` estimate for the literal target-minus second profile.
The common induction multiplier remains outside this rank-free sum. -/
theorem dimensionOneRosserMinusSecondRawPrimeSum_lt_of_ratio
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
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
  exact (dimensionOneRosserMinusSecondRawPrimeSum_le_relaxed P hprime hlevel
    hz hs hsLarge hcutoff).trans_lt
      (dimensionOneRosserMinusSecondRelaxedPrimeSum_lt_of_ratio P hK hprime
        hlevel hz hs hsLarge hss0 hcutoff hcap hRatio)

end PrimesRestrictedDigits
