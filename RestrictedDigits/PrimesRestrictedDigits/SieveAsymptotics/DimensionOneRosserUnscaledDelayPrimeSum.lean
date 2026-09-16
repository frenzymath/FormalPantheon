import PrimesRestrictedDigits.SieveAsymptotics.DecimalIwaniecWeightedDensity
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserUnscaledDelayTail
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserUnscaledDelayWeight

/-!
# Weighted prime sums for unscaled Rosser delay transport

This file applies Iwaniec's weighted density lemma to the project-local unscaled sign-paired
delay profiles.
-/

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace PrimesRestrictedDigits

/-- The unscaled delay prime sum paired with an upper Rosser target. -/
noncomputable def dimensionOneRosserPlusUnscaledDelayPrimeSum
    (P : Finset Nat) (level u z : Real) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / u) <= (p : Real) ∧ (p : Real) < z),
    (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) *
      dimensionOneDelayScaledMinus
        (buchstabArgument level (p : Real))

/-- The unscaled delay prime sum paired with a lower Rosser target. -/
noncomputable def dimensionOneRosserMinusUnscaledDelayPrimeSum
    (P : Finset Nat) (level u z : Real) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / u) <= (p : Real) ∧ (p : Real) < z),
    (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) *
      dimensionOneDelayScaledPlus
        (buchstabArgument level (p : Real))

private theorem unscaledDelayPrimeSum_eq_scaled
    (P : Finset Nat) (F B : Real -> Real) {level u z : Real}
    (hB : ∀ x : Real,
      B x = F (buchstabArgument level x) / Real.log (level / x))
    (hprime : ∀ p ∈ P, p.Prime) (hz : 2 <= z) :
    (∑ p ∈ P.filter (fun p : Nat =>
        level ^ (1 / u) <= (p : Real) ∧ (p : Real) < z),
      (p : Real)⁻¹ *
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
        (Real.log (p : Real) / Real.log (level / (p : Real))) *
        F (buchstabArgument level (p : Real))) =
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
        (∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / u) <= (p : Real) ∧ (p : Real) < z),
          (p : Real)⁻¹ *
            (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
              sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
            (Real.log (p : Real) / Real.log z) * B (p : Real)) := by
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hB]
  field_simp [hV.ne', hlogz.ne']

private theorem unscaledDelay_log_data
    {level z s u : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsu : s < u) :
    Real.log z = Real.log level / s ∧
      Real.log (level / z) = Real.log level * (1 - 1 / s) ∧
      buchstabArgument level z = s - 1 ∧
      Real.log (level ^ (1 / u)) = Real.log level / u := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have huPos : 0 < u := hsPos.trans hsu
  have hL : Real.log level = s * Real.log z := by
    rw [hs]
    field_simp
  have hlogzEq : Real.log z = Real.log level / s := by
    rw [hL]
    field_simp
  have hlogDiv : Real.log (level / z) =
      Real.log level * (1 - 1 / s) := by
    rw [Real.log_div hlevelPos.ne' hzPos.ne', hlogzEq]
    ring
  exact ⟨hlogzEq, hlogDiv,
    buchstabArgument_eq_sub_one_of_log_ratio hs,
    log_rpow_one_div hlevelPos⟩

private theorem unscaledDelayPrimeSum_le_of_properties
    (P : Finset Nat) (F B : Real -> Real) {K level z s u : Real}
    (hB : ∀ x : Real,
      B x = F (buchstabArgument level x) / Real.log (level / x))
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u))
    (hRatio : ∀ x : Real,
      level ^ (1 / u) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x))
    (hB0 : ∀ x ∈ Icc (level ^ (1 / u)) z, 0 <= B x)
    (hBcont : ContinuousOn B (Icc (level ^ (1 / u)) z))
    (hBmono : MonotoneOn B (Icc (level ^ (1 / u)) z))
    {integralValue : Real}
    (hIntegral : Real.log level *
      (∫ x in (level ^ (1 / u))..z, B x / (x * Real.log x)) =
        integralValue) :
    (∑ p ∈ P.filter (fun p : Nat =>
        level ^ (1 / u) <= (p : Real) ∧ (p : Real) < z),
      (p : Real)⁻¹ *
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
        (Real.log (p : Real) / Real.log (level / (p : Real))) *
        F (buchstabArgument level (p : Real))) <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (integralValue +
          (2 * K * u / (Real.log level * (1 - 1 / s))) * F (s - 1)) := by
  rcases unscaledDelay_log_data hlevel hz hs hsLower hsu with
    ⟨hlogzEq, hlogDiv, hargz, hlogCutoff⟩
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have huPos : 0 < u := hsPos.trans hsu
  have hOne : 0 < 1 - 1 / s := by
    rw [sub_pos, div_lt_one hsPos]
    linarith
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hcutoffz : level ^ (1 / u) < z :=
    dimensionOneRosserFirstCutoff_lt hlevel hz hs hsu hsLower
  have hWeighted := iwaniecWeightedDensitySum_le_of_ratio
    P B hK hprime hcutoff hcutoffz hRatio hBcont hBmono hB0
  have hScaled := mul_le_mul_of_nonneg_left hWeighted
    (mul_nonneg hV.le hlogz.le)
  rw [<- unscaledDelayPrimeSum_eq_scaled P F B hB hprime hz] at hScaled
  have hIntegral' :
      (∫ x in (level ^ (1 / u))..z, B x / (x * Real.log x)) =
        integralValue / Real.log level := by
    apply (eq_div_iff hL.ne').2
    simpa only [mul_comm] using hIntegral
  have hBz : B z = F (s - 1) /
      (Real.log level * (1 - 1 / s)) := by
    rw [hB, hargz, hlogDiv]
  rw [hIntegral', hBz, hlogCutoff, hlogzEq] at hScaled
  calc
    _ <= (sieveDensityBelow P (fun q => (q : Real)⁻¹) z *
          (Real.log level / s)) *
        (integralValue / Real.log level +
          2 * K *
            (F (s - 1) /
              (Real.log level * (1 - 1 / s))) /
            (Real.log level / u)) := hScaled
    _ = _ := by
      field_simp [hL.ne', hsPos.ne', huPos.ne', hOne.ne']

/-- Lemma 21 for the upper-target unscaled delay prime sum. -/
theorem dimensionOneRosserPlusUnscaledDelayPrimeSum_le_of_ratio
    (P : Finset Nat) {K level z s u : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u))
    (hRatio : ∀ x : Real,
      level ^ (1 / u) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    dimensionOneRosserPlusUnscaledDelayPrimeSum P level u z <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        ((∫ t in s..u,
            dimensionOneDelayScaledMinus (t - 1) / (t - 1)) +
          (2 * K * u / (Real.log level * (1 - 1 / s))) *
            dimensionOneDelayScaledMinus (s - 1)) := by
  rcases dimensionOneRosserPlusUnscaledDelayWeight_properties hlevel hz hs
    hsLower hsu hcutoff with ⟨hB0, hBcont, hBmono⟩
  unfold dimensionOneRosserPlusUnscaledDelayPrimeSum
  exact unscaledDelayPrimeSum_le_of_properties P dimensionOneDelayScaledMinus
    (dimensionOneRosserPlusUnscaledDelayWeight level)
    (fun x => rfl) hK hprime hlevel hz hs (by linarith) hsu hcutoff hRatio
    hB0 hBcont hBmono
    (log_mul_integral_dimensionOneRosserPlusUnscaledDelayWeight_eq
      hlevel hz hs hsLower hsu hcutoff)

/-- Lemma 21 for the lower-target unscaled delay prime sum. -/
theorem dimensionOneRosserMinusUnscaledDelayPrimeSum_le_of_ratio
    (P : Finset Nat) {K level z s u : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u))
    (hRatio : ∀ x : Real,
      level ^ (1 / u) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    dimensionOneRosserMinusUnscaledDelayPrimeSum P level u z <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        ((∫ t in s..u,
            dimensionOneDelayScaledPlus (t - 1) / (t - 1)) +
          (2 * K * u / (Real.log level * (1 - 1 / s))) *
            dimensionOneDelayScaledPlus (s - 1)) := by
  rcases dimensionOneRosserMinusUnscaledDelayWeight_properties hlevel hz hs
    hsLower hsu hcutoff with ⟨hB0, hBcont, hBmono⟩
  unfold dimensionOneRosserMinusUnscaledDelayPrimeSum
  exact unscaledDelayPrimeSum_le_of_properties P dimensionOneDelayScaledPlus
    (dimensionOneRosserMinusUnscaledDelayWeight level)
    (fun x => rfl) hK hprime hlevel hz hs hsLower hsu hcutoff hRatio
    hB0 hBcont hBmono
    (log_mul_integral_dimensionOneRosserMinusUnscaledDelayWeight_eq
      hlevel hz hs hsLower hsu hcutoff)

/-- Contracted-difference form of the upper-target unscaled delay prime-sum
bound. -/
theorem dimensionOneRosserPlusUnscaledDelayPrimeSum_le_contractedDifference_of_ratio
    (P : Finset Nat) {K level z s u : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u))
    (hRatio : ∀ x : Real,
      level ^ (1 / u) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    dimensionOneRosserPlusUnscaledDelayPrimeSum P level u z <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        ((1 - 1 / u) *
            (dimensionOneDelayScaledPlus s - dimensionOneDelayScaledPlus u) +
          (2 * K * u / (Real.log level * (1 - 1 / s))) *
            dimensionOneDelayScaledMinus (s - 1)) := by
  have hraw := dimensionOneRosserPlusUnscaledDelayPrimeSum_le_of_ratio
    P hK hprime hlevel hz hs hsLower hsu hcutoff hRatio
  have htail :=
    integral_dimensionOneRosserPlusUnscaledDelay_le_endpointFactor_mul_sub
      hsLower hsu.le
  have hscale : 0 <= sieveDensityBelow P
      (fun q => (q : Real)⁻¹) z / s := by
    exact div_nonneg
      (sieveDensityBelow_reciprocal_pos P z hprime).le (by linarith)
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (add_le_add htail le_rfl) hscale)

/-- Contracted-difference form of the lower-target unscaled delay prime-sum
bound. -/
theorem dimensionOneRosserMinusUnscaledDelayPrimeSum_le_contractedDifference_of_ratio
    (P : Finset Nat) {K level z s u : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u))
    (hRatio : ∀ x : Real,
      level ^ (1 / u) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    dimensionOneRosserMinusUnscaledDelayPrimeSum P level u z <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        ((1 - 1 / u) *
            (dimensionOneDelayScaledMinus s - dimensionOneDelayScaledMinus u) +
          (2 * K * u / (Real.log level * (1 - 1 / s))) *
            dimensionOneDelayScaledPlus (s - 1)) := by
  have hraw := dimensionOneRosserMinusUnscaledDelayPrimeSum_le_of_ratio
    P hK hprime hlevel hz hs hsLower hsu hcutoff hRatio
  have htail :=
    integral_dimensionOneRosserMinusUnscaledDelay_le_endpointFactor_mul_sub
      hsLower hsu.le
  have hscale : 0 <= sieveDensityBelow P
      (fun q => (q : Real)⁻¹) z / s := by
    exact div_nonneg
      (sieveDensityBelow_reciprocal_pos P z hprime).le (by linarith)
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (add_le_add htail le_rfl) hscale)

/-- Difference form of the upper-target unscaled delay prime-sum bound. -/
theorem dimensionOneRosserPlusUnscaledDelayPrimeSum_le_difference_of_ratio
    (P : Finset Nat) {K level z s u : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u))
    (hRatio : ∀ x : Real,
      level ^ (1 / u) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    dimensionOneRosserPlusUnscaledDelayPrimeSum P level u z <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (dimensionOneDelayScaledPlus s - dimensionOneDelayScaledPlus u +
          (2 * K * u / (Real.log level * (1 - 1 / s))) *
            dimensionOneDelayScaledMinus (s - 1)) := by
  have hraw := dimensionOneRosserPlusUnscaledDelayPrimeSum_le_of_ratio
    P hK hprime hlevel hz hs hsLower hsu hcutoff hRatio
  have htail := integral_dimensionOneRosserPlusUnscaledDelay_le_sub
    hsLower hsu.le
  have hscale : 0 <= sieveDensityBelow P
      (fun q => (q : Real)⁻¹) z / s := by
    exact div_nonneg
      (sieveDensityBelow_reciprocal_pos P z hprime).le (by linarith)
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (add_le_add htail le_rfl) hscale)

/-- Difference form of the lower-target unscaled delay prime-sum bound. -/
theorem dimensionOneRosserMinusUnscaledDelayPrimeSum_le_difference_of_ratio
    (P : Finset Nat) {K level z s u : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u))
    (hRatio : ∀ x : Real,
      level ^ (1 / u) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    dimensionOneRosserMinusUnscaledDelayPrimeSum P level u z <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (dimensionOneDelayScaledMinus s - dimensionOneDelayScaledMinus u +
          (2 * K * u / (Real.log level * (1 - 1 / s))) *
            dimensionOneDelayScaledPlus (s - 1)) := by
  have hraw := dimensionOneRosserMinusUnscaledDelayPrimeSum_le_of_ratio
    P hK hprime hlevel hz hs hsLower hsu hcutoff hRatio
  have htail := integral_dimensionOneRosserMinusUnscaledDelay_le_sub
    hsLower hsu.le
  have hscale : 0 <= sieveDensityBelow P
      (fun q => (q : Real)⁻¹) z / s := by
    exact div_nonneg
      (sieveDensityBelow_reciprocal_pos P z hprime).le (by linarith)
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (add_le_add htail le_rfl) hscale)

end PrimesRestrictedDigits
