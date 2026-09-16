import PrimesRestrictedDigits.SieveAsymptotics.DecimalIwaniecWeightedDensity
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedWeight

/-!
# Weighted prime sum for the independent high-rank seed

This file applies Iwaniec's weighted density lemma to the transformed elementary seed
envelope. The resulting endpoint is exactly the shifted quantity `H(s - 1)`.
-/

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace PrimesRestrictedDigits

/-- The finite transformed prime sum carrying the independent seed
envelope. -/
noncomputable def dimensionOneRosserSeedPrimeSum
    (P : Finset Nat) (level s0 z : Real) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
    (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) *
      dimensionOneRosserSeedEnvelope
        (buchstabArgument level (p : Real))

private theorem dimensionOneRosserSeedPrimeSum_eq_scaled
    (P : Finset Nat) {level s0 z : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hz : 2 <= z) :
    dimensionOneRosserSeedPrimeSum P level s0 z =
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
        (∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
          (p : Real)⁻¹ *
            (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
              sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
            (Real.log (p : Real) / Real.log z) *
            dimensionOneRosserSeedWeight level (p : Real)) := by
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  rw [Finset.mul_sum]
  unfold dimensionOneRosserSeedPrimeSum
  apply Finset.sum_congr rfl
  intro p hp
  unfold dimensionOneRosserSeedWeight
  field_simp [hV.ne', hlogz.ne']

private theorem dimensionOneRosserSeed_log_data
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0) :
    Real.log z = Real.log level / s ∧
      Real.log (level / z) = Real.log level * (1 - 1 / s) ∧
      buchstabArgument level z = s - 1 ∧
      Real.log (level ^ (1 / s0)) = Real.log level / s0 := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by
    have := Real.exp_pos (5000 : Real)
    linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hL : Real.log level = s * Real.log z := by
    rw [hs]
    field_simp
  have hlogzEq : Real.log z = Real.log level / s := by
    rw [hL]
    field_simp
  have hlogDiv :
      Real.log (level / z) = Real.log level * (1 - 1 / s) := by
    rw [Real.log_div hlevelPos.ne' hzPos.ne', hlogzEq]
    ring
  exact ⟨hlogzEq, hlogDiv,
    buchstabArgument_eq_sub_one_of_log_ratio hs,
    log_rpow_one_div hlevelPos⟩

/-- Weighted Lemma 21 for the transformed seed envelope.  The endpoint is
the shifted envelope `H(s - 1)`, not a sign-specific delay profile. -/
theorem dimensionOneRosserSeedPrimeSum_le_of_ratio
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hRatio : ∀ x : Real,
      level ^ (1 / s0) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    dimensionOneRosserSeedPrimeSum P level s0 z <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        ((∫ t in s..s0,
          dimensionOneRosserSeedEnvelope (t - 1) / (t - 1)) +
        (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
          dimensionOneRosserSeedEnvelope (s - 1)) := by
  have hlogs := dimensionOneRosserSeed_log_data hlevel hz hs hsLarge hss0
  rcases hlogs with ⟨hlogzEq, hlogDiv, hargz, hlogCutoff⟩
  have hlogLevel : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by
    have := Real.exp_pos (5000 : Real)
    linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hOne : 0 < 1 - 1 / s := by
    rw [sub_pos, div_lt_one hsPos]
    have hexp : (1 : Real) <= Real.exp 5000 :=
      Real.one_le_exp (by norm_num)
    linarith
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hcutoffz : level ^ (1 / s0) < z :=
    dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 (by
      have hexp : (1 : Real) <= Real.exp 5000 :=
        Real.one_le_exp (by norm_num)
      linarith)
  rcases dimensionOneRosserSeedWeight_properties hlevel hz hs hsLarge hss0
      hcutoff with ⟨hB0, hBcont, hBmono⟩
  have hWeighted := iwaniecWeightedDensitySum_le_of_ratio
    P (dimensionOneRosserSeedWeight level) hK hprime hcutoff hcutoffz
      hRatio hBcont hBmono hB0
  have hScaled := mul_le_mul_of_nonneg_left hWeighted
    (mul_nonneg hV.le hlogz.le)
  rw [← dimensionOneRosserSeedPrimeSum_eq_scaled P hprime hz] at hScaled
  have hIntegralMul :
      Real.log level *
          (∫ x in (level ^ (1 / s0))..z,
            dimensionOneRosserSeedWeight level x /
              (x * Real.log x)) =
        ∫ t in s..s0,
          dimensionOneRosserSeedEnvelope (t - 1) / (t - 1) :=
    log_mul_integral_dimensionOneRosserSeedWeight_eq hlevel hz hs hsLarge
      hss0 hcutoff
  have hIntegral :
      (∫ x in (level ^ (1 / s0))..z,
        dimensionOneRosserSeedWeight level x /
          (x * Real.log x)) =
        (∫ t in s..s0,
          dimensionOneRosserSeedEnvelope (t - 1) / (t - 1)) /
            Real.log level := by
    apply (eq_div_iff hlogLevel.ne').2
    simpa only [mul_comm] using hIntegralMul
  have hBz : dimensionOneRosserSeedWeight level z =
      dimensionOneRosserSeedEnvelope (s - 1) /
        (Real.log level * (1 - 1 / s)) := by
    unfold dimensionOneRosserSeedWeight
    rw [hargz, hlogDiv]
  rw [hIntegral, hBz, hlogCutoff] at hScaled
  calc
    dimensionOneRosserSeedPrimeSum P level s0 z <=
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
          (((∫ t in s..s0,
              dimensionOneRosserSeedEnvelope (t - 1) / (t - 1)) /
                Real.log level) +
            2 * K *
                (dimensionOneRosserSeedEnvelope (s - 1) /
                  (Real.log level * (1 - 1 / s))) /
              (Real.log level / s0)) := hScaled
    _ = _ := by
      rw [hlogzEq]
      field_simp [hlogLevel.ne', hsPos.ne', hs0Pos.ne', hOne.ne']

end PrimesRestrictedDigits
