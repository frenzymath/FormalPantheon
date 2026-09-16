import PrimesRestrictedDigits.SieveAsymptotics.DecimalIwaniecWeightedDensity
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserRawFirstIntegral

/-!
# Raw first weighted dimension-one Rosser sums

This applies the decimal form of Iwaniec's Lemma 21 to the raw first weights and evaluates the
exact transformed integral.
-/

open Finset MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable def dimensionOneRosserPlusRawFirstPrimeSum
    (P : Finset Nat) (level s0 z : Real) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
    (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) *
      dimensionOneRosserModelMinusRaw (buchstabArgument level (p : Real))

noncomputable def dimensionOneRosserMinusRawFirstPrimeSum
    (P : Finset Nat) (level s0 z : Real) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
    (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) *
      dimensionOneRosserModelPlusRaw (buchstabArgument level (p : Real))

private theorem raw_first_log_data
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) :
    Real.log z = Real.log level / s ∧
      Real.log (level / z) = Real.log level * (1 - 1 / s) ∧
      buchstabArgument level z = s - 1 ∧
      Real.log (level ^ (1 / s0)) = Real.log level / s0 := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
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

theorem dimensionOneRosserPlusRawFirstPrimeSum_eq_scaled
    (P : Finset Nat) {level s0 z : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hz : 2 <= z) :
    dimensionOneRosserPlusRawFirstPrimeSum P level s0 z =
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
        (∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
          (p : Real)⁻¹ *
            (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
              sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
            (Real.log (p : Real) / Real.log z) *
            dimensionOneRosserPlusRawFirstWeight level (p : Real)) := by
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  rw [Finset.mul_sum]
  unfold dimensionOneRosserPlusRawFirstPrimeSum
  apply Finset.sum_congr rfl
  intro p hp
  unfold dimensionOneRosserPlusRawFirstWeight
  field_simp [hV.ne', hlogz.ne']

theorem dimensionOneRosserMinusRawFirstPrimeSum_eq_scaled
    (P : Finset Nat) {level s0 z : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hz : 2 <= z) :
    dimensionOneRosserMinusRawFirstPrimeSum P level s0 z =
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
        (∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
          (p : Real)⁻¹ *
            (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
              sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
            (Real.log (p : Real) / Real.log z) *
            dimensionOneRosserMinusRawFirstWeight level (p : Real)) := by
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  rw [Finset.mul_sum]
  unfold dimensionOneRosserMinusRawFirstPrimeSum
  apply Finset.sum_congr rfl
  intro p hp
  unfold dimensionOneRosserMinusRawFirstWeight
  field_simp [hV.ne', hlogz.ne']

theorem dimensionOneRosserPlusRawFirstPrimeSum_le_of_ratio
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hRatio : ∀ u : Real, level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserPlusRawFirstPrimeSum P level s0 z <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusRaw s -
          dimensionOneRosserModelPlusRaw s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelMinusRaw (s - 1)) := by
  have hlogs := raw_first_log_data hlevel hz hs (by linarith) hss0
  rcases hlogs with ⟨hlogzEq, hlogDiv, hargz, hlogCutoff⟩
  have hlogLevel : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hOne : 0 < 1 - 1 / s := by
    rw [sub_pos, div_lt_one hsPos]
    linarith
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hcutoffz : level ^ (1 / s0) < z :=
    dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 (by linarith)
  rcases dimensionOneRosserPlusRawFirstWeight_properties hlevel hz hs hss0
      hcutoff hsLower with ⟨hB0, hBcont, hBmono⟩
  have hWeighted := iwaniecWeightedDensitySum_le_of_ratio
    P (dimensionOneRosserPlusRawFirstWeight level) hK hprime hcutoff
      hcutoffz hRatio hBcont hBmono hB0
  have hScaled := mul_le_mul_of_nonneg_left hWeighted
    (mul_nonneg hV.le hlogz.le)
  rw [<- dimensionOneRosserPlusRawFirstPrimeSum_eq_scaled P hprime hz]
    at hScaled
  have hIntegralMul :
      Real.log level *
          (∫ x in (level ^ (1 / s0))..z,
            dimensionOneRosserPlusRawFirstWeight level x /
              (x * Real.log x)) =
        dimensionOneRosserModelPlusRaw s -
          dimensionOneRosserModelPlusRaw s0 := by
    rw [log_mul_integral_dimensionOneRosserPlusRawFirstWeight_eq
      hlevel hz hs hss0 hsLower]
    exact integral_dimensionOneRosserModelMinusRaw_div_eq hsLower hss0.le
  have hIntegral :
      (∫ x in (level ^ (1 / s0))..z,
        dimensionOneRosserPlusRawFirstWeight level x /
          (x * Real.log x)) =
        (dimensionOneRosserModelPlusRaw s -
          dimensionOneRosserModelPlusRaw s0) / Real.log level := by
    apply (eq_div_iff hlogLevel.ne').2
    simpa only [mul_comm] using hIntegralMul
  have hBz : dimensionOneRosserPlusRawFirstWeight level z =
      dimensionOneRosserModelMinusRaw (s - 1) /
        (Real.log level * (1 - 1 / s)) := by
    unfold dimensionOneRosserPlusRawFirstWeight
    rw [hargz, hlogDiv]
  rw [hIntegral, hBz, hlogCutoff] at hScaled
  calc
    dimensionOneRosserPlusRawFirstPrimeSum P level s0 z <=
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
          ((dimensionOneRosserModelPlusRaw s -
              dimensionOneRosserModelPlusRaw s0) / Real.log level +
            2 * K *
                (dimensionOneRosserModelMinusRaw (s - 1) /
                  (Real.log level * (1 - 1 / s))) /
              (Real.log level / s0)) := hScaled
    _ = _ := by
      rw [hlogzEq]
      field_simp [hlogLevel.ne', hsPos.ne', hs0Pos.ne', hOne.ne']

theorem dimensionOneRosserMinusRawFirstPrimeSum_le_of_ratio
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hRatio : ∀ u : Real, level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserMinusRawFirstPrimeSum P level s0 z <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (dimensionOneRosserModelMinusRaw s -
          dimensionOneRosserModelMinusRaw s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelPlusRaw (s - 1)) := by
  have hlogs := raw_first_log_data hlevel hz hs hsLower hss0
  rcases hlogs with ⟨hlogzEq, hlogDiv, hargz, hlogCutoff⟩
  have hlogLevel : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hOne : 0 < 1 - 1 / s := by
    rw [sub_pos, div_lt_one hsPos]
    linarith
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hcutoffz : level ^ (1 / s0) < z :=
    dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 hsLower
  rcases dimensionOneRosserMinusRawFirstWeight_properties hlevel hz hs hss0
      hcutoff hsLower with ⟨hB0, hBcont, hBmono⟩
  have hWeighted := iwaniecWeightedDensitySum_le_of_ratio
    P (dimensionOneRosserMinusRawFirstWeight level) hK hprime hcutoff
      hcutoffz hRatio hBcont hBmono hB0
  have hScaled := mul_le_mul_of_nonneg_left hWeighted
    (mul_nonneg hV.le hlogz.le)
  rw [<- dimensionOneRosserMinusRawFirstPrimeSum_eq_scaled P hprime hz]
    at hScaled
  have hIntegralMul :
      Real.log level *
          (∫ x in (level ^ (1 / s0))..z,
            dimensionOneRosserMinusRawFirstWeight level x /
              (x * Real.log x)) =
        dimensionOneRosserModelMinusRaw s -
          dimensionOneRosserModelMinusRaw s0 := by
    rw [log_mul_integral_dimensionOneRosserMinusRawFirstWeight_eq
      hlevel hz hs hss0 hsLower]
    exact integral_dimensionOneRosserModelPlusRaw_div_eq hsLower hss0.le
  have hIntegral :
      (∫ x in (level ^ (1 / s0))..z,
        dimensionOneRosserMinusRawFirstWeight level x /
          (x * Real.log x)) =
        (dimensionOneRosserModelMinusRaw s -
          dimensionOneRosserModelMinusRaw s0) / Real.log level := by
    apply (eq_div_iff hlogLevel.ne').2
    simpa only [mul_comm] using hIntegralMul
  have hBz : dimensionOneRosserMinusRawFirstWeight level z =
      dimensionOneRosserModelPlusRaw (s - 1) /
        (Real.log level * (1 - 1 / s)) := by
    unfold dimensionOneRosserMinusRawFirstWeight
    rw [hargz, hlogDiv]
  rw [hIntegral, hBz, hlogCutoff] at hScaled
  calc
    dimensionOneRosserMinusRawFirstPrimeSum P level s0 z <=
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) z * Real.log z) *
          ((dimensionOneRosserModelMinusRaw s -
              dimensionOneRosserModelMinusRaw s0) / Real.log level +
            2 * K *
                (dimensionOneRosserModelPlusRaw (s - 1) /
                  (Real.log level * (1 - 1 / s))) /
              (Real.log level / s0)) := hScaled
    _ = _ := by
      rw [hlogzEq]
      field_simp [hlogLevel.ne', hsPos.ne', hs0Pos.ne', hOne.ne']

end PrimesRestrictedDigits
