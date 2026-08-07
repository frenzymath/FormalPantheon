import BoundedGaps.BombieriVinogradov.Analytic.PerronEnvelope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Perron envelope integral

This file evaluates the continuous reciprocal Perron envelope in the large
regime used by Akbary--Hambrook's optimized truncation.

Source: `AkbaryHambrook2013v2`, Section 6, p. 18, between equations (6.4) and
(6.5). Semantic review: `SEM-455`.
-/

open MeasureTheory
open scoped Interval

namespace BoundedGaps.Maynard

noncomputable section

/-- The totalized reciprocal Perron envelope is always nonnegative, including
for heights outside the positive source regime. -/
theorem perronEnvelope_nonneg (B t : ℝ) :
    0 ≤ perronEnvelope B t := by
  simp only [perronEnvelope]
  split_ifs
  · positivity
  · exact inv_nonneg.mpr (le_max_of_le_left (abs_nonneg t))

/-- In the large regime, the symmetric integral of the reciprocal Perron
envelope has the logarithmic value used after equation (6.4). -/
theorem integral_perronEnvelope_eq_two_mul_log
    {B T : ℝ} (hB : 0 < B) (hT : 0 < T) (hBT : 1 ≤ T * B) :
    (∫ t in -T..T, perronEnvelope B t) =
      2 * Real.log (Real.exp 1 * T * B) := by
  have hinvT : B⁻¹ ≤ T := (inv_le_iff_one_le_mul₀ hB).2 hBT
  have hcont : Continuous (perronEnvelope B) := continuous_perronEnvelope hB.le
  have hzeroInv : (∫ t in 0..B⁻¹, perronEnvelope B t) = 1 := by
    rw [intervalIntegral.integral_congr (f := perronEnvelope B)
      (g := fun _ ↦ B)]
    · simp [hB.ne']
    · intro t ht
      rw [Set.uIcc_of_le (inv_nonneg.mpr hB.le)] at ht
      rw [perronEnvelope, if_neg hB.ne', abs_of_nonneg ht.1,
        max_eq_right ht.2, inv_inv]
  have hinvTop : (∫ t in B⁻¹..T, perronEnvelope B t) =
      Real.log (T * B) := by
    rw [intervalIntegral.integral_congr (f := perronEnvelope B)
      (g := fun t ↦ t⁻¹)]
    · rw [integral_inv_of_pos (inv_pos.mpr hB) hT]
      congr 1
      field_simp
    · intro t ht
      rw [Set.uIcc_of_le hinvT] at ht
      have ht0 : 0 ≤ t := (inv_pos.mpr hB).le.trans ht.1
      rw [perronEnvelope, if_neg hB.ne', abs_of_nonneg ht0,
        max_eq_left ht.1]
  have hzeroTop : (∫ t in 0..T, perronEnvelope B t) =
      1 + Real.log (T * B) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
      hzeroInv, hinvTop]
  have hneg : (∫ t in -T..0, perronEnvelope B t) =
      ∫ t in 0..T, perronEnvelope B t := by
    calc
      (∫ t in -T..0, perronEnvelope B t) =
          ∫ t in 0..T, perronEnvelope B (-t) := by
            symm
            have h := intervalIntegral.integral_comp_neg
              (a := 0) (b := T) (f := perronEnvelope B)
            rw [neg_zero] at h
            exact h
      _ = ∫ t in 0..T, perronEnvelope B t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        simp [perronEnvelope]
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
    hneg, hzeroTop]
  have hTB : T * B ≠ 0 := mul_ne_zero hT.ne' hB.ne'
  rw [show Real.exp 1 * T * B = Real.exp 1 * (T * B) by ring,
    Real.log_mul (Real.exp_ne_zero 1) hTB, Real.log_exp]
  ring

end

end BoundedGaps.Maynard
