import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldPlateauMellinDecay
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Goldfeld Mellin transform on the positive real axis

The fixed plateau is supported in `[0, 2]` and bounded by one.  Integrating
the resulting power majorant gives the quantitative estimate used in
Goldfeld's proof of Koukoulopoulos Theorem 12.9.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 126.
Semantic review: `SEM-560`.
-/

noncomputable section

open Complex Set MeasureTheory

namespace BoundedGaps.Maynard

/-- Universal norm version of the positive-real Mellin estimate used in the
proof of Theorem 12.9. -/
theorem norm_goldfeldMellinContinuationData_Phi_ofReal_le_two_div
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    ‖goldfeldMellinContinuationData.Phi (delta : ℂ)‖ ≤ 2 / delta := by
  rw [goldfeldMellinContinuationData.agrees_on_right (by simpa using hdelta0)]
  let f : ℝ → ℂ := fun y =>
    (y : ℂ) ^ (((delta : ℝ) : ℂ) - 1) * (goldfeldPlateau y : ℂ)
  have hfIoi : IntegrableOn f (Ioi (0 : ℝ)) := by
    have hconv := goldfeldRawMellin_convergent
      (s := ((delta : ℝ) : ℂ)) (by simpa using hdelta0)
    rw [MellinConvergent] at hconv
    change IntegrableOn f (Ioi (0 : ℝ)) at hconv
    exact hconv
  have htruncate :
      (∫ y in Ioi (0 : ℝ), f y) = ∫ y in Ioc (0 : ℝ) 2, f y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ hy => hy.1)
    intro y hy
    have hyTwo : 2 ≤ y := by
      exact (lt_of_not_ge fun hyLe => hy.2 ⟨hy.1, hyLe⟩).le
    simp [f, goldfeldPlateau_eq_zero hyTwo]
  have hfIoc : IntegrableOn f (Ioc (0 : ℝ) 2) :=
    hfIoi.mono_set (fun _ hy => hy.1)
  have hpowInterval : IntervalIntegrable
      (fun y : ℝ => y ^ (delta - 1)) volume 0 2 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpowIoc : IntegrableOn (fun y : ℝ => y ^ (delta - 1))
      (Ioc (0 : ℝ) 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
      hpowInterval
  have hpoint : ∀ y ∈ Ioc (0 : ℝ) 2, ‖f y‖ ≤ y ^ (delta - 1) := by
    intro y hy
    dsimp only [f]
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hy.1]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (goldfeldPlateau_nonneg y)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hy.1.le _)
      (goldfeldPlateau_le_one y)
  have heval :
      (∫ y in Ioc (0 : ℝ) 2, y ^ (delta - 1)) =
        (2 : ℝ) ^ delta / delta := by
    calc
      (∫ y in Ioc (0 : ℝ) 2, y ^ (delta - 1)) =
          ∫ y in (0 : ℝ)..2, y ^ (delta - 1) := by
        exact (intervalIntegral.integral_of_le (by norm_num)).symm
      _ = ((2 : ℝ) ^ ((delta - 1) + 1) -
            (0 : ℝ) ^ ((delta - 1) + 1)) / ((delta - 1) + 1) := by
        rw [integral_rpow (Or.inl (by linarith))]
      _ = (2 : ℝ) ^ delta / delta := by
        rw [show delta - 1 + 1 = delta by ring,
          Real.zero_rpow hdelta0.ne']
        ring
  have hpow : (2 : ℝ) ^ delta ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hdelta1
  rw [goldfeldRawMellin, mellin]
  change ‖∫ y in Ioi (0 : ℝ), f y‖ ≤ 2 / delta
  rw [htruncate]
  calc
    ‖∫ y in Ioc (0 : ℝ) 2, f y‖ ≤
        ∫ y in Ioc (0 : ℝ) 2, ‖f y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioc (0 : ℝ) 2, y ^ (delta - 1) :=
      setIntegral_mono_on hfIoc.norm hpowIoc measurableSet_Ioc hpoint
    _ = (2 : ℝ) ^ delta / delta := heval
    _ ≤ 2 / delta :=
      (div_le_div_iff_of_pos_right hdelta0).2 hpow

end BoundedGaps.Maynard
