import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaZeroResidue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fixed-left-edge modified-Perron kernel estimates

On the project-fixed line `Re(s) = -1/2`, the modified kernel has an
integrable reciprocal-height majorant. This file also evaluates that majorant
and gives a generic interval reduction under an explicit logarithmic-
derivative bound and genuine integrability.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 115, proof of
Theorem 11.3. The source leaves the edge estimate as an exercise. Semantic
review: `SEM-530`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

/-- The modified Perron kernel has an integrable reciprocal-height bound on
the fixed negative-half line. -/
theorem norm_dirichletExplicitFormulaKernel_leftEdge_le
    {x t : ℝ} (hx : 2 ≤ x) :
    ‖dirichletExplicitFormulaKernel x
        (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
      6 / (|t| + 1) := by
  let s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I
  have hxpos : 0 < x := by linarith
  have hxone : (1 : ℝ) ≤ x := by linarith
  have hs : s ≠ 0 := by
    intro hsZero
    have hre := congrArg Complex.re hsZero
    norm_num [s] at hre
  rw [show (((-1 / 2 : ℝ) : ℂ) + t * I) = s by rfl,
    dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hxpos hs,
    norm_div]
  have hpow : x ^ (-1 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hxone (by norm_num)
  have hnum : ‖(x : ℂ) ^ s - 1‖ ≤ 2 := by
    calc
      ‖(x : ℂ) ^ s - 1‖ ≤ ‖(x : ℂ) ^ s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = x ^ (-1 / 2 : ℝ) + 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
        simp [s]
      _ ≤ 2 := by linarith
  have hhalf : (1 / 2 : ℝ) ≤ ‖s‖ := by
    calc
      (1 / 2 : ℝ) = |s.re| := by norm_num [s]
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  have htNorm : |t| ≤ ‖s‖ := by
    calc
      |t| = |s.im| := by simp [s]
      _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hscale : |t| + 1 ≤ 3 * ‖s‖ := by nlinarith
  have hsNormPos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hheightPos : 0 < |t| + 1 := by linarith [abs_nonneg t]
  calc
    ‖(x : ℂ) ^ s - 1‖ / ‖s‖ ≤ 2 / ‖s‖ :=
      div_le_div_of_nonneg_right hnum hsNormPos.le
    _ ≤ 6 / (|t| + 1) := by
      apply (div_le_div_iff₀ hsNormPos hheightPos).2
      nlinarith

/-- The symmetric reciprocal-height weight has an exact logarithmic integral. -/
theorem integral_inv_abs_add_one_neg_eq
    {U : ℝ} (hU : 0 ≤ U) :
    (∫ t in -U..U, (|t| + 1)⁻¹) =
      2 * Real.log (U + 1) := by
  let w : ℝ → ℝ := fun t => (|t| + 1)⁻¹
  have hwContinuous : Continuous w := by
    dsimp [w]
    exact (continuous_abs.add continuous_const).inv₀ (fun t => by
      have ht : 0 < |t| + 1 := by linarith [abs_nonneg t]
      exact ht.ne')
  have hpos : (∫ t in 0..U, w t) = Real.log (U + 1) := by
    rw [intervalIntegral.integral_congr (f := w)
      (g := fun t : ℝ => (t + 1)⁻¹)]
    · rw [intervalIntegral.integral_comp_add_right (fun t : ℝ => t⁻¹) 1,
        integral_inv_of_pos (by norm_num) (by linarith)]
      simp
    · intro t ht
      rw [uIcc_of_le hU] at ht
      simp [w, abs_of_nonneg ht.1]
  have hneg : (∫ t in -U..0, w t) = ∫ t in 0..U, w t := by
    calc
      (∫ t in -U..0, w t) = ∫ t in 0..U, w (-t) := by
        symm
        simpa only [neg_zero] using intervalIntegral.integral_comp_neg
          (a := 0) (b := U) w
      _ = ∫ t in 0..U, w t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        simp [w]
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hwContinuous.intervalIntegrable (-U) 0)
      (hwContinuous.intervalIntegrable 0 U),
    hneg, hpos]
  ring

/-- A uniform logarithmic-derivative majorant controls the full fixed left
edge through the exact reciprocal-height kernel integral. -/
theorem norm_intervalIntegral_dirichletExplicitFormulaIntegrand_leftEdge_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x U K : ℝ} (hx : 2 ≤ x) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hIntegrable : IntervalIntegrable
      (fun t : ℝ => dirichletExplicitFormulaIntegrand chi x
        (((-1 / 2 : ℝ) : ℂ) + t * Complex.I))
      MeasureTheory.volume (-U) U)
    (hLogDeriv : ∀ t ∈ Set.Icc (-U) U,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤ K) :
    ‖∫ t in -U..U,
        dirichletExplicitFormulaIntegrand chi x
          (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
      12 * K * Real.log (U + 1) := by
  let w : ℝ → ℝ := fun t => (|t| + 1)⁻¹
  let g : ℝ → ℝ := fun t => 6 * K * w t
  have hab : -U ≤ U := by linarith
  have hwContinuous : Continuous w := by
    dsimp [w]
    exact (continuous_abs.add continuous_const).inv₀ (fun t => by
      have ht : 0 < |t| + 1 := by linarith [abs_nonneg t]
      exact ht.ne')
  have hgIntegrable : IntervalIntegrable g volume (-U) U :=
    (continuous_const.mul hwContinuous).intervalIntegrable _ _
  have hpoint : ∀ t ∈ Icc (-U) U,
      ‖dirichletExplicitFormulaIntegrand chi x
        (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ g t := by
    intro t ht
    have hlog := hLogDeriv t ht
    have hkernel := norm_dirichletExplicitFormulaKernel_leftEdge_le
      (x := x) (t := t) hx
    rw [dirichletExplicitFormulaIntegrand, norm_mul, norm_neg]
    calc
      ‖logDeriv (DirichletCharacter.LFunction chi)
          (((-1 / 2 : ℝ) : ℂ) + t * I)‖ *
          ‖dirichletExplicitFormulaKernel x
            (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        K * (6 / (|t| + 1)) :=
          mul_le_mul hlog hkernel (norm_nonneg _) hK
      _ = g t := by simp [g, w, div_eq_mul_inv]; ring
  calc
    ‖∫ t in -U..U,
        dirichletExplicitFormulaIntegrand chi x
          (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        ∫ t in -U..U,
          ‖dirichletExplicitFormulaIntegrand chi x
            (((-1 / 2 : ℝ) : ℂ) + t * I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in -U..U, g t :=
      intervalIntegral.integral_mono_on hab hIntegrable.norm
        hgIntegrable hpoint
    _ = 12 * K * Real.log (U + 1) := by
      rw [show (∫ t in -U..U, g t) =
          6 * K * ∫ t in -U..U, (|t| + 1)⁻¹ by
        simp only [g, w, intervalIntegral.integral_const_mul],
        integral_inv_abs_add_one_neg_eq hU]
      ring

end

end BoundedGaps.Maynard
