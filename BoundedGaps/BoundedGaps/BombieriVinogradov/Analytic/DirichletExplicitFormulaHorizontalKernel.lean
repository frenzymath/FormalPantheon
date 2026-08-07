import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaZeroResidue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Horizontal modified-Perron kernel estimates

`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 115, uses the
modified kernel `(x^s-1)/s` on a rectangle with right edge
`1+1/log x`, but leaves the edge estimates as an exercise. This file proves
the elementary horizontal kernel bound and reduces a horizontal integrand
estimate to a supplied logarithmic-derivative majorant.

It does not prove that majorant, edge integrability, or the complete contour
estimate. Semantic review: `SEM-527`.
-/

noncomputable section

open scoped Interval

namespace BoundedGaps.Maynard

/-- The modified Perron kernel on either horizontal edge is controlled by
its real-power numerator and the comparison height. -/
theorem norm_dirichletExplicitFormulaKernel_horizontal_le
    {x sigma t T : ℝ} (hx : 0 < x) (hT : 0 < T) (ht : T ≤ |t|) :
    ‖dirichletExplicitFormulaKernel x
        ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (x ^ sigma + 1) / T := by
  let s : ℂ := (sigma : ℂ) + (t : ℂ) * Complex.I
  have hTnorm : T ≤ ‖s‖ := by
    calc
      T ≤ |t| := ht
      _ = |s.im| := by simp [s]
      _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hs : s ≠ 0 := by
    intro hs
    rw [hs, norm_zero] at hTnorm
    linarith
  rw [show (sigma : ℂ) + (t : ℂ) * Complex.I = s by rfl,
    dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hx hs,
    Complex.norm_div]
  have hnum : ‖(x : ℂ) ^ s - 1‖ ≤ x ^ sigma + 1 := by
    calc
      ‖(x : ℂ) ^ s - 1‖ ≤ ‖(x : ℂ) ^ s‖ + ‖1‖ := norm_sub_le _ _
      _ = x ^ sigma + 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
        simp [s]
  calc
    ‖(x : ℂ) ^ s - 1‖ / ‖s‖ ≤ (x ^ sigma + 1) / ‖s‖ := by
      exact div_le_div_of_nonneg_right hnum (norm_nonneg s)
    _ ≤ (x ^ sigma + 1) / T := by
      exact div_le_div_of_nonneg_left (by positivity) hT hTnorm

/-- On the source right-edge range, a uniform factor four bounds the
horizontal modified Perron kernel. -/
theorem norm_dirichletExplicitFormulaKernel_horizontal_le_four_mul
    {x sigma t T : ℝ} (hx : 2 ≤ x)
    (hsigma : sigma ≤ 1 + 1 / Real.log x)
    (hT : 0 < T) (ht : T ≤ |t|) :
    ‖dirichletExplicitFormulaKernel x
        ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4 * x / T := by
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hxne : x ≠ 1 := by linarith
  have hpow : x ^ sigma ≤ x ^ (1 + 1 / Real.log x) :=
    Real.rpow_le_rpow_of_exponent_le hxone hsigma
  have hnum : x ^ sigma + 1 ≤ 4 * x := by
    calc
      x ^ sigma + 1 ≤ x ^ (1 + 1 / Real.log x) + 1 :=
        add_le_add hpow le_rfl
      _ = x * Real.exp 1 + 1 := by
        rw [Real.rpow_add hxpos, Real.rpow_one, one_div,
          Real.rpow_inv_log hxpos hxne]
      _ ≤ x * 3 + x := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le hxpos.le) hxone
      _ = 4 * x := by ring
  refine (norm_dirichletExplicitFormulaKernel_horizontal_le hxpos hT ht).trans ?_
  exact div_le_div_of_nonneg_right hnum hT.le

/-- A supplied logarithmic-derivative majorant controls one left-to-right
horizontal interval of the modified Perron integrand. -/
theorem norm_intervalIntegral_dirichletExplicitFormulaIntegrand_horizontal_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x a b t T K : ℝ} (hx : 2 ≤ x) (hab : a ≤ b)
    (hb : b ≤ 1 + 1 / Real.log x) (hT : 0 < T) (ht : T ≤ |t|)
    (hK : 0 ≤ K)
    (hIntegrable : IntervalIntegrable
      (fun r : ℝ => dirichletExplicitFormulaIntegrand chi x
        ((r : ℂ) + (t : ℂ) * Complex.I)) MeasureTheory.volume a b)
    (hLogDeriv : ∀ r ∈ Set.Icc a b,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K) :
    ‖∫ r in a..b,
        dirichletExplicitFormulaIntegrand chi x
          ((r : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * K * x / T) * (b - a) := by
  have hpoint : ∀ r ∈ Set.Icc a b,
      ‖dirichletExplicitFormulaIntegrand chi x
        ((r : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4 * K * x / T := by
    intro r hr
    have hrUpper : r ≤ 1 + 1 / Real.log x := hr.2.trans hb
    have hkernel :=
      norm_dirichletExplicitFormulaKernel_horizontal_le_four_mul
        hx hrUpper hT ht
    have hlog := hLogDeriv r hr
    rw [dirichletExplicitFormulaIntegrand, norm_mul, norm_neg]
    calc
      ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + (t : ℂ) * Complex.I)‖ *
          ‖dirichletExplicitFormulaKernel x
            ((r : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * (4 * x / T) :=
        mul_le_mul hlog hkernel (norm_nonneg _) hK
      _ = 4 * K * x / T := by ring
  calc
    ‖∫ r in a..b,
        dirichletExplicitFormulaIntegrand chi x
          ((r : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        ∫ r in a..b,
          ‖dirichletExplicitFormulaIntegrand chi x
            ((r : ℂ) + (t : ℂ) * Complex.I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ _r in a..b, 4 * K * x / T :=
      intervalIntegral.integral_mono_on hab hIntegrable.norm
        intervalIntegrable_const hpoint
    _ = (4 * K * x / T) * (b - a) := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
      ring

end BoundedGaps.Maynard
