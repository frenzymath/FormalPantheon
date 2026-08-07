import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The finite Dirichlet Perron kernel

This file defines the vertically parametrized scalar kernel from
`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 71, Lemma 7.1, and
evaluates its natural-cutoff endpoint exactly. The half weight is retained;
conversion to an inclusive arithmetic sum occurs only later.

Semantic review: `SEM-533`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory
open scoped Interval

noncomputable section

/-- The finite scalar Perron kernel after `s = alpha + i*t` has removed the
factor `i` from the contour normalization. -/
noncomputable def dirichletPerronKernel
    (y alpha U : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -U..U,
      (y : ℂ) ^ ((alpha : ℂ) + t * I) /
        ((alpha : ℂ) + t * I)

/-- The exact starred Perron weight at a positive natural cutoff. The zero
index is suppressed independently of the coefficient sequence. -/
def dirichletPerronNaturalWeight (x n : ℕ) : ℝ :=
  if n = 0 then 0
  else if n < x then 1
  else if n = x then 1 / 2
  else 0

@[simp]
theorem dirichletPerronNaturalWeight_zero (x : ℕ) :
    dirichletPerronNaturalWeight x 0 = 0 := by
  simp [dirichletPerronNaturalWeight]

@[simp]
theorem dirichletPerronNaturalWeight_of_pos_of_lt
    {x n : ℕ} (hn : 0 < n) (hnx : n < x) :
    dirichletPerronNaturalWeight x n = 1 := by
  simp [dirichletPerronNaturalWeight, hn.ne', hnx]

@[simp]
theorem dirichletPerronNaturalWeight_self {x : ℕ} (hx : 0 < x) :
    dirichletPerronNaturalWeight x x = 1 / 2 := by
  simp [dirichletPerronNaturalWeight, hx.ne']

@[simp]
theorem dirichletPerronNaturalWeight_of_lt
    {x n : ℕ} (hxn : x < n) :
    dirichletPerronNaturalWeight x n = 0 := by
  have hn : n ≠ 0 := (Nat.zero_lt_of_lt hxn).ne'
  simp [dirichletPerronNaturalWeight, hn,
    Nat.not_lt.mpr hxn.le, hxn.ne']

private lemma continuous_inv_perronLine
    {alpha : ℝ} (halpha : 0 < alpha) :
    Continuous fun t : ℝ =>
      (1 : ℂ) / ((alpha : ℂ) + t * I) := by
  apply continuous_const.div₀
  · fun_prop
  · intro t ht
    have hre := congrArg Complex.re ht
    simp at hre
    exact halpha.ne' hre

private lemma integral_inv_perronLine
    {alpha U : ℝ} (halpha : 0 < alpha) :
    (∫ t in -U..U, (1 : ℂ) / ((alpha : ℂ) + t * I)) =
      ((2 * Real.arctan (U / alpha) : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun t => (1 : ℂ) / ((alpha : ℂ) + t * I)
  have hg : Continuous g := by
    simpa [g] using continuous_inv_perronLine halpha
  have hgInt : IntervalIntegrable g volume (-U) U :=
    hg.intervalIntegrable _ _
  have hrePoint (t : ℝ) :
      (g t).re = alpha / (alpha ^ 2 + t ^ 2) := by
    simp [g, Complex.normSq_apply]
    congr 1; ring
  have himPoint (t : ℝ) : (g (-t)).im = -(g t).im := by
    simp [g, Complex.normSq_apply]
    ring
  have hre :
      (∫ t in -U..U, g t).re = 2 * Real.arctan (U / alpha) := by
    calc
      (∫ t in -U..U, g t).re = ∫ t in -U..U, (g t).re :=
        (intervalIntegral.intervalIntegral_re hgInt).symm
      _ = ∫ t in -U..U, alpha / (alpha ^ 2 + t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact hrePoint t
      _ = Real.arctan (U / alpha) -
          Real.arctan ((-U) / alpha) :=
        integral_div_sq_add_sq
      _ = 2 * Real.arctan (U / alpha) := by
        rw [show (-U) / alpha = -(U / alpha) by ring,
          Real.arctan_neg]
        ring
  have him : (∫ t in -U..U, g t).im = 0 := by
    have hcomp := intervalIntegral.integral_comp_neg
      (fun t : ℝ => (g t).im) (a := -U) (b := U)
    have hsame :
        (∫ t in -U..U, (g (-t)).im) =
          ∫ t in -U..U, (g t).im := by
      simpa using hcomp
    have hneg :
        (∫ t in -U..U, (g (-t)).im) =
          -(∫ t in -U..U, (g t).im) := by
      simp_rw [himPoint]
      exact intervalIntegral.integral_neg
    have hzero : (∫ t in -U..U, (g t).im) = 0 := by
      linarith
    calc
      (∫ t in -U..U, g t).im = ∫ t in -U..U, (g t).im :=
        (intervalIntegral.intervalIntegral_im hgInt).symm
      _ = 0 := hzero
  change (∫ t in -U..U, g t) =
    ((2 * Real.arctan (U / alpha) : ℝ) : ℂ)
  apply Complex.ext
  · simpa using hre
  · simpa using him

/-- At the jump, the finite Perron kernel is the exact arctangent ratio. -/
theorem dirichletPerronKernel_one_eq_arctan
    {alpha U : ℝ} (halpha : 0 < alpha) :
    dirichletPerronKernel 1 alpha U =
      ((Real.arctan (U / alpha) / Real.pi : ℝ) : ℂ) := by
  rw [dirichletPerronKernel]
  have hfun :
      (∫ t in -U..U,
        ((1 : ℝ) : ℂ) ^ ((alpha : ℂ) + t * I) /
          ((alpha : ℂ) + t * I)) =
        ∫ t in -U..U, (1 : ℂ) / ((alpha : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp
  rw [hfun, integral_inv_perronLine halpha]
  push_cast
  field_simp [Real.pi_ne_zero]

private lemma arctan_le_self_of_nonneg {z : ℝ} (hz : 0 ≤ z) :
    Real.arctan z ≤ z := by
  have h := intervalIntegral.integral_mono_on hz
    (intervalIntegral.intervalIntegrable_inv_one_add_sq (a := 0) (b := z))
    (show IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 z by
      exact intervalIntegrable_const)
    (fun t _ => inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t]))
  simpa using h

/-- The exact endpoint kernel differs from its limiting half weight by at
most `alpha/(pi*U)`. -/
theorem norm_dirichletPerronKernel_one_sub_half_le
    {alpha U : ℝ} (halpha : 0 < alpha) (hU : 0 < U) :
    ‖dirichletPerronKernel 1 alpha U - (1 / 2 : ℂ)‖ ≤
      alpha / (Real.pi * U) := by
  rw [dirichletPerronKernel_one_eq_arctan halpha]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hratio : 0 < U / alpha := div_pos hU halpha
  have hnonpos :
      Real.arctan (U / alpha) / Real.pi - 1 / 2 ≤ 0 := by
    rw [sub_nonpos, div_le_iff₀ Real.pi_pos]
    nlinarith [Real.arctan_lt_pi_div_two (U / alpha)]
  rw [abs_of_nonpos hnonpos]
  have hinv : (U / alpha)⁻¹ = alpha / U := by
    field_simp
  have hidentity :
      -(Real.arctan (U / alpha) / Real.pi - 1 / 2) =
        Real.arctan (alpha / U) / Real.pi := by
    rw [← hinv, Real.arctan_inv_of_pos hratio]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hidentity]
  calc
    Real.arctan (alpha / U) / Real.pi ≤
        (alpha / U) / Real.pi := by
      exact div_le_div_of_nonneg_right
        (arctan_le_self_of_nonneg (div_nonneg halpha.le hU.le))
        Real.pi_pos.le
    _ = alpha / (Real.pi * U) := by field_simp

end

end BoundedGaps.Maynard
