import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit cutoff arithmetic for the quadratic L-value bound

This file chooses a natural smoothing cutoff at the source scale
`q * (log q)^4` and proves the numerical inequalities used in Theorem 12.8.
All numerals are project-derived.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125.
Semantic review: `SEM-547`.
-/

noncomputable section

namespace BoundedGaps.Maynard

private noncomputable def quadraticLValueScale (q : ℕ) : ℝ :=
  (2 ^ 22 : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ 4

/-- The explicit natural smoothing cutoff used for the effective L-value
bound. -/
noncomputable def quadraticLValueCutoff (q : ℕ) : ℕ :=
  ⌈quadraticLValueScale q⌉₊

private lemma one_half_lt_log_natCast {q : ℕ} (hq : 1 < q) :
    (1 / 2 : ℝ) < Real.log (q : ℝ) := by
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  exact hlogTwo.trans_le (Real.log_le_log (by norm_num) hqTwo)

private lemma quadraticLValueScale_pos {q : ℕ} (hq : 1 < q) :
    0 < quadraticLValueScale q := by
  have hqPos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hlogPos : 0 < Real.log (q : ℝ) := by
    linarith [one_half_lt_log_natCast hq]
  unfold quadraticLValueScale
  exact mul_pos (mul_pos (by norm_num) hqPos) (pow_pos hlogPos 4)

private lemma one_eighth_le_natCast_mul_log_pow_four {q : ℕ} (hq : 1 < q) :
    (1 / 8 : ℝ) ≤ (q : ℝ) * (Real.log (q : ℝ)) ^ 4 := by
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogPow : (1 / 2 : ℝ) ^ 4 ≤ (Real.log (q : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (one_half_lt_log_natCast hq).le 4
  have hmul := mul_le_mul hqTwo hlogPow (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 4)
    (by positivity : (0 : ℝ) ≤ q)
  norm_num at hmul ⊢
  exact hmul

private lemma quadraticLValueScale_le_cutoff {q : ℕ} :
    quadraticLValueScale q ≤ (quadraticLValueCutoff q : ℝ) := by
  exact Nat.le_ceil _

private lemma cutoff_le_two_mul_quadraticLValueScale
    {q : ℕ} (hq : 1 < q) :
    (quadraticLValueCutoff q : ℝ) ≤ 2 * quadraticLValueScale q := by
  unfold quadraticLValueCutoff
  apply Nat.ceil_le_two_mul
  have hmul := one_eighth_le_natCast_mul_log_pow_four hq
  unfold quadraticLValueScale
  nlinarith

/-- The explicit cutoff is in the domain of the square-sum lower bound. -/
theorem four_le_quadraticLValueCutoff {q : ℕ} (hq : 1 < q) :
    4 ≤ quadraticLValueCutoff q := by
  have hscale := quadraticLValueScale_le_cutoff (q := q)
  have hmul := one_eighth_le_natCast_mul_log_pow_four hq
  have hfour : (4 : ℝ) ≤ quadraticLValueScale q := by
    unfold quadraticLValueScale
    nlinarith
  exact_mod_cast hfour.trans hscale

/-- A coarse logarithmic upper bound for the explicit cutoff. -/
theorem log_quadraticLValueCutoff_le {q : ℕ} (hq : 1 < q) :
    Real.log (quadraticLValueCutoff q : ℝ) ≤
      51 * Real.log (q : ℝ) := by
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := hqTwo.trans' (by norm_num)
  have hqPos : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hqTwo
  have hlogNonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
  have hlogLeQ : Real.log (q : ℝ) ≤ (q : ℝ) :=
    (Real.log_le_sub_one_of_pos hqPos).trans (by linarith)
  have htwoPow : (2 : ℝ) ^ 23 ≤ (q : ℝ) ^ 23 :=
    pow_le_pow_left₀ (by norm_num) hqTwo 23
  have hlogPow : (Real.log (q : ℝ)) ^ 4 ≤ (q : ℝ) ^ 4 :=
    pow_le_pow_left₀ hlogNonneg hlogLeQ 4
  have hcutPow : (quadraticLValueCutoff q : ℝ) ≤ (q : ℝ) ^ 51 := by
    calc
      (quadraticLValueCutoff q : ℝ) ≤ 2 * quadraticLValueScale q :=
        cutoff_le_two_mul_quadraticLValueScale hq
      _ = (2 : ℝ) ^ 23 * q * (Real.log (q : ℝ)) ^ 4 := by
        unfold quadraticLValueScale
        norm_num
        ring
      _ ≤ (q : ℝ) ^ 23 * q * (q : ℝ) ^ 4 := by
        gcongr
      _ = (q : ℝ) ^ 28 := by ring
      _ ≤ (q : ℝ) ^ 51 := pow_le_pow_right₀ hqOne (by norm_num)
  have hcutPos : (0 : ℝ) < quadraticLValueCutoff q := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4)
      (four_le_quadraticLValueCutoff hq))
  have hlog := Real.log_le_log hcutPos hcutPow
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

private lemma cutoffLowerScale_le_sqrt {q : ℕ} (hq : 1 < q) :
    2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤
      Real.sqrt (quadraticLValueCutoff q : ℝ) := by
  have hleftNonneg :
      0 ≤ 2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    positivity
  have hleftSq :
      (2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        quadraticLValueScale q := by
    have hsqrtQSq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) :=
      Real.sq_sqrt (by positivity)
    unfold quadraticLValueScale
    rw [show
      (2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        4194304 * (Real.sqrt (q : ℝ)) ^ 2 *
          (Real.log (q : ℝ)) ^ 4 by ring]
    rw [hsqrtQSq]
    norm_num
  have hsqrtSq :
      (Real.sqrt (quadraticLValueCutoff q : ℝ)) ^ 2 =
        (quadraticLValueCutoff q : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hscale := quadraticLValueScale_le_cutoff (q := q)
  have hsqrtNonneg := Real.sqrt_nonneg (quadraticLValueCutoff q : ℝ)
  nlinarith

/-- The comparison error at the explicit cutoff consumes at most one eighth
of the square-sum main scale. -/
theorem quadraticLValueComparisonError_le {q : ℕ} (hq : 1 < q) :
    (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
      (1 / 8 : ℝ) * Real.sqrt (quadraticLValueCutoff q : ℝ) := by
  have hlogPos : 0 < Real.log (q : ℝ) := by
    linarith [one_half_lt_log_natCast hq]
  have hcoef :
      6 + 4 * Real.log (quadraticLValueCutoff q : ℝ) ≤
        216 * Real.log (q : ℝ) := by
    have hlogCut := log_quadraticLValueCutoff_le hq
    have hlogHalf := one_half_lt_log_natCast hq
    linarith
  have hfactorNonneg :
      0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) hlogPos.le
  have herror :
      (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
        216 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    calc
      (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ) =
        (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
          (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by ring
      _ ≤ (216 * Real.log (q : ℝ)) *
          (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef hfactorNonneg
      _ = 216 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by ring
  have hlower := cutoffLowerScale_le_sqrt hq
  calc
    (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
      216 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := herror
    _ ≤ 256 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
      gcongr
      norm_num
    _ = (1 / 8 : ℝ) *
        (2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) := by ring
    _ ≤ (1 / 8 : ℝ) * Real.sqrt (quadraticLValueCutoff q : ℝ) := by
      gcongr

/-- The natural ceiling enlarges the source scale by less than the displayed
factor two, so its square root has this explicit upper bound. -/
theorem sqrt_quadraticLValueCutoff_le {q : ℕ} (hq : 1 < q) :
    Real.sqrt (quadraticLValueCutoff q : ℝ) ≤
      4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
  have hrightNonneg :
      0 ≤ 4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    positivity
  have hrightSq :
      (4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        4 * quadraticLValueScale q := by
    have hsqrtQSq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) :=
      Real.sq_sqrt (by positivity)
    unfold quadraticLValueScale
    rw [show
      (4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        16777216 * (Real.sqrt (q : ℝ)) ^ 2 *
          (Real.log (q : ℝ)) ^ 4 by ring]
    rw [hsqrtQSq]
    norm_num
    ring
  have hsqrtSq :
      (Real.sqrt (quadraticLValueCutoff q : ℝ)) ^ 2 =
        (quadraticLValueCutoff q : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hcut := cutoff_le_two_mul_quadraticLValueScale hq
  have hscalePos := quadraticLValueScale_pos hq
  have hsqrtNonneg := Real.sqrt_nonneg (quadraticLValueCutoff q : ℝ)
  nlinarith

end BoundedGaps.Maynard
