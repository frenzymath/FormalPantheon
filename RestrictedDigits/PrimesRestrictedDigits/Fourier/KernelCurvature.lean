import PrimesRestrictedDigits.Fourier.KernelNormSq
import PrimesRestrictedDigits.Fourier.CurvatureInterpolation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform curvature of the squared digit kernel

The exact double-cosine expansion gives a global lower second-derivative bound.
After adding a quadratic, this supplies certified endpoint bounds on every
decimal cell without numerical interior-extremum searches.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private noncomputable def frequency (d e : ℕ) : ℝ :=
  2 * Real.pi * ((e : ℝ) - (d : ℝ))

private noncomputable def kernelSqCosine (a : Fin 10) (x : ℝ) : ℝ :=
  (1 / 81 : ℝ) *
    ∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
      Real.cos (frequency d e * x)

private noncomputable def kernelSqFirst (a : Fin 10) (x : ℝ) : ℝ :=
  (1 / 81 : ℝ) *
    ∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
      (-Real.sin (frequency d e * x) * frequency d e)

private noncomputable def kernelSqSecond (a : Fin 10) (x : ℝ) : ℝ :=
  (1 / 81 : ℝ) *
    ∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
      (-(Real.cos (frequency d e * x) * frequency d e) * frequency d e)

private theorem hasDerivAt_kernelSqCosine (a : Fin 10) (x : ℝ) :
    HasDerivAt (kernelSqCosine a) (kernelSqFirst a x) x := by
  unfold kernelSqCosine kernelSqFirst
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro d hd
  apply HasDerivAt.fun_sum
  intro e he
  exact (hasDerivAt_const_mul (x := x) (frequency d e)).cos

private theorem hasDerivAt_kernelSqFirst (a : Fin 10) (x : ℝ) :
    HasDerivAt (kernelSqFirst a) (kernelSqSecond a x) x := by
  unfold kernelSqFirst kernelSqSecond
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro d hd
  apply HasDerivAt.fun_sum
  intro e he
  have h := (hasDerivAt_const_mul (x := x) (frequency d e)).sin
  have hneg := h.neg
  have hmul := hneg.mul_const (frequency d e)
  simpa [mul_comm] using hmul

private theorem kernelSqCosine_eq (a : Fin 10) :
    kernelSqCosine a = fun x => digitKernel a x ^ 2 := by
  funext x
  rw [digitKernel_sq_eq_cos_sum]
  rfl

private theorem hasDerivAt_digitKernel_sq (a : Fin 10) (x : ℝ) :
    HasDerivAt (fun y : ℝ => digitKernel a y ^ 2) (kernelSqFirst a x) x := by
  rw [← kernelSqCosine_eq a]
  exact hasDerivAt_kernelSqCosine a x

private theorem iteratedDeriv_two_digitKernel_sq (a : Fin 10) (x : ℝ) :
    (deriv^[2] (fun y : ℝ => digitKernel a y ^ 2)) x = kernelSqSecond a x := by
  change deriv (deriv (fun y : ℝ => digitKernel a y ^ 2)) x = _
  have hfirst : deriv (fun y : ℝ => digitKernel a y ^ 2) = kernelSqFirst a := by
    funext y
    exact (hasDerivAt_digitKernel_sq a y).deriv
  rw [hfirst]
  exact (hasDerivAt_kernelSqFirst a x).deriv

private theorem kernelSqSecond_term_lower (a : Fin 10) (x : ℝ)
    {d e : ℕ} (hd : d ∈ allowedDecimalDigits a)
    (he : e ∈ allowedDecimalDigits a) :
    -(324 * Real.pi ^ 2) ≤
      -(Real.cos (frequency d e * x) * frequency d e) * frequency d e := by
  have hdlt : d < 10 := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hd).1
  have helt : e < 10 := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp he).1
  have hdle : (d : ℝ) ≤ 9 := by
    exact_mod_cast (show d ≤ 9 by omega)
  have hele : (e : ℝ) ≤ 9 := by
    exact_mod_cast (show e ≤ 9 by omega)
  have hdnonneg : (0 : ℝ) ≤ d := by positivity
  have henonneg : (0 : ℝ) ≤ e := by positivity
  have hdiff_lower : -(9 : ℝ) ≤ (e : ℝ) - (d : ℝ) := by
    linarith
  have hdiff_upper : (e : ℝ) - (d : ℝ) ≤ 9 := by
    linarith
  have hdiff_sq : ((e : ℝ) - (d : ℝ)) ^ 2 ≤ 81 := by
    nlinarith
  have hfreq_sq : frequency d e ^ 2 ≤ 324 * Real.pi ^ 2 := by
    calc
      frequency d e ^ 2 = (2 * Real.pi) ^ 2 *
          ((e : ℝ) - (d : ℝ)) ^ 2 := by
        rw [frequency]
        ring
      _ ≤ (2 * Real.pi) ^ 2 * 81 :=
        mul_le_mul_of_nonneg_left hdiff_sq (sq_nonneg _)
      _ = 324 * Real.pi ^ 2 := by ring
  have hcos := Real.cos_le_one (frequency d e * x)
  have hmul := mul_le_mul_of_nonneg_right hcos (sq_nonneg (frequency d e))
  calc
    -(324 * Real.pi ^ 2) ≤ -(frequency d e ^ 2) := neg_le_neg hfreq_sq
    _ ≤ -(Real.cos (frequency d e * x) * frequency d e) * frequency d e := by
      nlinarith

private theorem kernelSqSecond_lower (a : Fin 10) (x : ℝ) :
    -(3200 : ℝ) ≤ kernelSqSecond a x := by
  let B : ℝ := 324 * Real.pi ^ 2
  have hinner (d : ℕ) (hd : d ∈ allowedDecimalDigits a) :
      -(9 * B) ≤ ∑ e ∈ allowedDecimalDigits a,
        (-(Real.cos (frequency d e * x) * frequency d e) * frequency d e) := by
    calc
      -(9 * B) = ∑ e ∈ allowedDecimalDigits a, -B := by
        rw [Finset.sum_const, allowedDecimalDigits_card]
        simp
      _ ≤ ∑ e ∈ allowedDecimalDigits a,
          (-(Real.cos (frequency d e * x) * frequency d e) * frequency d e) := by
        apply Finset.sum_le_sum
        intro e he
        exact kernelSqSecond_term_lower a x hd he
  have hsum : -(81 * B) ≤
      ∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
        (-(Real.cos (frequency d e * x) * frequency d e) * frequency d e) := by
    calc
      -(81 * B) = ∑ d ∈ allowedDecimalDigits a, -(9 * B) := by
        rw [Finset.sum_const, allowedDecimalDigits_card]
        simp
        ring
      _ ≤ ∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
          (-(Real.cos (frequency d e * x) * frequency d e) * frequency d e) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hinner d hd
  have hpi : 324 * Real.pi ^ 2 < (3200 : ℝ) := by
    nlinarith [Real.pi_lt_d6, Real.pi_pos]
  unfold kernelSqSecond
  calc
    -(3200 : ℝ) ≤ -B := by linarith
    _ = (1 / 81 : ℝ) * (-(81 * B)) := by ring
    _ ≤ (1 / 81 : ℝ) *
        (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
          (-(Real.cos (frequency d e * x) * frequency d e) * frequency d e)) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)

theorem iteratedDeriv_two_digitKernel_sq_lower (a : Fin 10) (x : ℝ) :
    -(3200 : ℝ) ≤
      (deriv^[2] (fun y : ℝ => digitKernel a y ^ 2)) x := by
  rw [iteratedDeriv_two_digitKernel_sq]
  exact kernelSqSecond_lower a x

private noncomputable def convexifiedKernelSq (a : Fin 10) (x : ℝ) : ℝ :=
  kernelSqCosine a x + 1600 * x ^ 2

private noncomputable def convexifiedKernelSqFirst (a : Fin 10) (x : ℝ) : ℝ :=
  kernelSqFirst a x + 3200 * x

private noncomputable def convexifiedKernelSqSecond (a : Fin 10) (x : ℝ) : ℝ :=
  kernelSqSecond a x + 3200

private theorem hasDerivAt_convexifiedKernelSq (a : Fin 10) (x : ℝ) :
    HasDerivAt (convexifiedKernelSq a) (convexifiedKernelSqFirst a x) x := by
  unfold convexifiedKernelSq convexifiedKernelSqFirst
  have hquad := (hasDerivAt_pow 2 x).const_mul (1600 : ℝ)
  have hquad' : HasDerivAt (fun y : ℝ => 1600 * y ^ 2) (3200 * x) x := by
    exact hquad.congr_deriv (by norm_num; ring)
  exact (hasDerivAt_kernelSqCosine a x).add hquad'

private theorem hasDerivAt_convexifiedKernelSqFirst (a : Fin 10) (x : ℝ) :
    HasDerivAt (convexifiedKernelSqFirst a) (convexifiedKernelSqSecond a x) x := by
  unfold convexifiedKernelSqFirst convexifiedKernelSqSecond
  exact (hasDerivAt_kernelSqFirst a x).add
    (hasDerivAt_const_mul (x := x) (3200 : ℝ))

theorem convexOn_digitKernel_sq_add_quadratic (a : Fin 10) :
    ConvexOn ℝ Set.univ
      (fun x : ℝ => digitKernel a x ^ 2 + 1600 * x ^ 2) := by
  have hconv : ConvexOn ℝ Set.univ (convexifiedKernelSq a) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    · exact (continuous_iff_continuousAt.2 fun x =>
        (hasDerivAt_convexifiedKernelSq a x).continuousAt).continuousOn
    · intro x hx
      exact (hasDerivAt_convexifiedKernelSq a x).hasDerivWithinAt
    · intro x hx
      exact (hasDerivAt_convexifiedKernelSqFirst a x).hasDerivWithinAt
    · intro x hx
      unfold convexifiedKernelSqSecond
      linarith [kernelSqSecond_lower a x]
  unfold convexifiedKernelSq at hconv
  rw [kernelSqCosine_eq] at hconv
  exact hconv

theorem digitKernel_sq_le_max_endpoints_add_curvature
    (a : Fin 10) {left right x : ℝ} (hx : x ∈ Set.Icc left right) :
    digitKernel a x ^ 2 ≤
      max (digitKernel a left ^ 2) (digitKernel a right ^ 2) +
        400 * (right - left) ^ 2 := by
  have hab : left ≤ right := le_trans hx.1 hx.2
  have hconv := (convexOn_digitKernel_sq_add_quadratic a).subset
    (Set.subset_univ (Set.Icc left right)) (convex_Icc left right)
  have hconv' : ConvexOn ℝ (Set.Icc left right)
      (fun y : ℝ => digitKernel a y ^ 2 + (3200 / 2) * y ^ 2) := by
    convert hconv using 1; norm_num
  have h := le_max_endpoints_add_curvature_of_convexOn
    (f := fun y : ℝ => digitKernel a y ^ 2) (a := left) (b := right)
    (x := x) (M := 3200) hab hx (by norm_num) hconv'
  nlinarith [h]

theorem digitKernel_sq_le_cell_endpoints (a : Fin 10) (left x : ℝ)
    (hx : x ∈ Set.Icc left (left + 1 / 100000)) :
    digitKernel a x ^ 2 ≤
      max (digitKernel a left ^ 2)
        (digitKernel a (left + 1 / 100000) ^ 2) + 1 / 25000000 := by
  have h := digitKernel_sq_le_max_endpoints_add_curvature a hx
  nlinarith [h]

theorem allowedDecimalDigits_diff_sq_sum_le (a : Fin 10) :
    (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
      ((e : ℝ) - (d : ℝ)) ^ 2) ≤ (1480 : ℝ) := by
  fin_cases a <;>
    norm_num [allowedDecimalDigits, Finset.sum_filter, Finset.sum_range_succ]

private theorem kernelSqSecond_term_lower_tight (a : Fin 10) (x : ℝ)
    {d e : ℕ} (_hd : d ∈ allowedDecimalDigits a)
    (_he : e ∈ allowedDecimalDigits a) :
    -(frequency d e) ^ 2 ≤
      -(Real.cos (frequency d e * x) * frequency d e) * frequency d e := by
  have hcos := Real.cos_le_one (frequency d e * x)
  have hmul := mul_le_mul_of_nonneg_right hcos (sq_nonneg (frequency d e))
  nlinarith

private theorem kernelSqSecond_lower_tight (a : Fin 10) (x : ℝ) :
    -(722 : ℝ) ≤ kernelSqSecond a x := by
  have hterms :
      (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
        -(frequency d e) ^ 2) ≤
        ∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
          (-(Real.cos (frequency d e * x) * frequency d e) * frequency d e) := by
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro e he
    exact kernelSqSecond_term_lower_tight a x hd he
  have hfreq :
      (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
        (frequency d e) ^ 2) ≤ 5920 * Real.pi ^ 2 := by
    calc
      (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
          (frequency d e) ^ 2) =
          4 * Real.pi ^ 2 *
            (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
              ((e : ℝ) - (d : ℝ)) ^ 2) := by
        simp_rw [show ∀ d e : ℕ,
            (frequency d e) ^ 2 =
              (4 * Real.pi ^ 2) * ((e : ℝ) - (d : ℝ)) ^ 2 by
          intro d e
          rw [frequency]
          ring]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mul_sum]
      _ ≤ 4 * Real.pi ^ 2 * 1480 :=
        mul_le_mul_of_nonneg_left (allowedDecimalDigits_diff_sq_sum_le a)
          (by positivity)
      _ = 5920 * Real.pi ^ 2 := by ring
  have hpi : 5920 * Real.pi ^ 2 < (722 : ℝ) * 81 := by
    nlinarith [Real.pi_lt_d6, Real.pi_pos]
  have hfreq' :
      (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
        (frequency d e) ^ 2) ≤ (722 : ℝ) * 81 :=
    hfreq.trans hpi.le
  unfold kernelSqSecond
  calc
    -(722 : ℝ) = (1 / 81 : ℝ) * (-((722 : ℝ) * 81)) := by ring
    _ ≤ (1 / 81 : ℝ) *
        (-∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
          (frequency d e) ^ 2) := by
      gcongr
    _ = (1 / 81 : ℝ) *
        (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
          -(frequency d e) ^ 2) := by
      congr 1
      simp_rw [Finset.sum_neg_distrib]
    _ ≤ (1 / 81 : ℝ) *
        (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
          (-(Real.cos (frequency d e * x) * frequency d e) * frequency d e)) := by
      gcongr

theorem iteratedDeriv_two_digitKernel_sq_lower_tight (a : Fin 10) (x : ℝ) :
    -(722 : ℝ) ≤
      (deriv^[2] (fun y : ℝ => digitKernel a y ^ 2)) x := by
  rw [iteratedDeriv_two_digitKernel_sq]
  exact kernelSqSecond_lower_tight a x

private noncomputable def tightConvexifiedKernelSq (a : Fin 10) (x : ℝ) : ℝ :=
  kernelSqCosine a x + 361 * x ^ 2

private noncomputable def tightConvexifiedKernelSqFirst (a : Fin 10) (x : ℝ) : ℝ :=
  kernelSqFirst a x + 722 * x

private noncomputable def tightConvexifiedKernelSqSecond (a : Fin 10) (x : ℝ) : ℝ :=
  kernelSqSecond a x + 722

private theorem hasDerivAt_tightConvexifiedKernelSq (a : Fin 10) (x : ℝ) :
    HasDerivAt (tightConvexifiedKernelSq a)
      (tightConvexifiedKernelSqFirst a x) x := by
  unfold tightConvexifiedKernelSq tightConvexifiedKernelSqFirst
  have hquad := (hasDerivAt_pow 2 x).const_mul (361 : ℝ)
  have hquad' : HasDerivAt (fun y : ℝ => 361 * y ^ 2) (722 * x) x := by
    exact hquad.congr_deriv (by norm_num; ring)
  exact (hasDerivAt_kernelSqCosine a x).add hquad'

private theorem hasDerivAt_tightConvexifiedKernelSqFirst
    (a : Fin 10) (x : ℝ) :
    HasDerivAt (tightConvexifiedKernelSqFirst a)
      (tightConvexifiedKernelSqSecond a x) x := by
  unfold tightConvexifiedKernelSqFirst tightConvexifiedKernelSqSecond
  exact (hasDerivAt_kernelSqFirst a x).add
    (hasDerivAt_const_mul (x := x) (722 : ℝ))

theorem convexOn_digitKernel_sq_add_tight_quadratic (a : Fin 10) :
    ConvexOn ℝ Set.univ
      (fun x : ℝ => digitKernel a x ^ 2 + 361 * x ^ 2) := by
  have hconv : ConvexOn ℝ Set.univ (tightConvexifiedKernelSq a) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    · exact (continuous_iff_continuousAt.2 fun x =>
        (hasDerivAt_tightConvexifiedKernelSq a x).continuousAt).continuousOn
    · intro x hx
      exact (hasDerivAt_tightConvexifiedKernelSq a x).hasDerivWithinAt
    · intro x hx
      exact (hasDerivAt_tightConvexifiedKernelSqFirst a x).hasDerivWithinAt
    · intro x hx
      unfold tightConvexifiedKernelSqSecond
      linarith [kernelSqSecond_lower_tight a x]
  unfold tightConvexifiedKernelSq at hconv
  rw [kernelSqCosine_eq] at hconv
  exact hconv

theorem digitKernel_sq_le_max_endpoints_add_tight_curvature
    (a : Fin 10) {left right x : ℝ} (hx : x ∈ Set.Icc left right) :
    digitKernel a x ^ 2 ≤
      max (digitKernel a left ^ 2) (digitKernel a right ^ 2) +
        (361 / 4 : ℝ) * (right - left) ^ 2 := by
  have hab : left ≤ right := le_trans hx.1 hx.2
  have hconv := (convexOn_digitKernel_sq_add_tight_quadratic a).subset
    (Set.subset_univ (Set.Icc left right)) (convex_Icc left right)
  have hconv' : ConvexOn ℝ (Set.Icc left right)
      (fun y : ℝ => digitKernel a y ^ 2 + (722 / 2) * y ^ 2) := by
    convert hconv using 1; norm_num
  have h := le_max_endpoints_add_curvature_of_convexOn
    (f := fun y : ℝ => digitKernel a y ^ 2) (a := left) (b := right)
    (x := x) (M := 722) hab hx (by norm_num) hconv'
  nlinarith [h]

theorem digitKernel_sq_le_cell_endpoints_tight (a : Fin 10) (left x : ℝ)
    (hx : x ∈ Set.Icc left (left + 1 / 100000)) :
    digitKernel a x ^ 2 ≤
      max (digitKernel a left ^ 2)
        (digitKernel a (left + 1 / 100000) ^ 2) +
        361 / 40000000000 := by
  have h := digitKernel_sq_le_max_endpoints_add_tight_curvature a hx
  nlinarith [h]

end PrimesRestrictedDigits
