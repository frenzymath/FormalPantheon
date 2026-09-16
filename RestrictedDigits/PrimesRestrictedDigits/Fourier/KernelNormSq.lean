import PrimesRestrictedDigits.Fourier.DigitKernel
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Ring

/-!
# Kernel norm-square expansion

The squared finite digit kernel is an exact finite double cosine sum. This is
the algebraic input for later Taylor and interval certificates.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem complexNormSq_sum_double {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, z i) =
      ∑ i ∈ s, ∑ j ∈ s, ((starRingEnd ℂ) (z i) * z j).re := by
  rw [Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
  simp only [Finset.sum_mul_sum]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp only [neg_mul, neg_neg, sub_eq_add_neg]
  simp_rw [Finset.sum_add_distrib]

theorem expNormSq_sum_double {ι : Type*} (s : Finset ι) (values : ι → ℝ) :
    Complex.normSq (∑ i ∈ s, Complex.exp ((values i : ℂ) * Complex.I)) =
      ∑ i ∈ s, ∑ j ∈ s, Real.cos (values j - values i) := by
  rw [complexNormSq_sum_double]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have harg :
      (starRingEnd ℂ) ((values i : ℂ) * Complex.I) +
          (values j : ℂ) * Complex.I =
        ((values j - values i : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
      ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

theorem digitKernel_sq_eq_cos_sum (a : Fin 10) (x : ℝ) :
    digitKernel a x ^ 2 =
      (1 / 81 : ℝ) *
        ∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
          Real.cos (2 * Real.pi * ((e : ℝ) - (d : ℝ)) * x) := by
  unfold digitKernel
  have hnorm :
      ‖∑ d ∈ allowedDecimalDigits a,
          Complex.exp (((2 * Real.pi * (d : ℝ) * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
        Complex.normSq (∑ d ∈ allowedDecimalDigits a,
          Complex.exp (((2 * Real.pi * (d : ℝ) * x : ℝ) : ℂ) * Complex.I)) :=
    Complex.sq_norm _
  rw [show ((1 / 9 : ℝ) *
      ‖∑ d ∈ allowedDecimalDigits a,
          Complex.exp (((2 * Real.pi * (d : ℝ) * x : ℝ) : ℂ) * Complex.I)‖) ^ 2 =
      (1 / 81 : ℝ) * ‖∑ d ∈ allowedDecimalDigits a,
          Complex.exp (((2 * Real.pi * (d : ℝ) * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 by
        ring]
  rw [hnorm, expNormSq_sum_double]
  apply congrArg (fun y : ℝ => (1 / 81 : ℝ) * y) ?_
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  ring

end PrimesRestrictedDigits
