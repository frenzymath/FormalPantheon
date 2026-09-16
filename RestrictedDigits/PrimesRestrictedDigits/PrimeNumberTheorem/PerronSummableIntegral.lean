import PrimesRestrictedDigits.PrimeNumberTheorem.PerronFiniteIntegral
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronSummableSupport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The summable Dirichlet-series Perron integral

This file applies dominated convergence to identify the source vertical
integral in `MONTGOMERY-VAUGHAN-MNT-I`, Theorem 5.2, pp. 139--140, with its
countable sum of one-term Perron kernels.
-/

open Complex MeasureTheory
open scoped Interval

namespace PrimesRestrictedDigits

/-- The source vertical integral for an L-series, after parametrizing
`s = sigma + I * t`. -/
noncomputable def truncatedPerronIntegral
    (a : Nat -> Complex) (x sigma T : Real) : Complex :=
  ((1 / (2 * Real.pi) : Real) : Complex) *
    ∫ t in -T..T,
      LSeries a ((sigma : Complex) + Complex.I * t) *
        (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)

private lemma perronLine_ne_zero
    {sigma : Real} (hsigma : 0 < sigma) (t : Real) :
    (sigma : Complex) + Complex.I * t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  exact hsigma.ne' hre

private lemma sigma_le_norm_perronLine
    {sigma : Real} (hsigma : 0 < sigma) (t : Real) :
    sigma <= ‖(sigma : Complex) + Complex.I * t‖ := by
  have h := Complex.abs_re_le_norm ((sigma : Complex) + Complex.I * t)
  simpa [abs_of_pos hsigma] using h

private lemma perronTermIntegrand_continuous
    {a : Nat -> Complex} {x sigma : Real} (hx : 0 < x)
    (hsigma : 0 < sigma) (n : Nat) :
    Continuous (fun t : Real =>
      LSeries.term a ((sigma : Complex) + Complex.I * t) n *
        (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)) := by
  by_cases hn : n = 0
  · subst n
    simpa using (continuous_const : Continuous (fun _ : Real => (0 : Complex)))
  · have hnC : (n : Complex) ≠ 0 := by exact_mod_cast hn
    have hline : Continuous (fun t : Real =>
        (sigma : Complex) + Complex.I * t) := by fun_prop
    have hnpow : Continuous (fun t : Real =>
        (n : Complex) ^ ((sigma : Complex) + Complex.I * t)) :=
      (differentiable_id.const_cpow (.inl hnC)).continuous.comp hline
    have hnpowne : forall t : Real,
        (n : Complex) ^ ((sigma : Complex) + Complex.I * t) ≠ 0 := by
      intro t
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    have hxpow : Continuous (fun t : Real =>
        (x : Complex) ^ ((sigma : Complex) + Complex.I * t)) :=
      (differentiable_id.const_cpow
        (.inl <| Complex.ofReal_ne_zero.mpr hx.ne')).continuous.comp hline
    simp only [LSeries.term_of_ne_zero hn]
    exact ((continuous_const.div₀ hnpow hnpowne).mul hxpow).div₀ hline
      (perronLine_ne_zero hsigma)

private lemma norm_perronTermIntegrand_le
    {a : Nat -> Complex} {x sigma : Real} (hx : 0 < x)
    (hsigma : 0 < sigma) (n : Nat) (t : Real) :
    ‖LSeries.term a ((sigma : Complex) + Complex.I * t) n *
        (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)‖ <=
      ‖LSeries.term a (sigma : Complex) n‖ * x ^ sigma / sigma := by
  rw [norm_div, norm_mul, LSeries.norm_term_eq, LSeries.norm_term_eq,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul,
    one_mul, sub_self, add_zero]
  exact div_le_div_of_nonneg_left (mul_nonneg (by positivity) (by positivity))
    hsigma (sigma_le_norm_perronLine hsigma t)

/-- Dominated convergence interchanges an absolutely convergent L-series with
the finite vertical interval integral. -/
theorem hasSum_intervalIntegral_lSeriesTerm
    {a : Nat -> Complex} {x sigma T : Real}
    (hx : 0 < x) (hsigma : 0 < sigma)
    (hsum : LSeriesSummable a (sigma : Complex)) :
    HasSum
      (fun n => ∫ t in -T..T,
        LSeries.term a ((sigma : Complex) + Complex.I * t) n *
          (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t))
      (∫ t in -T..T,
        LSeries a ((sigma : Complex) + Complex.I * t) *
          (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : Real) =>
      ‖LSeries.term a (sigma : Complex) n‖ * x ^ sigma / sigma)
  · intro n
    exact (perronTermIntegrand_continuous hx hsigma n).aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall fun t _ =>
      norm_perronTermIntegrand_le hx hsigma n t
  · exact Filter.Eventually.of_forall fun _ _ =>
      (hsum.norm.mul_right (x ^ sigma / sigma)).congr fun n => by ring
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t _ => by
      have hline : LSeriesSummable a
          ((sigma : Complex) + Complex.I * t) :=
        LSeriesSummable.of_re_le_re (by simp) hsum
      simpa [div_eq_mul_inv, mul_assoc] using
        hline.LSeriesHasSum.mul_right
          ((x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t))

private theorem normalized_perronTermIntegral_eq
    {a : Nat -> Complex} {x sigma T : Real} (hx : 0 < x)
    (hsigma : 0 < sigma) (n : Nat) :
    ((1 / (2 * Real.pi) : Real) : Complex) *
        (∫ t in -T..T,
          LSeries.term a ((sigma : Complex) + Complex.I * t) n *
            (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
              ((sigma : Complex) + Complex.I * t)) =
      perronKernelTerm a x sigma T n := by
  by_cases hn : n = 0
  · subst n
    simp [perronKernelTerm]
  · have h := finitePerronIntegral_eq_sum_perronKernel
      (S := {n}) (a := a) (x := x) (sigma := sigma) (T := T)
      (fun m hm => by
        simp only [Finset.mem_singleton] at hm
        subst m
        exact Nat.pos_of_ne_zero hn) hx hsigma
    simpa [finitePerronIntegral, perronKernelTerm, hn] using h

/-- The guarded one-term Perron kernels sum to the source vertical integral. -/
theorem hasSum_perronKernelTerm_truncatedPerronIntegral
    {a : Nat -> Complex} {x sigma T : Real}
    (hsum : LSeriesSummable a (sigma : Complex))
    (hx : 0 < x) (hsigma : 0 < sigma) :
    HasSum (perronKernelTerm a x sigma T)
      (truncatedPerronIntegral a x sigma T) := by
  have h := (hasSum_intervalIntegral_lSeriesTerm (T := T) hx hsigma hsum).mul_left
    (((1 / (2 * Real.pi) : Real) : Complex))
  exact HasSum.congr_fun h fun n =>
    (normalized_perronTermIntegral_eq hx hsigma n).symm

/-- The source vertical integral is exactly the countable sum of guarded
one-term Perron kernels. -/
theorem truncatedPerronIntegral_eq_tsum_perronKernel
    {a : Nat -> Complex} {x sigma T : Real}
    (hsum : LSeriesSummable a (sigma : Complex))
    (hx : 0 < x) (hsigma : 0 < sigma) :
    truncatedPerronIntegral a x sigma T =
      ∑' n, perronKernelTerm a x sigma T n :=
  (hasSum_perronKernelTerm_truncatedPerronIntegral hsum hx hsigma).tsum_eq.symm

end PrimesRestrictedDigits
