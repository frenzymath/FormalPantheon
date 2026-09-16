import PrimesRestrictedDigits.PrimeNumberTheorem.PerronKernel
import Mathlib.NumberTheory.LSeries.Basic

/-!
# The finite Dirichlet-series Perron integral

This file identifies the finite vertical integral in
`MONTGOMERY-VAUGHAN-MNT-I`, Theorem 5.2, pp. 139--140, with the sum of its
one-term Perron kernels.
-/

open Complex MeasureTheory
open scoped Interval

namespace PrimesRestrictedDigits

/-- The source vertical integral for a finite set of Dirichlet coefficients,
after parametrizing `s = sigma + I * t`. -/
noncomputable def finitePerronIntegral
    (S : Finset Nat) (a : Nat -> Complex) (x sigma T : Real) : Complex :=
  ((1 / (2 * Real.pi) : Real) : Complex) *
    ∫ t in -T..T,
      (∑ n ∈ S, LSeries.term a ((sigma : Complex) + Complex.I * t) n) *
        (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)

private theorem lSeriesTerm_mul_cpow_eq
    {a : Nat -> Complex} {x : Real} {s : Complex} {n : Nat}
    (hx : 0 < x) (hn : 0 < n) :
    LSeries.term a s n * (x : Complex) ^ s =
      a n * ((x / (n : Real) : Real) : Complex) ^ s := by
  have hn' : (0 : Real) < n := by exact_mod_cast hn
  have hnC : (((n : Real) : Complex)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hn'.ne'
  have hnpow : ((n : Real) : Complex) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  have hbase : ((x / (n : Real) : Real) : Complex) *
      ((n : Real) : Complex) = (x : Complex) := by
    exact_mod_cast div_mul_cancel₀ x hn'.ne'
  have hmul : ((x / (n : Real) : Real) : Complex) ^ s *
      ((n : Real) : Complex) ^ s =
      (x : Complex) ^ s := by
    rw [← Complex.mul_cpow_ofReal_nonneg
      (div_nonneg hx.le hn'.le) hn'.le, hbase]
  have hdiv : (x : Complex) ^ s / ((n : Real) : Complex) ^ s =
      ((x / (n : Real) : Real) : Complex) ^ s :=
    (div_eq_iff hnpow).2 hmul.symm
  rw [LSeries.term_of_ne_zero hn.ne']
  change a n / ((n : Real) : Complex) ^ s * (x : Complex) ^ s = _
  calc
    a n / ((n : Real) : Complex) ^ s * (x : Complex) ^ s =
        a n * ((x : Complex) ^ s / ((n : Real) : Complex) ^ s) := by ring
    _ = a n * ((x / (n : Real) : Real) : Complex) ^ s := by rw [hdiv]

/-- For positive finite support, the source vertical integral is exactly the
sum of the normalized one-term kernels. -/
theorem finitePerronIntegral_eq_sum_perronKernel
    {S : Finset Nat} {a : Nat -> Complex} {x sigma T : Real}
    (hS : forall n, n ∈ S -> 0 < n) (hx : 0 < x) (hsigma : 0 < sigma) :
    finitePerronIntegral S a x sigma T =
      ∑ n ∈ S, a n * perronKernel (x / (n : Real)) sigma T := by
  have hpoint (t : Real) :
      (∑ n ∈ S, LSeries.term a ((sigma : Complex) + Complex.I * t) n) *
          (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t) =
        ∑ n ∈ S, a n *
          (((x / (n : Real) : Real) : Complex) ^
            ((sigma : Complex) + Complex.I * t) /
              ((sigma : Complex) + Complex.I * t)) := by
    rw [Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hnS
    rw [lSeriesTerm_mul_cpow_eq hx (hS n hnS)]
    ring
  have hinterm (n : Nat) (hnS : n ∈ S) : IntervalIntegrable
      (fun t : Real => a n *
        (((x / (n : Real) : Real) : Complex) ^
          ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t))) volume (-T) T := by
    have hn' : (0 : Real) < n := by exact_mod_cast hS n hnS
    have hbase : (0 : Real) < x / (n : Real) := div_pos hx hn'
    have hpow : Continuous (fun t : Real =>
        (((x / (n : Real) : Real) : Complex) ^
          ((sigma : Complex) + Complex.I * t))) :=
      (differentiable_id.const_cpow
        (.inl <| Complex.ofReal_ne_zero.mpr hbase.ne')).continuous.comp (by
          fun_prop)
    have hden : Continuous (fun t : Real =>
        (sigma : Complex) + Complex.I * t) := by fun_prop
    have hdenne : forall t : Real,
        (sigma : Complex) + Complex.I * t ≠ 0 := by
      intro t ht
      have hre := congrArg Complex.re ht
      simp at hre
      exact hsigma.ne' hre
    exact (continuous_const.mul (hpow.div₀ hden hdenne)).intervalIntegrable _ _
  rw [finitePerronIntegral]
  have hintegral :
      (∫ t in -T..T,
        (∑ n ∈ S, LSeries.term a ((sigma : Complex) + Complex.I * t) n) *
          (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t)) =
        ∫ t in -T..T, ∑ n ∈ S, a n *
          (((x / (n : Real) : Real) : Complex) ^
            ((sigma : Complex) + Complex.I * t) /
              ((sigma : Complex) + Complex.I * t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hpoint t
  rw [hintegral]
  rw [intervalIntegral.integral_finsetSum (fun n hnS => hinterm n hnS)]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hnS
  rw [perronKernel]
  ring

end PrimesRestrictedDigits
