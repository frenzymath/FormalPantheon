import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# A generic logarithmic-derivative Perron contour

This file isolates the analytic rectangle identity used in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.16, pp. 378--379. If a
function is analytic and nonzero throughout a closed rectangle in the positive
half-plane, its logarithmic-derivative Perron integrand has zero boundary
integral.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/-- The logarithmic-derivative Perron integrand attached to `f`. -/
noncomputable def logDerivPerronIntegrand
    (f : Complex -> Complex) (x : Real) (s : Complex) : Complex :=
  (-logDeriv f s) * ((x : Complex) ^ s / s)

/-- A left-to-right horizontal integral of a logarithmic-derivative Perron
integrand. -/
noncomputable def logDerivPerronHorizontalIntegral
    (f : Complex -> Complex) (x sigma1 sigma0 t : Real) : Complex :=
  ∫ r in sigma1..sigma0,
    logDerivPerronIntegrand f x
      ((r : Complex) + Complex.I * (t : Complex))

/-- An upward vertical integral of a logarithmic-derivative Perron integrand. -/
noncomputable def logDerivPerronVerticalIntegral
    (f : Complex -> Complex) (x sigma T : Real) : Complex :=
  ∫ t in -T..T,
    logDerivPerronIntegrand f x
      ((sigma : Complex) + Complex.I * (t : Complex))

private theorem differentiableOn_logDerivPerronIntegrand
    {f : Complex -> Complex} {x sigma1 sigma0 T : Real}
    (hx : 0 < x) (hsigma1Pos : 0 < sigma1)
    (hf : AnalyticOnNhd Complex f
      (Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T))
    (hzero : forall s,
      s ∈ Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T -> f s ≠ 0) :
    DifferentiableOn Complex (logDerivPerronIntegrand f x)
      (Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T) := by
  let R : Set Complex := Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T
  have hLogDeriv : AnalyticOnNhd Complex (logDeriv f) R := by
    change AnalyticOnNhd Complex (fun s => deriv f s / f s) R
    exact hf.deriv.div hf hzero
  have hQuotient : DifferentiableOn Complex
      (fun s : Complex => (x : Complex) ^ s / s) R := by
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply (differentiableAt_id.const_cpow
      (.inl <| Complex.ofReal_ne_zero.mpr hx.ne')).div differentiableAt_id
    intro hsZero
    have hRe := congrArg Complex.re hsZero
    rw [Complex.mem_reProdIm] at hs
    simp at hRe
    linarith [hs.1.1]
  exact hLogDeriv.differentiableOn.neg.mul hQuotient

/-- The counterclockwise boundary integral of a logarithmic-derivative Perron
integrand vanishes on a positive-real rectangle where the underlying function
is analytic and nonzero. -/
theorem logDerivPerron_boundary_eq_zero
    {f : Complex -> Complex} {x sigma1 sigma0 T : Real}
    (hx : 0 < x) (hsigma1Pos : 0 < sigma1)
    (hsigma : sigma1 <= sigma0) (hT : 0 < T)
    (hf : AnalyticOnNhd Complex f
      (Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T))
    (hzero : forall s,
      s ∈ Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T -> f s ≠ 0) :
    logDerivPerronHorizontalIntegral f x sigma1 sigma0 (-T) -
        logDerivPerronHorizontalIntegral f x sigma1 sigma0 T +
        Complex.I * logDerivPerronVerticalIntegral f x sigma0 T -
        Complex.I * logDerivPerronVerticalIntegral f x sigma1 T = 0 := by
  have hDifferentiable :=
    differentiableOn_logDerivPerronIntegrand hx hsigma1Pos hf hzero
  simpa only [logDerivPerronHorizontalIntegral,
    logDerivPerronVerticalIntegral, Complex.ofReal_neg, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_ofNat, mul_comm] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (logDerivPerronIntegrand f x)
      (Complex.mk sigma1 (-T)) (Complex.mk sigma0 T) (by
        simpa only [uIcc_of_le hsigma,
          uIcc_of_le (by linarith : -T <= T)] using hDifferentiable)

end PrimesRestrictedDigits
