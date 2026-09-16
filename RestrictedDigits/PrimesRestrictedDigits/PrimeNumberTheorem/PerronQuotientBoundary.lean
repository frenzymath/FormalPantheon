import PrimesRestrictedDigits.PrimeNumberTheorem.PerronPoleBoundary

/-!
# The symmetric Perron quotient boundary

This combines the entire positive-base Perron quotient with the separated
simple-pole boundary used in `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5,
Eq. (5.9), pp. 139--140.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private noncomputable def perronQuotientIntegrand
    (y : Real) (s : Complex) : Complex :=
  (y : Complex) ^ s / s

private theorem intervalIntegral_perronQuotient_split
    {y a b : Real} (hy : 0 < y) (path : Real → Complex)
    (hpath : Continuous path) (hne : ∀ t, path t ≠ 0) :
    (∫ t in a..b, perronQuotientIntegrand y (path t)) =
      (∫ t in a..b, perronRegularizedCpow y (path t)) +
        ∫ t in a..b, (1 : Complex) / path t := by
  have hR : Continuous (fun t => perronRegularizedCpow y (path t)) :=
    (differentiable_perronRegularizedCpow hy).continuous.comp hpath
  have hInv : Continuous (fun t => (1 : Complex) / path t) := by
    exact continuous_const.div₀ hpath fun t ht => hne t ht
  rw [show (fun t => perronQuotientIntegrand y (path t)) =
      fun t => perronRegularizedCpow y (path t) + (1 : Complex) / path t by
    funext t
    exact perronCpow_div_eq_regularized_add_inv hy (hne t)]
  exact intervalIntegral.integral_add
    (hR.intervalIntegrable a b) (hInv.intervalIntegrable a b)

/-- The entire part of Perron's quotient has zero boundary integral on the
symmetric rectangle. -/
theorem perronRegularized_symmetric_boundary_eq_zero
    {y sigma T : Real} (hy : 0 < y) :
    (∫ r in -sigma..sigma,
          perronRegularizedCpow y ((r : Complex) + (-T : Real) * Complex.I)) -
        (∫ r in -sigma..sigma,
          perronRegularizedCpow y ((r : Complex) + (T : Real) * Complex.I)) +
        Complex.I * (∫ t in -T..T,
          perronRegularizedCpow y ((sigma : Complex) + Complex.I * t)) -
        Complex.I * (∫ t in -T..T,
          perronRegularizedCpow y ((-sigma : Complex) + Complex.I * t)) = 0 := by
  simpa only [Complex.ofReal_neg, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_ofNat, mul_comm] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (perronRegularizedCpow y) (Complex.mk (-sigma) (-T)) (Complex.mk sigma T)
      (differentiable_perronRegularizedCpow hy).differentiableOn

private theorem perronQuotient_symmetric_boundary_eq_aux
    {y sigma T : Real} (hy : 0 < y) (hsigma : 0 < sigma) (hT : 0 < T) :
    (∫ r in -sigma..sigma,
          perronQuotientIntegrand y
            ((r : Complex) + (-T : Real) * Complex.I)) -
        (∫ r in -sigma..sigma,
          perronQuotientIntegrand y
            ((r : Complex) + (T : Real) * Complex.I)) +
        Complex.I * (∫ t in -T..T,
          perronQuotientIntegrand y
            ((sigma : Complex) + Complex.I * t)) -
        Complex.I * (∫ t in -T..T,
          perronQuotientIntegrand y
            ((-sigma : Complex) + Complex.I * t)) =
      ((2 * Real.pi : Real) : Complex) * Complex.I := by
  have hbottom := intervalIntegral_perronQuotient_split
    (a := -sigma) (b := sigma) hy
    (fun r : Real => (r : Complex) + (-T : Real) * Complex.I) (by fun_prop) (by
      intro r hr
      have him := congrArg Complex.im hr
      simp at him
      linarith)
  have htop := intervalIntegral_perronQuotient_split
    (a := -sigma) (b := sigma) hy
    (fun r : Real => (r : Complex) + (T : Real) * Complex.I) (by fun_prop) (by
      intro r hr
      have him := congrArg Complex.im hr
      simp at him
      linarith)
  have hright := intervalIntegral_perronQuotient_split
    (a := -T) (b := T) hy
    (fun t : Real => (sigma : Complex) + Complex.I * t) (by fun_prop) (by
      intro t ht
      have hre := congrArg Complex.re ht
      simp at hre
      linarith)
  have hleft := intervalIntegral_perronQuotient_split
    (a := -T) (b := T) hy
    (fun t : Real => (-sigma : Complex) + Complex.I * t) (by fun_prop) (by
      intro t ht
      have hre := congrArg Complex.re ht
      simp at hre
      linarith)
  have hreg := perronRegularized_symmetric_boundary_eq_zero
    (y := y) (sigma := sigma) (T := T) hy
  have hinv := inverse_symmetric_boundary_eq_two_pi_mul_I hsigma hT
  rw [hbottom, htop, hright, hleft]
  linear_combination hreg + hinv

/-- The original quotient has residue-one boundary on the symmetric rectangle.
Every boundary point is nonzero, and the pole is handled only through the
separated identities above. See `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5,
Eq. (5.9), pp. 139--140. -/
theorem perronQuotient_symmetric_boundary_eq
    {y sigma T : Real} (hy : 0 < y) (hsigma : 0 < sigma) (hT : 0 < T) :
    (∫ r in -sigma..sigma,
          (y : Complex) ^ ((r : Complex) + (-T : Real) * Complex.I) /
            ((r : Complex) + (-T : Real) * Complex.I)) -
        (∫ r in -sigma..sigma,
          (y : Complex) ^ ((r : Complex) + (T : Real) * Complex.I) /
            ((r : Complex) + (T : Real) * Complex.I)) +
        Complex.I * (∫ t in -T..T,
          (y : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t)) -
        Complex.I * (∫ t in -T..T,
          (y : Complex) ^ ((-sigma : Complex) + Complex.I * t) /
            ((-sigma : Complex) + Complex.I * t)) =
      ((2 * Real.pi : Real) : Complex) * Complex.I := by
  simpa only [perronQuotientIntegrand] using
    perronQuotient_symmetric_boundary_eq_aux hy hsigma hT

end PrimesRestrictedDigits
