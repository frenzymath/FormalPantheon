import PrimesRestrictedDigits.PrimeNumberTheorem.LogDerivPerronPoleContour
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronVonMangoldt
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronContourParameters

/-!
# The exact zeta Perron contour

This module proves the residue identity used in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Theorem 6.9, p. 181.  The pole at one
is separated explicitly; Cauchy's rectangle theorem is applied only to a
differentiable regularized integrand.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/-- The zeta logarithmic-derivative integrand before vertical
parametrization. -/
noncomputable def zetaPerronIntegrand (x : Real) (s : Complex) : Complex :=
  (-logDeriv riemannZeta s) * ((x : Complex) ^ s / s)

/-- A horizontal edge of the zeta Perron rectangle. -/
noncomputable def zetaPerronHorizontalIntegral
    (x sigma1 sigma0 t : Real) : Complex :=
  ∫ r in sigma1..sigma0,
    zetaPerronIntegrand x ((r : Complex) + Complex.I * t)

/-- An upward vertical edge of the zeta Perron rectangle. -/
noncomputable def zetaPerronVerticalIntegral
    (x sigma T : Real) : Complex :=
  ∫ t in -T..T,
    zetaPerronIntegrand x ((sigma : Complex) + Complex.I * t)

private theorem zetaPerron_boundary_eq_of_nonzero
    {x sigma1 sigma0 T : Real} (hx : 0 < x) (hsigma1Pos : 0 < sigma1)
    (hsigma1 : sigma1 < 1) (hsigma0 : 1 < sigma0) (hT : 0 < T)
    (hNonzero : forall s : Complex,
      s ∈ Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T ->
        regularizedRiemannZeta s ≠ 0) :
    zetaPerronHorizontalIntegral x sigma1 sigma0 (-T) -
        zetaPerronHorizontalIntegral x sigma1 sigma0 T +
        Complex.I * zetaPerronVerticalIntegral x sigma0 T -
        Complex.I * zetaPerronVerticalIntegral x sigma1 T =
      ((2 * Real.pi : Real) : Complex) * Complex.I * x := by
  have hAnalytic : AnalyticOnNhd Complex regularizedRiemannZeta
      (Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T) :=
    analyticOnNhd_regularizedRiemannZeta.mono (Set.subset_univ _)
  have hrel : forall s,
      s ∈ Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T -> s ≠ 1 ->
        -logDeriv riemannZeta s =
          -logDeriv regularizedRiemannZeta s + 1 / (s - 1) := by
    intro s hs hsOne
    have hZeta : riemannZeta s ≠ 0 := by
      intro hZeta
      apply hNonzero s hs
      rw [regularizedRiemannZeta_apply_of_ne hsOne, hZeta, mul_zero]
    rw [logDeriv_regularizedRiemannZeta_eq hsOne hZeta]
    ring
  simpa only [zetaPerronHorizontalIntegral, zetaPerronVerticalIntegral,
    zetaPerronIntegrand, logDerivPerronHorizontalIntegral,
    logDerivPerronVerticalIntegral, logDerivPerronIntegrand] using
    (logDerivPerron_boundary_eq_residue
      (f := riemannZeta) (g := regularizedRiemannZeta) hx hsigma1Pos
      hsigma1 hsigma0 hT hAnalytic hNonzero hrel)

/-- The exact counterclockwise zeta Perron boundary has the residue
`2 * pi * I * x` at one. -/
theorem zetaPerron_boundary_eq
    {c x sigma0 T : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hx : 0 < x) (hsigma0 : 1 < sigma0) (hT : 0 < T) :
    zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T) sigma0 (-T) -
        zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T) sigma0 T +
        Complex.I * zetaPerronVerticalIntegral x sigma0 T -
        Complex.I * zetaPerronVerticalIntegral x
          (zetaPerronLeftLine c T) T =
      ((2 * Real.pi : Real) : Complex) * Complex.I * x := by
  apply zetaPerron_boundary_eq_of_nonzero hx
    (zetaPerronLeftLine_pos hc hT)
    (zetaPerronLeftLine_lt_one hc hT) hsigma0 hT
  exact regularizedRiemannZeta_ne_zero_on_perronRectangle hc hT

/-- Solving the exact boundary identity for the original right edge gives
the two horizontal edges and the upward left edge with their exact signs. -/
theorem zetaPerronIntegral_sub_self_eq_edges
    {c x sigma0 T : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hx : 0 < x) (hsigma0 : 1 < sigma0) (hT : 0 < T) :
    zetaPerronIntegral x sigma0 T - (x : Complex) =
      ((1 / (2 * Real.pi) : Real) : Complex) *
        (Complex.I *
            (zetaPerronHorizontalIntegral x
                (zetaPerronLeftLine c T) sigma0 (-T) -
              zetaPerronHorizontalIntegral x
                (zetaPerronLeftLine c T) sigma0 T) +
          zetaPerronVerticalIntegral x (zetaPerronLeftLine c T) T) := by
  have hBoundary := zetaPerron_boundary_eq hc hx hsigma0 hT
  have hVertical : zetaPerronIntegral x sigma0 T =
      ((1 / (2 * Real.pi) : Real) : Complex) *
        zetaPerronVerticalIntegral x sigma0 T := by
    rw [zetaPerronIntegral, zetaPerronVerticalIntegral]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [zetaPerronIntegrand, div_eq_mul_inv, mul_assoc]
  rw [hVertical]
  have hIRight :
      Complex.I * zetaPerronVerticalIntegral x sigma0 T =
        ((2 * Real.pi : Real) : Complex) * Complex.I * x -
            (zetaPerronHorizontalIntegral x
                (zetaPerronLeftLine c T) sigma0 (-T) -
              zetaPerronHorizontalIntegral x
                (zetaPerronLeftLine c T) sigma0 T) +
          Complex.I * zetaPerronVerticalIntegral x
            (zetaPerronLeftLine c T) T := by
    linear_combination hBoundary
  have hSolvedRaw := congrArg (fun z : Complex => -Complex.I * z) hIRight
  ring_nf at hSolvedRaw
  rw [Complex.I_sq] at hSolvedRaw
  ring_nf at hSolvedRaw
  have hSolved :
      zetaPerronVerticalIntegral x sigma0 T -
          ((2 * Real.pi : Real) : Complex) * x =
        Complex.I *
            (zetaPerronHorizontalIntegral x
                (zetaPerronLeftLine c T) sigma0 (-T) -
              zetaPerronHorizontalIntegral x
                (zetaPerronLeftLine c T) sigma0 T) +
          zetaPerronVerticalIntegral x (zetaPerronLeftLine c T) T := by
    rw [show ((2 * Real.pi : Real) : Complex) =
        ((Real.pi * 2 : Real) : Complex) by ring_nf]
    linear_combination hSolvedRaw
  have hReciprocal :
      ((1 / (2 * Real.pi) : Real) : Complex) *
          ((2 * Real.pi : Real) : Complex) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  calc
    ((1 / (2 * Real.pi) : Real) : Complex) *
          zetaPerronVerticalIntegral x sigma0 T - (x : Complex) =
        ((1 / (2 * Real.pi) : Real) : Complex) *
          (zetaPerronVerticalIntegral x sigma0 T -
            ((2 * Real.pi : Real) : Complex) * x) := by
      rw [mul_sub, ← mul_assoc, hReciprocal, one_mul]
    _ = _ := by rw [hSolved]

end PrimesRestrictedDigits
