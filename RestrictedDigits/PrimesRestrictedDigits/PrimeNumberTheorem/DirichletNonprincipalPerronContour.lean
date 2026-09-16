import PrimesRestrictedDigits.PrimeNumberTheorem.LogDerivPerronContour
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronContourParameters
import PrimesRestrictedDigits.PrimeNumberTheorem.TwistedPerron

/-!
# The exact nonprincipal Dirichlet Perron contour

This module proves the zero-residue contour identity from
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.16, pp. 378--379, for the
decimal-smooth nonprincipal family. Quantitative edge estimates are kept in a
separate downstream slice.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/-- A left-to-right horizontal edge of the Dirichlet Perron rectangle. -/
noncomputable def dirichletPerronHorizontalIntegral
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (x sigma1 sigma0 t : Real) : Complex :=
  logDerivPerronHorizontalIntegral chi.LFunction x sigma1 sigma0 t

/-- An upward vertical edge of the Dirichlet Perron rectangle. -/
noncomputable def dirichletPerronVerticalIntegral
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (x sigma T : Real) : Complex :=
  logDerivPerronVerticalIntegral chi.LFunction x sigma T

/-- The exact counterclockwise boundary of the nonprincipal Dirichlet Perron
integrand vanishes on the factor-five rectangle. -/
theorem dirichletPerron_boundary_eq_zero
    {c : Real}
    (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c)
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hSmooth : IsDecimalSmooth q) (hchi : chi ≠ 1)
    {x sigma0 T : Real} (hx : 0 < x) (hsigma0 : 1 < sigma0)
    (hT : 0 < T) :
    dirichletPerronHorizontalIntegral chi x
          (dirichletPerronLeftLine c q T) sigma0 (-T) -
        dirichletPerronHorizontalIntegral chi x
          (dirichletPerronLeftLine c q T) sigma0 T +
        Complex.I * dirichletPerronVerticalIntegral chi x sigma0 T -
        Complex.I * dirichletPerronVerticalIntegral chi x
          (dirichletPerronLeftLine c q T) T = 0 := by
  let R : Set Complex :=
    Set.Icc (dirichletPerronLeftLine c q T) sigma0 ×ℂ Set.Icc (-T) T
  have hSigmaPos : 0 < dirichletPerronLeftLine c q T :=
    dirichletPerronLeftLine_pos hc hT
  have hSigmaOrder : dirichletPerronLeftLine c q T ≤ sigma0 :=
    le_of_lt ((dirichletPerronLeftLine_lt_one hc hT).trans hsigma0)
  have hAnalytic : AnalyticOnNhd Complex chi.LFunction R := by
    have hEntire : AnalyticOnNhd Complex chi.LFunction Set.univ :=
      (chi.differentiable_LFunction hchi).differentiableOn.analyticOnNhd
        isOpen_univ
    exact hEntire.mono (Set.subset_univ R)
  have hNonzero : ∀ s : Complex, s ∈ R → chi.LFunction s ≠ 0 := by
    simpa only [R] using
      nonprincipalLFunction_ne_zero_on_dirichletPerronRectangle
        hc chi hSmooth hchi hT (sigma0 := sigma0)
  simpa only [dirichletPerronHorizontalIntegral,
    dirichletPerronVerticalIntegral] using
    logDerivPerron_boundary_eq_zero hx hSigmaPos hSigmaOrder hT
      hAnalytic hNonzero

/-- Solving the zero boundary identity for the original upward right edge
gives the two horizontal edges and the upward left edge with exact signs. -/
theorem dirichletPerronIntegral_eq_edges
    {c : Real}
    (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c)
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hSmooth : IsDecimalSmooth q) (hchi : chi ≠ 1)
    {x sigma0 T : Real} (hx : 0 < x) (hsigma0 : 1 < sigma0)
    (hT : 0 < T) :
    dirichletPerronIntegral chi x sigma0 T =
      ((1 / (2 * Real.pi) : Real) : Complex) *
        (Complex.I *
            (dirichletPerronHorizontalIntegral chi x
                (dirichletPerronLeftLine c q T) sigma0 (-T) -
              dirichletPerronHorizontalIntegral chi x
                (dirichletPerronLeftLine c q T) sigma0 T) +
          dirichletPerronVerticalIntegral chi x
            (dirichletPerronLeftLine c q T) T) := by
  have hBoundary :=
    dirichletPerron_boundary_eq_zero hc chi hSmooth hchi hx hsigma0 hT
  have hVertical : dirichletPerronIntegral chi x sigma0 T =
      ((1 / (2 * Real.pi) : Real) : Complex) *
        dirichletPerronVerticalIntegral chi x sigma0 T := by
    rw [dirichletPerronIntegral, dirichletPerronVerticalIntegral,
      logDerivPerronVerticalIntegral]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [logDerivPerronIntegrand, div_eq_mul_inv, mul_assoc]
  have hIRight :
      Complex.I * dirichletPerronVerticalIntegral chi x sigma0 T =
        -(dirichletPerronHorizontalIntegral chi x
            (dirichletPerronLeftLine c q T) sigma0 (-T) -
          dirichletPerronHorizontalIntegral chi x
            (dirichletPerronLeftLine c q T) sigma0 T) +
          Complex.I * dirichletPerronVerticalIntegral chi x
            (dirichletPerronLeftLine c q T) T := by
    linear_combination hBoundary
  have hSolvedRaw := congrArg (fun z : Complex => -Complex.I * z) hIRight
  ring_nf at hSolvedRaw
  rw [Complex.I_sq] at hSolvedRaw
  ring_nf at hSolvedRaw
  have hSolved :
      dirichletPerronVerticalIntegral chi x sigma0 T =
        Complex.I *
            (dirichletPerronHorizontalIntegral chi x
                (dirichletPerronLeftLine c q T) sigma0 (-T) -
              dirichletPerronHorizontalIntegral chi x
                (dirichletPerronLeftLine c q T) sigma0 T) +
          dirichletPerronVerticalIntegral chi x
            (dirichletPerronLeftLine c q T) T := by
    linear_combination hSolvedRaw
  rw [hVertical, hSolved]

end PrimesRestrictedDigits
