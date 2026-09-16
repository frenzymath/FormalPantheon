import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletNonprincipalPerronContour
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPrincipalPerronContourParameters
import PrimesRestrictedDigits.PrimeNumberTheorem.LogDerivPerronPoleContour

/-!
# The exact principal Dirichlet Perron contour

This module proves the residue-`x` principal contour identity from
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.16, pp. 378--379. Mathlib's
entire principal regularization keeps Cauchy's theorem away from the
totalized pole value.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/-- The exact counterclockwise principal Dirichlet Perron boundary has
residue `2 * pi * I * x` at one. -/
theorem principalDirichletPerron_boundary_eq
    {c : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    {q : Nat} [NeZero q]
    {x sigma0 T : Real} (hx : 0 < x) (hsigma0 : 1 < sigma0)
    (hT : 0 < T) :
    dirichletPerronHorizontalIntegral
          (1 : DirichletCharacter Complex q) x
          (dirichletPerronLeftLine c q T) sigma0 (-T) -
        dirichletPerronHorizontalIntegral
          (1 : DirichletCharacter Complex q) x
          (dirichletPerronLeftLine c q T) sigma0 T +
        Complex.I * dirichletPerronVerticalIntegral
          (1 : DirichletCharacter Complex q) x sigma0 T -
        Complex.I * dirichletPerronVerticalIntegral
          (1 : DirichletCharacter Complex q) x
          (dirichletPerronLeftLine c q T) T =
      ((2 * Real.pi : Real) : Complex) * Complex.I * x := by
  let sigma1 : Real := dirichletPerronLeftLine c q T
  let R : Set Complex := Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T
  have hSigmaPos : 0 < sigma1 :=
    dirichletPerronLeftLine_pos_of_riemannZeta hc hT
  have hSigmaLt : sigma1 < 1 :=
    dirichletPerronLeftLine_lt_one_of_riemannZeta hc hT
  have hAnalytic : AnalyticOnNhd Complex
      (DirichletCharacter.LFunctionTrivChar₁ q) R := by
    have hEntire : AnalyticOnNhd Complex
        (DirichletCharacter.LFunctionTrivChar₁ q) Set.univ :=
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
        |>.analyticOnNhd isOpen_univ
    exact hEntire.mono (Set.subset_univ R)
  have hNonzero : ∀ s : Complex,
      s ∈ R → DirichletCharacter.LFunctionTrivChar₁ q s ≠ 0 := by
    simpa only [R, sigma1] using
      LFunctionTrivChar₁_ne_zero_on_dirichletPerronRectangle
        hc hT (q := q) (sigma0 := sigma0)
  have hRelation : ∀ s : Complex, s ∈ R → s ≠ 1 →
      -logDeriv (1 : DirichletCharacter Complex q).LFunction s =
        -logDeriv (DirichletCharacter.LFunctionTrivChar₁ q) s +
          1 / (s - 1) := by
    intro s hs hsOne
    rw [Complex.mem_reProdIm] at hs
    have hTBound : |s.im| ≤ T := by
      rw [abs_le]
      exact hs.2
    have hsPos : 0 < s.re := hSigmaPos.trans_le hs.1.1
    have hRegion :
        1 - c / Real.log (|s.im| + 4) ≤ s.re :=
      (dirichletPerronLeftLine_riemannZetaZeroFree hc hT hTBound).trans
        hs.1.1
    have hZetaCoordinates := hc.2.2 s.im s.re hRegion
    have hsCoordinates :
        ((s.re : Real) : Complex) + Complex.I * (s.im : Complex) = s := by
      apply Complex.ext <;> simp
    have hZeta : riemannZeta s ≠ 0 := by
      rw [hsCoordinates] at hZetaCoordinates
      exact hZetaCoordinates
    exact neg_logDeriv_principal_eq_neg_logDeriv_LFunctionTrivChar₁_add_inv
      hsPos hsOne hZeta
  simpa only [dirichletPerronHorizontalIntegral,
    dirichletPerronVerticalIntegral, sigma1, R] using
    logDerivPerron_boundary_eq_residue
      (f := (1 : DirichletCharacter Complex q).LFunction)
      (g := DirichletCharacter.LFunctionTrivChar₁ q)
      hx hSigmaPos hSigmaLt hsigma0 hT hAnalytic hNonzero hRelation

/-- Solving the principal residue boundary for the original upward right edge
puts the main term `x` on the left and leaves the upward left edge positive. -/
theorem principalDirichletPerronIntegral_sub_self_eq_edges
    {c : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    {q : Nat} [NeZero q]
    {x sigma0 T : Real} (hx : 0 < x) (hsigma0 : 1 < sigma0)
    (hT : 0 < T) :
    dirichletPerronIntegral (1 : DirichletCharacter Complex q)
        x sigma0 T - (x : Complex) =
      ((1 / (2 * Real.pi) : Real) : Complex) *
        (Complex.I *
            (dirichletPerronHorizontalIntegral
                (1 : DirichletCharacter Complex q) x
                (dirichletPerronLeftLine c q T) sigma0 (-T) -
              dirichletPerronHorizontalIntegral
                (1 : DirichletCharacter Complex q) x
                (dirichletPerronLeftLine c q T) sigma0 T) +
          dirichletPerronVerticalIntegral
            (1 : DirichletCharacter Complex q) x
            (dirichletPerronLeftLine c q T) T) := by
  have hBoundary :=
    principalDirichletPerron_boundary_eq (q := q) hc hx hsigma0 hT
  have hVertical :
      dirichletPerronIntegral (1 : DirichletCharacter Complex q)
          x sigma0 T =
        ((1 / (2 * Real.pi) : Real) : Complex) *
          dirichletPerronVerticalIntegral
            (1 : DirichletCharacter Complex q) x sigma0 T := by
    rw [dirichletPerronIntegral, dirichletPerronVerticalIntegral,
      logDerivPerronVerticalIntegral]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [logDerivPerronIntegrand, div_eq_mul_inv, mul_assoc]
  rw [hVertical]
  have hIRight :
      Complex.I * dirichletPerronVerticalIntegral
          (1 : DirichletCharacter Complex q) x sigma0 T =
        ((2 * Real.pi : Real) : Complex) * Complex.I * x -
            (dirichletPerronHorizontalIntegral
                (1 : DirichletCharacter Complex q) x
                (dirichletPerronLeftLine c q T) sigma0 (-T) -
              dirichletPerronHorizontalIntegral
                (1 : DirichletCharacter Complex q) x
                (dirichletPerronLeftLine c q T) sigma0 T) +
          Complex.I * dirichletPerronVerticalIntegral
            (1 : DirichletCharacter Complex q) x
            (dirichletPerronLeftLine c q T) T := by
    linear_combination hBoundary
  have hSolvedRaw := congrArg (fun z : Complex => -Complex.I * z) hIRight
  ring_nf at hSolvedRaw
  rw [Complex.I_sq] at hSolvedRaw
  ring_nf at hSolvedRaw
  have hSolved :
      dirichletPerronVerticalIntegral
          (1 : DirichletCharacter Complex q) x sigma0 T -
          ((2 * Real.pi : Real) : Complex) * x =
        Complex.I *
            (dirichletPerronHorizontalIntegral
                (1 : DirichletCharacter Complex q) x
                (dirichletPerronLeftLine c q T) sigma0 (-T) -
              dirichletPerronHorizontalIntegral
                (1 : DirichletCharacter Complex q) x
                (dirichletPerronLeftLine c q T) sigma0 T) +
          dirichletPerronVerticalIntegral
            (1 : DirichletCharacter Complex q) x
            (dirichletPerronLeftLine c q T) T := by
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
          dirichletPerronVerticalIntegral
            (1 : DirichletCharacter Complex q) x sigma0 T - (x : Complex) =
        ((1 / (2 * Real.pi) : Real) : Complex) *
          (dirichletPerronVerticalIntegral
              (1 : DirichletCharacter Complex q) x sigma0 T -
            ((2 * Real.pi : Real) : Complex) * x) := by
      rw [mul_sub, ← mul_assoc, hReciprocal, one_mul]
    _ = _ := by rw [hSolved]

end PrimesRestrictedDigits
