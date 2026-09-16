import PrimesRestrictedDigits.PrimeNumberTheorem.LogDerivPerronContour
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronPoleBoundary

/-!
# A logarithmic-derivative Perron contour with a simple pole

This file separates a unit simple pole from a logarithmic-derivative Perron
integrand. The pole-free part is regularized with a divided slope before
Cauchy's rectangle theorem is applied, while the remaining pole boundary is
evaluated explicitly.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private noncomputable def polePerronQuotient
    (x : Real) (s : Complex) : Complex :=
  (x : Complex) ^ s / s

private noncomputable def regularizedLogDerivPerronIntegrand
    (g : Complex -> Complex) (x : Real) (s : Complex) : Complex :=
  dslope (polePerronQuotient x) 1 s +
    logDerivPerronIntegrand g x s

private theorem differentiableOn_polePerronQuotient
    {x : Real} (hx : 0 < x) :
    DifferentiableOn Complex (polePerronQuotient x)
      {s : Complex | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  apply DifferentiableAt.differentiableWithinAt
  change DifferentiableAt Complex (fun z : Complex => (x : Complex) ^ z / z) s
  apply (differentiableAt_id.const_cpow
    (.inl <| Complex.ofReal_ne_zero.mpr hx.ne')).div differentiableAt_id
  intro hsZero
  have hRe := congrArg Complex.re hsZero
  simp at hRe
  linarith

private theorem logDerivPerronIntegrand_eq_regularized_add_pole
    {f g : Complex -> Complex} {x : Real} {s : Complex}
    (hsOne : s ≠ 1)
    (hrel : -logDeriv f s = -logDeriv g s + 1 / (s - 1)) :
    logDerivPerronIntegrand f x s =
      regularizedLogDerivPerronIntegrand g x s +
        (x : Complex) / (s - 1) := by
  change (-logDeriv f s) * polePerronQuotient x s =
    dslope (polePerronQuotient x) 1 s +
        (-logDeriv g s) * polePerronQuotient x s +
      (x : Complex) / (s - 1)
  rw [hrel, dslope_of_ne _ hsOne]
  simp only [slope, vsub_eq_sub, smul_eq_mul]
  have hQuotientOne : polePerronQuotient x 1 = (x : Complex) := by
    simp [polePerronQuotient, Complex.cpow_one]
  rw [hQuotientOne]
  field_simp [sub_ne_zero.mpr hsOne]
  ring

private theorem intervalIntegral_logDerivPerron_split
    {f g : Complex -> Complex} {x a b : Real} {R : Set Complex}
    {path : Real -> Complex}
    (hpath : ContinuousOn path (uIcc a b))
    (hmap : MapsTo path (uIcc a b) R)
    (hne : forall t, t ∈ uIcc a b -> path t ≠ 1)
    (hrel : forall s, s ∈ R -> s ≠ 1 ->
      -logDeriv f s = -logDeriv g s + 1 / (s - 1))
    (hRegularized : DifferentiableOn Complex
      (regularizedLogDerivPerronIntegrand g x) R) :
    (∫ t in a..b, logDerivPerronIntegrand f x (path t)) =
      (∫ t in a..b,
        regularizedLogDerivPerronIntegrand g x (path t)) +
        ∫ t in a..b, (x : Complex) / (path t - 1) := by
  have hRegularizedContinuous : ContinuousOn
      (fun t => regularizedLogDerivPerronIntegrand g x (path t))
        (uIcc a b) :=
    hRegularized.continuousOn.comp hpath hmap
  have hPoleContinuous : ContinuousOn
      (fun t => (x : Complex) / (path t - 1)) (uIcc a b) := by
    apply continuousOn_const.div
      (hpath.sub continuousOn_const)
    intro t ht hZero
    apply hne t ht
    exact sub_eq_zero.mp hZero
  calc
    _ = ∫ t in a..b,
        regularizedLogDerivPerronIntegrand g x (path t) +
          (x : Complex) / (path t - 1) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact logDerivPerronIntegrand_eq_regularized_add_pole
        (hne t ht) (hrel (path t) (hmap ht) (hne t ht))
    _ = _ := intervalIntegral.integral_add
      hRegularizedContinuous.intervalIntegrable
      hPoleContinuous.intervalIntegrable

/-- Suppose the negative logarithmic derivative of `f` differs from that of
an analytic, nonvanishing function `g` by `1 / (s - 1)`. Then the
counterclockwise logarithmic-derivative Perron boundary of `f` is exactly the
residue `2 * pi * I * x`. -/
theorem logDerivPerron_boundary_eq_residue
    {f g : Complex -> Complex} {x sigma1 sigma0 T : Real}
    (hx : 0 < x) (hsigma1Pos : 0 < sigma1)
    (hsigma1 : sigma1 < 1) (hsigma0 : 1 < sigma0) (hT : 0 < T)
    (hg : AnalyticOnNhd Complex g
      (Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T))
    (hzero : forall s,
      s ∈ Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T -> g s ≠ 0)
    (hrel : forall s,
      s ∈ Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T -> s ≠ 1 ->
        -logDeriv f s = -logDeriv g s + 1 / (s - 1)) :
    logDerivPerronHorizontalIntegral f x sigma1 sigma0 (-T) -
        logDerivPerronHorizontalIntegral f x sigma1 sigma0 T +
        Complex.I * logDerivPerronVerticalIntegral f x sigma0 T -
        Complex.I * logDerivPerronVerticalIntegral f x sigma1 T =
      ((2 * Real.pi : Real) : Complex) * Complex.I * x := by
  let U : Set Complex := {s : Complex | 0 < s.re}
  let R : Set Complex :=
    Set.Icc sigma1 sigma0 ×ℂ Set.Icc (-T) T
  have hSigmaOrder : sigma1 <= sigma0 :=
    hsigma1.le.trans (le_of_lt hsigma0)
  have hTOrder : -T <= T := by linarith
  have hRSubsetU : R ⊆ U := by
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    exact hsigma1Pos.trans_le hs.1.1
  have hQuotientU : DifferentiableOn Complex (polePerronQuotient x) U :=
    differentiableOn_polePerronQuotient hx
  have hUNeighborhood : U ∈ nhds (1 : Complex) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
  have hSlopeU : DifferentiableOn Complex
      (dslope (polePerronQuotient x) 1) U :=
    (Complex.differentiableOn_dslope hUNeighborhood).2 hQuotientU
  have hQuotientR : DifferentiableOn Complex (polePerronQuotient x) R :=
    hQuotientU.mono hRSubsetU
  have hLogDerivR : AnalyticOnNhd Complex (logDeriv g) R := by
    change AnalyticOnNhd Complex (fun s : Complex => deriv g s / g s) R
    exact hg.deriv.div hg hzero
  have hRegularized : DifferentiableOn Complex
      (regularizedLogDerivPerronIntegrand g x) R := by
    change DifferentiableOn Complex
      (fun s => dslope (polePerronQuotient x) 1 s +
        (-logDeriv g s) * polePerronQuotient x s) R
    exact (hSlopeU.mono hRSubsetU).add
      (hLogDerivR.differentiableOn.neg.mul hQuotientR)
  have hBottomMap : MapsTo
      (fun r : Real => (r : Complex) + Complex.I * (-T))
      (uIcc sigma1 sigma0) R := by
    intro r hr
    rw [uIcc_of_le hSigmaOrder, Set.mem_Icc] at hr
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using hr
    · simp [hTOrder]
  have hTopMap : MapsTo
      (fun r : Real => (r : Complex) + Complex.I * T)
      (uIcc sigma1 sigma0) R := by
    intro r hr
    rw [uIcc_of_le hSigmaOrder, Set.mem_Icc] at hr
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using hr
    · simp [hTOrder]
  have hRightMap : MapsTo
      (fun t : Real => (sigma0 : Complex) + Complex.I * t)
      (uIcc (-T) T) R := by
    intro t ht
    rw [uIcc_of_le hTOrder, Set.mem_Icc] at ht
    rw [Complex.mem_reProdIm]
    constructor
    · simp [hSigmaOrder]
    · simpa using ht
  have hLeftMap : MapsTo
      (fun t : Real => (sigma1 : Complex) + Complex.I * t)
      (uIcc (-T) T) R := by
    intro t ht
    rw [uIcc_of_le hTOrder, Set.mem_Icc] at ht
    rw [Complex.mem_reProdIm]
    constructor
    · simp [hSigmaOrder]
    · simpa using ht
  have hBottomNe : forall r, r ∈ uIcc sigma1 sigma0 ->
      ((r : Complex) + Complex.I * (-T)) ≠ 1 := by
    intro r hr hs
    have hIm := congrArg Complex.im hs
    simp at hIm
    linarith
  have hTopNe : forall r, r ∈ uIcc sigma1 sigma0 ->
      ((r : Complex) + Complex.I * T) ≠ 1 := by
    intro r hr hs
    have hIm := congrArg Complex.im hs
    simp at hIm
    linarith
  have hRightNe : forall t, t ∈ uIcc (-T) T ->
      ((sigma0 : Complex) + Complex.I * t) ≠ 1 := by
    intro t ht hs
    have hRe := congrArg Complex.re hs
    simp at hRe
    linarith
  have hLeftNe : forall t, t ∈ uIcc (-T) T ->
      ((sigma1 : Complex) + Complex.I * t) ≠ 1 := by
    intro t ht hs
    have hRe := congrArg Complex.re hs
    simp at hRe
    linarith
  have hBottom := intervalIntegral_logDerivPerron_split
    (f := f) (g := g) (R := R) (path := fun r : Real =>
      (r : Complex) + Complex.I * (-T)) (by fun_prop)
    hBottomMap hBottomNe hrel hRegularized
  have hTop := intervalIntegral_logDerivPerron_split
    (f := f) (g := g) (R := R) (path := fun r : Real =>
      (r : Complex) + Complex.I * T) (by fun_prop)
    hTopMap hTopNe hrel hRegularized
  have hRight := intervalIntegral_logDerivPerron_split
    (f := f) (g := g) (R := R) (path := fun t : Real =>
      (sigma0 : Complex) + Complex.I * t) (by fun_prop)
    hRightMap hRightNe hrel hRegularized
  have hLeft := intervalIntegral_logDerivPerron_split
    (f := f) (g := g) (R := R) (path := fun t : Real =>
      (sigma1 : Complex) + Complex.I * t) (by fun_prop)
    hLeftMap hLeftNe hrel hRegularized
  have hRegularizedBoundary :
      (∫ r in sigma1..sigma0,
            regularizedLogDerivPerronIntegrand g x
              ((r : Complex) + Complex.I * (-T))) -
          (∫ r in sigma1..sigma0,
            regularizedLogDerivPerronIntegrand g x
              ((r : Complex) + Complex.I * T)) +
          Complex.I * (∫ t in -T..T,
            regularizedLogDerivPerronIntegrand g x
              ((sigma0 : Complex) + Complex.I * t)) -
          Complex.I * (∫ t in -T..T,
            regularizedLogDerivPerronIntegrand g x
              ((sigma1 : Complex) + Complex.I * t)) = 0 := by
    simpa only [Complex.ofReal_neg, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_comm] using
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn
        (regularizedLogDerivPerronIntegrand g x)
        (Complex.mk sigma1 (-T)) (Complex.mk sigma0 T) (by
          simpa only [uIcc_of_le hSigmaOrder, uIcc_of_le hTOrder] using
            hRegularized)
  have hInverse := inverse_sub_real_boundary_eq_two_pi_mul_I
    (a := sigma1) (b := sigma0) (center := 1) (T := T)
    hsigma1 hsigma0 hT
  have hInverseAligned :
      (∫ r in sigma1..sigma0, (1 : Complex) /
            (((r : Complex) + Complex.I * (-T)) - 1)) -
          (∫ r in sigma1..sigma0, (1 : Complex) /
            (((r : Complex) + Complex.I * T) - 1)) +
          Complex.I * (∫ t in -T..T, (1 : Complex) /
            (((sigma0 : Complex) + Complex.I * t) - 1)) -
          Complex.I * (∫ t in -T..T, (1 : Complex) /
            (((sigma1 : Complex) + Complex.I * t) - 1)) =
        ((2 * Real.pi : Real) : Complex) * Complex.I := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, mul_comm] using hInverse
  have hPoleBottom :
      (∫ r in sigma1..sigma0, (x : Complex) /
          (((r : Complex) + Complex.I * (-T)) - 1)) =
        (x : Complex) * ∫ r in sigma1..sigma0, (1 : Complex) /
          (((r : Complex) + Complex.I * (-T)) - 1) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (intervalIntegral.integral_const_mul (a := sigma1) (b := sigma0)
        (x : Complex) (fun r : Real => (1 : Complex) /
          (((r : Complex) + Complex.I * (-T)) - 1)))
  have hPoleTop :
      (∫ r in sigma1..sigma0, (x : Complex) /
          (((r : Complex) + Complex.I * T) - 1)) =
        (x : Complex) * ∫ r in sigma1..sigma0, (1 : Complex) /
          (((r : Complex) + Complex.I * T) - 1) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (intervalIntegral.integral_const_mul (a := sigma1) (b := sigma0)
        (x : Complex) (fun r : Real => (1 : Complex) /
          (((r : Complex) + Complex.I * T) - 1)))
  have hPoleRight :
      (∫ t in -T..T, (x : Complex) /
          (((sigma0 : Complex) + Complex.I * t) - 1)) =
        (x : Complex) * ∫ t in -T..T, (1 : Complex) /
          (((sigma0 : Complex) + Complex.I * t) - 1) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (intervalIntegral.integral_const_mul (a := -T) (b := T)
        (x : Complex) (fun t : Real => (1 : Complex) /
          (((sigma0 : Complex) + Complex.I * t) - 1)))
  have hPoleLeft :
      (∫ t in -T..T, (x : Complex) /
          (((sigma1 : Complex) + Complex.I * t) - 1)) =
        (x : Complex) * ∫ t in -T..T, (1 : Complex) /
          (((sigma1 : Complex) + Complex.I * t) - 1) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (intervalIntegral.integral_const_mul (a := -T) (b := T)
        (x : Complex) (fun t : Real => (1 : Complex) /
          (((sigma1 : Complex) + Complex.I * t) - 1)))
  have hPole :
      (∫ r in sigma1..sigma0, (x : Complex) /
            (((r : Complex) + Complex.I * (-T)) - 1)) -
          (∫ r in sigma1..sigma0, (x : Complex) /
            (((r : Complex) + Complex.I * T) - 1)) +
          Complex.I * (∫ t in -T..T, (x : Complex) /
            (((sigma0 : Complex) + Complex.I * t) - 1)) -
          Complex.I * (∫ t in -T..T, (x : Complex) /
            (((sigma1 : Complex) + Complex.I * t) - 1)) =
        ((2 * Real.pi : Real) : Complex) * Complex.I * x := by
    rw [hPoleBottom, hPoleTop, hPoleRight, hPoleLeft]
    linear_combination (x : Complex) * hInverseAligned
  simp only [logDerivPerronHorizontalIntegral,
    logDerivPerronVerticalIntegral, Complex.ofReal_neg]
  rw [hBottom, hTop, hRight, hLeft]
  linear_combination hRegularizedBoundary + hPole

end PrimesRestrictedDigits
