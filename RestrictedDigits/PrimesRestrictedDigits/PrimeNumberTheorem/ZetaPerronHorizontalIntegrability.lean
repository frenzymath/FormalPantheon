import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronContour

/-!
# Integrability on a zeta Perron horizontal edge

At nonzero height, the strict quarter-width horizontal segment stays away
from the zeta pole and inside the zero-free region. Its Perron integrand is
therefore continuous and interval integrable.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/-- The zeta Perron integrand is genuinely interval integrable on every
nonzero horizontal segment of the strict quarter-width rectangle. -/
theorem intervalIntegrable_zetaPerronIntegrand_horizontal
    {c x sigma0 T t : Real}
    (hc : IsRiemannZetaZeroFreeConstant c) (hx : 0 < x)
    (hsigma0 : 1 < sigma0) (hT : 0 < T)
    (htBound : |t| <= T) (htZero : t ≠ 0) :
    IntervalIntegrable
      (fun r : Real => zetaPerronIntegrand x
        ((r : Complex) + Complex.I * (t : Complex)))
      volume (zetaPerronLeftLine c T) sigma0 := by
  let sigma1 : Real := zetaPerronLeftLine c T
  let path : Real -> Complex := fun r => (r : Complex) + Complex.I * t
  let R : Set Complex := path '' Set.uIcc sigma1 sigma0
  have hSigmaLt : sigma1 < 1 := zetaPerronLeftLine_lt_one hc hT
  have hOrder : sigma1 <= sigma0 :=
    hSigmaLt.le.trans (le_of_lt hsigma0)
  have hPathContinuous : Continuous path := by
    dsimp [path]
    fun_prop
  have hAwayFromOne : R <= {1}ᶜ := by
    intro s hs
    rcases hs with ⟨r, hr, rfl⟩
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hsOne
    have hIm := congrArg Complex.im hsOne
    simp [path] at hIm
    exact htZero hIm
  have hZetaAnalytic : AnalyticOnNhd Complex riemannZeta R :=
    analyticOn_riemannZeta.mono hAwayFromOne
  have hZetaNonzero : ∀ s ∈ R, riemannZeta s ≠ 0 := by
    intro s hs
    rcases hs with ⟨r, hr, rfl⟩
    rw [uIcc_of_le hOrder, Set.mem_Icc] at hr
    apply hc.2.2 t r
    exact (zetaPerronLeftLine_zeroFree hc hT htBound).trans hr.1
  have hLogDerivAnalytic :
      AnalyticOnNhd Complex (logDeriv riemannZeta) R := by
    change AnalyticOnNhd Complex
      (fun s : Complex => deriv riemannZeta s / riemannZeta s) R
    exact hZetaAnalytic.deriv.div hZetaAnalytic hZetaNonzero
  have hPathMap : MapsTo path (Set.uIcc sigma1 sigma0) R :=
    fun r hr => ⟨r, hr, rfl⟩
  have hLogDerivContinuous : ContinuousOn
      (fun r => logDeriv riemannZeta (path r))
      (Set.uIcc sigma1 sigma0) :=
    hLogDerivAnalytic.continuousOn.comp
      hPathContinuous.continuousOn hPathMap
  have hPowerContinuous : ContinuousOn
      (fun r => (x : Complex) ^ path r) (Set.uIcc sigma1 sigma0) :=
    hPathContinuous.continuousOn.const_cpow
      (.inl <| Complex.ofReal_ne_zero.mpr hx.ne')
  have hPathNonzero : ∀ r ∈ Set.uIcc sigma1 sigma0, path r ≠ 0 := by
    intro r hr hsZero
    have hIm := congrArg Complex.im hsZero
    simp [path] at hIm
    exact htZero hIm
  have hQuotientContinuous : ContinuousOn
      (fun r => (x : Complex) ^ path r / path r)
      (Set.uIcc sigma1 sigma0) :=
    hPowerContinuous.div hPathContinuous.continuousOn hPathNonzero
  have hIntegrandContinuous : ContinuousOn
      (fun r => zetaPerronIntegrand x (path r))
      (Set.uIcc sigma1 sigma0) := by
    intro r hr
    exact (hLogDerivContinuous r hr).neg.mul (hQuotientContinuous r hr)
  simpa only [sigma1, path] using hIntegrandContinuous.intervalIntegrable

end PrimesRestrictedDigits
