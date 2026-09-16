import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronContour

/-!
# Integrability on the zeta Perron left edge

The strict quarter-width line stays away from the zeta pole and inside its
zero-free region, so the logarithmic-derivative integrand is continuous on
every finite vertical segment.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/-- The zeta Perron integrand is genuinely interval integrable on the complete
upward left edge of the strict quarter-width rectangle. -/
theorem intervalIntegrable_zetaPerronIntegrand_left
    {c x T : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hx : 0 < x) (hT : 0 < T) :
    IntervalIntegrable
      (fun t : Real => zetaPerronIntegrand x
        ((zetaPerronLeftLine c T : Complex) + Complex.I * (t : Complex)))
      volume (-T) T := by
  let sigma : Real := zetaPerronLeftLine c T
  let path : Real -> Complex := fun t => (sigma : Complex) + Complex.I * t
  let R : Set Complex := path '' Set.uIcc (-T) T
  have hSigmaPos : 0 < sigma := zetaPerronLeftLine_pos hc hT
  have hSigmaLt : sigma < 1 := zetaPerronLeftLine_lt_one hc hT
  have hOrder : -T <= T := by linarith
  have hPathContinuous : Continuous path := by
    dsimp [path]
    fun_prop
  have hAwayFromOne : R <= {1}ᶜ := by
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hsOne
    have hRe := congrArg Complex.re hsOne
    simp [path] at hRe
    linarith
  have hZetaAnalytic : AnalyticOnNhd Complex riemannZeta R :=
    analyticOn_riemannZeta.mono hAwayFromOne
  have hZetaNonzero : ∀ s ∈ R, riemannZeta s ≠ 0 := by
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    rw [uIcc_of_le hOrder, Set.mem_Icc] at ht
    apply hc.2.2 t sigma
    exact zetaPerronLeftLine_zeroFree hc hT (abs_le.2 ht)
  have hLogDerivAnalytic :
      AnalyticOnNhd Complex (logDeriv riemannZeta) R := by
    change AnalyticOnNhd Complex
      (fun s : Complex => deriv riemannZeta s / riemannZeta s) R
    exact hZetaAnalytic.deriv.div hZetaAnalytic hZetaNonzero
  have hPathMap : MapsTo path (Set.uIcc (-T) T) R :=
    fun t ht => ⟨t, ht, rfl⟩
  have hLogDerivContinuous : ContinuousOn
      (fun t => logDeriv riemannZeta (path t)) (Set.uIcc (-T) T) :=
    hLogDerivAnalytic.continuousOn.comp hPathContinuous.continuousOn hPathMap
  have hPowerContinuous : ContinuousOn
      (fun t => (x : Complex) ^ path t) (Set.uIcc (-T) T) :=
    hPathContinuous.continuousOn.const_cpow
      (.inl <| Complex.ofReal_ne_zero.mpr hx.ne')
  have hPathNonzero : ∀ t ∈ Set.uIcc (-T) T, path t ≠ 0 := by
    intro t ht hsZero
    have hRe := congrArg Complex.re hsZero
    simp [path] at hRe
    linarith
  have hQuotientContinuous : ContinuousOn
      (fun t => (x : Complex) ^ path t / path t) (Set.uIcc (-T) T) :=
    hPowerContinuous.div hPathContinuous.continuousOn hPathNonzero
  have hIntegrandContinuous : ContinuousOn
      (fun t => zetaPerronIntegrand x (path t)) (Set.uIcc (-T) T) := by
    intro t ht
    exact (hLogDerivContinuous t ht).neg.mul (hQuotientContinuous t ht)
  simpa only [sigma, path] using hIntegrandContinuous.intervalIntegrable

end PrimesRestrictedDigits
