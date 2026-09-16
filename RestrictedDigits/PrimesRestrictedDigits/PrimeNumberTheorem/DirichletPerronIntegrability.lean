import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronConstants
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPrincipalPerronContourParameters
import PrimesRestrictedDigits.PrimeNumberTheorem.LogDerivPerronContour

/-!
# Integrability of the shifted Dirichlet Perron edges

This module proves genuine interval integrability on the horizontal and left
edges used by the decimal-smooth Dirichlet Perron contours. The principal
branch is handled through Mathlib's entire pole regularization; the original
principal L-function is used only on paths that avoid one.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private theorem intervalIntegrable_logDerivPerronIntegrand_comp
    {f : Complex -> Complex} {x a b : Real} {path : Real -> Complex}
    (hx : 0 < x) (hpath : ContinuousOn path (Set.uIcc a b))
    (hlog : ContinuousOn
      (fun t => -logDeriv f (path t)) (Set.uIcc a b))
    (hpath0 : forall t, t ∈ Set.uIcc a b -> path t ≠ 0) :
    IntervalIntegrable
      (fun t => logDerivPerronIntegrand f x (path t)) volume a b := by
  have hpower : ContinuousOn
      (fun t => (x : Complex) ^ path t) (Set.uIcc a b) :=
    hpath.const_cpow (.inl <| Complex.ofReal_ne_zero.mpr hx.ne')
  have hquotient : ContinuousOn
      (fun t => (x : Complex) ^ path t / path t) (Set.uIcc a b) :=
    hpower.div hpath hpath0
  have hintegrand : ContinuousOn
      (fun t => (-logDeriv f (path t)) *
        ((x : Complex) ^ path t / path t)) (Set.uIcc a b) := by
    intro t ht
    exact (hlog t ht).mul (hquotient t ht)
  simpa only [logDerivPerronIntegrand] using hintegrand.intervalIntegrable

/-- The Dirichlet Perron integrand is genuinely interval integrable on every
nonzero horizontal segment of the factor-five rectangle. -/
theorem DirichletPerronLogDerivBounds.intervalIntegrable_dirichletPerronIntegrand_horizontal
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hq : IsDecimalSmooth q) {x sigma0 T t : Real}
    (hx : 0 < x) (hsigma0 : 1 < sigma0) (hT : 0 < T)
    (htBound : |t| <= T) (htZero : t ≠ 0) :
    IntervalIntegrable
      (fun r : Real => logDerivPerronIntegrand chi.LFunction x
        ((r : Complex) + Complex.I * (t : Complex)))
      volume (dirichletPerronLeftLine c q T) sigma0 := by
  classical
  let sigma1 : Real := dirichletPerronLeftLine c q T
  let path : Real -> Complex :=
    fun r => (r : Complex) + Complex.I * (t : Complex)
  have hsigma1Pos : 0 < sigma1 := by
    simpa only [sigma1] using
      dirichletPerronLeftLine_pos_of_riemannZeta
        h.riemannZetaZeroFree hT
  have hsigma1Lt : sigma1 < 1 := by
    simpa only [sigma1] using
      dirichletPerronLeftLine_lt_one_of_riemannZeta
        h.riemannZetaZeroFree hT
  have horder : sigma1 <= sigma0 :=
    hsigma1Lt.le.trans (le_of_lt hsigma0)
  have hpath : Continuous path := by
    dsimp [path]
    fun_prop
  have hpath0 : forall r, r ∈ Set.uIcc sigma1 sigma0 -> path r ≠ 0 := by
    intro r _hr hrZero
    have him := congrArg Complex.im hrZero
    simp [path] at him
    exact htZero him
  have hlog : ContinuousOn
      (fun r => -logDeriv chi.LFunction (path r))
      (Set.uIcc sigma1 sigma0) := by
    by_cases hchi : chi = 1
    · subst chi
      have hprincipal : forall r, r ∈ Set.uIcc sigma1 sigma0 ->
          0 < (path r).re ∧ path r ≠ 1 ∧ riemannZeta (path r) ≠ 0 := by
        intro r hr
        rw [uIcc_of_le horder, Set.mem_Icc] at hr
        have hrLeft : dirichletPerronLeftLine c q T <= r := by
          simpa only [sigma1] using hr.1
        have hsPos : 0 < (path r).re := by
          simpa [path] using hsigma1Pos.trans_le hr.1
        have hsOne : path r ≠ 1 := by
          intro hs
          have him := congrArg Complex.im hs
          simp [path] at him
          exact htZero him
        have hregion :
            1 - c / Real.log (|t| + 4) <= r :=
          (dirichletPerronLeftLine_riemannZetaZeroFree
            h.riemannZetaZeroFree hT htBound).trans hrLeft
        have hzeta := h.riemannZetaZeroFree.2.2 t r hregion
        have hzetaPath : riemannZeta (path r) ≠ 0 := by
          simpa only [path] using hzeta
        exact ⟨hsPos, hsOne, hzetaPath⟩
      have hregularized : ContinuousOn
          (fun r => -logDeriv
            (DirichletCharacter.LFunctionTrivChar₁ q) (path r))
          (Set.uIcc sigma1 sigma0) := by
        have hcontinuous :=
          DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁
            (n := q)
        have hcomp := hcontinuous.comp hpath.continuousOn (by
          intro r hr
          exact Or.inr
            (principalLFunction_ne_zero_of_re_pos_of_riemannZeta_ne_zero
              (hprincipal r hr).1 (hprincipal r hr).2.1
              (hprincipal r hr).2.2))
        refine hcomp.congr ?_
        intro r _hr
        simp only [Function.comp_apply, logDeriv_apply, neg_div]
      have hpole : ContinuousOn (fun r => 1 / (path r - 1))
          (Set.uIcc sigma1 sigma0) := by
        exact continuousOn_const.div
          (hpath.continuousOn.sub continuousOn_const)
          (fun r hr => sub_ne_zero.mpr (hprincipal r hr).2.1)
      refine (hregularized.add hpole).congr ?_
      intro r hr
      exact neg_logDeriv_principal_eq_neg_logDeriv_LFunctionTrivChar₁_add_inv
        (hprincipal r hr).1 (hprincipal r hr).2.1 (hprincipal r hr).2.2
    · have hnonzero : MapsTo path (Set.uIcc sigma1 sigma0)
          {s | chi.LFunction s ≠ 0} := by
        intro r hr
        rw [uIcc_of_le horder, Set.mem_Icc] at hr
        have hrLeft : dirichletPerronLeftLine c q T <= r := by
          simpa only [sigma1] using hr.1
        have hregion :
            1 - c / Real.log ((q : Real) * (|t| + 4)) <= r :=
          (dirichletPerronLeftLine_zeroFree
            h.nonprincipalZeroFree hT htBound).trans hrLeft
        change chi.LFunction (path r) ≠ 0
        simpa only [path] using
          h.nonprincipalZeroFree.2.2 chi hq hchi t r hregion
      have hcontinuous :=
        DirichletCharacter.continuousOn_neg_logDeriv_LFunction_of_nontriv hchi
      have hcomp := hcontinuous.comp hpath.continuousOn hnonzero
      refine hcomp.congr ?_
      intro r _hr
      simp only [Function.comp_apply, logDeriv_apply, neg_div]
  simpa only [sigma1, path] using
    intervalIntegrable_logDerivPerronIntegrand_comp
      hx hpath.continuousOn hlog hpath0

/-- The Dirichlet Perron integrand is genuinely interval integrable on the
complete upward left edge of the factor-five rectangle. -/
theorem DirichletPerronLogDerivBounds.intervalIntegrable_dirichletPerronIntegrand_left
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hq : IsDecimalSmooth q) {x T : Real}
    (hx : 0 < x) (hT : 0 < T) :
    IntervalIntegrable
      (fun t : Real => logDerivPerronIntegrand chi.LFunction x
        ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * (t : Complex)))
      volume (-T) T := by
  classical
  let sigma1 : Real := dirichletPerronLeftLine c q T
  let path : Real -> Complex :=
    fun t => (sigma1 : Complex) + Complex.I * (t : Complex)
  have hsigma1Pos : 0 < sigma1 := by
    simpa only [sigma1] using
      dirichletPerronLeftLine_pos_of_riemannZeta
        h.riemannZetaZeroFree hT
  have hsigma1Lt : sigma1 < 1 := by
    simpa only [sigma1] using
      dirichletPerronLeftLine_lt_one_of_riemannZeta
        h.riemannZetaZeroFree hT
  have horder : -T <= T := by linarith
  have hpath : Continuous path := by
    dsimp [path]
    fun_prop
  have hpath0 : forall t, t ∈ Set.uIcc (-T) T -> path t ≠ 0 := by
    intro t _ht htZero
    have hre := congrArg Complex.re htZero
    simp [path] at hre
    linarith
  have hlog : ContinuousOn
      (fun t => -logDeriv chi.LFunction (path t))
      (Set.uIcc (-T) T) := by
    by_cases hchi : chi = 1
    · subst chi
      have hprincipal : forall t, t ∈ Set.uIcc (-T) T ->
          0 < (path t).re ∧ path t ≠ 1 ∧ riemannZeta (path t) ≠ 0 := by
        intro t ht
        rw [uIcc_of_le horder, Set.mem_Icc] at ht
        have htBound : |t| <= T := abs_le.2 ht
        have hsPos : 0 < (path t).re := by
          simpa [path] using hsigma1Pos
        have hsOne : path t ≠ 1 := by
          intro hs
          have hre := congrArg Complex.re hs
          simp [path] at hre
          linarith
        have hregion :
            1 - c / Real.log (|t| + 4) <= sigma1 := by
          simpa only [sigma1] using
            dirichletPerronLeftLine_riemannZetaZeroFree
              h.riemannZetaZeroFree hT htBound
        have hzeta := h.riemannZetaZeroFree.2.2 t sigma1 hregion
        have hzetaPath : riemannZeta (path t) ≠ 0 := by
          simpa only [path] using hzeta
        exact ⟨hsPos, hsOne, hzetaPath⟩
      have hregularized : ContinuousOn
          (fun t => -logDeriv
            (DirichletCharacter.LFunctionTrivChar₁ q) (path t))
          (Set.uIcc (-T) T) := by
        have hcontinuous :=
          DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁
            (n := q)
        have hcomp := hcontinuous.comp hpath.continuousOn (by
          intro t ht
          exact Or.inr
            (principalLFunction_ne_zero_of_re_pos_of_riemannZeta_ne_zero
              (hprincipal t ht).1 (hprincipal t ht).2.1
              (hprincipal t ht).2.2))
        refine hcomp.congr ?_
        intro t _ht
        simp only [Function.comp_apply, logDeriv_apply, neg_div]
      have hpole : ContinuousOn (fun t => 1 / (path t - 1))
          (Set.uIcc (-T) T) := by
        exact continuousOn_const.div
          (hpath.continuousOn.sub continuousOn_const)
          (fun t ht => sub_ne_zero.mpr (hprincipal t ht).2.1)
      refine (hregularized.add hpole).congr ?_
      intro t ht
      exact neg_logDeriv_principal_eq_neg_logDeriv_LFunctionTrivChar₁_add_inv
        (hprincipal t ht).1 (hprincipal t ht).2.1 (hprincipal t ht).2.2
    · have hnonzero : MapsTo path (Set.uIcc (-T) T)
          {s | chi.LFunction s ≠ 0} := by
        intro t ht
        rw [uIcc_of_le horder, Set.mem_Icc] at ht
        have htBound : |t| <= T := abs_le.2 ht
        have hregion :
            1 - c / Real.log ((q : Real) * (|t| + 4)) <= sigma1 := by
          simpa only [sigma1] using
            dirichletPerronLeftLine_zeroFree
              h.nonprincipalZeroFree hT htBound
        change chi.LFunction (path t) ≠ 0
        simpa only [path] using
          h.nonprincipalZeroFree.2.2 chi hq hchi t sigma1 hregion
      have hcontinuous :=
        DirichletCharacter.continuousOn_neg_logDeriv_LFunction_of_nontriv hchi
      have hcomp := hcontinuous.comp hpath.continuousOn hnonzero
      refine hcomp.congr ?_
      intro t _ht
      simp only [Function.comp_apply, logDeriv_apply, neg_div]
  simpa only [sigma1, path] using
    intervalIntegrable_logDerivPerronIntegrand_comp
      hx hpath.continuousOn hlog hpath0

end PrimesRestrictedDigits
