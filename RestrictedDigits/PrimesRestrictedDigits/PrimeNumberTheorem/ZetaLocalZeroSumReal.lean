import Mathlib.NumberTheory.LSeries.ZetaZeros
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLocalZeros

/-!
# Real-part bounds for the local zeta-zero sum

This file records the positivity and selected-zero consequences of the
multiplicity-weighted local divisor used in `MONTGOMERY-VAUGHAN-MNT-I`,
Chapter 6, Theorems 6.6--6.7. The closed radius-`5 / 6` disk and its analytic
multiplicities are exactly those in `riemannZetaLocalZeroSum`.
-/

open Complex Metric Set
open MeromorphicOn

namespace PrimesRestrictedDigits

/-- The closed-disk divisor used by `riemannZetaLocalZeroSum`, exposed so
later zero-free estimates can state support and multiplicity hypotheses
without unfolding the sum. -/
noncomputable def riemannZetaLocalDivisor (t : Real) :=
  MeromorphicOn.divisor riemannZeta
    (closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
      (5 / 6 : Real))

private lemma one_not_mem_riemannZetaLocalDivisor_closedBall
    {t : Real} (hT : 7 / 8 <= |t|) :
    (1 : Complex) ∉ closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
      (5 / 6 : Real) := by
  let c : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  intro hOne
  have hDist : dist (1 : Complex) c <= (5 / 6 : Real) := mem_closedBall.mp hOne
  have hIm : |t| <= norm ((1 : Complex) - c) := by
    have h := Complex.abs_im_le_norm ((1 : Complex) - c)
    have hEq : ((1 : Complex) - c).im = -t := by
      dsimp [c]
      norm_num
    rwa [hEq, abs_neg] at h
  have : |t| <= (5 / 6 : Real) :=
    hIm.trans (by simpa only [dist_eq_norm] using hDist)
  norm_num at hT this
  linarith

private lemma analyticOnNhd_riemannZeta_localDivisor_closedBall
    {t : Real} (hT : 7 / 8 <= |t|) :
    AnalyticOnNhd Complex riemannZeta
      (closedBall
        (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
        (5 / 6 : Real)) := by
  apply analyticOn_riemannZeta.mono
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hzOne
  subst z
  exact one_not_mem_riemannZetaLocalDivisor_closedBall hT hz

private lemma riemannZetaLocalDivisor_support_zero
    {t : Real} (hT : 7 / 8 <= |t|) {rho : Complex}
    (hRho : rho ∈ (riemannZetaLocalDivisor t).support) :
    riemannZeta rho = 0 := by
  have hf := analyticOnNhd_riemannZeta_localDivisor_closedBall hT
  have hMem := (riemannZetaLocalDivisor t).supportWithinDomain hRho
  have hAt := hf rho hMem
  by_contra hZero
  have hOrder : analyticOrderAt riemannZeta rho = 0 :=
    hAt.analyticOrderAt_eq_zero.mpr hZero
  have hDivisor : riemannZetaLocalDivisor t rho = 0 := by
    rw [riemannZetaLocalDivisor, hf.divisor_apply hMem, hOrder]
    simp
  exact hRho hDivisor

/-- A point in the support of the high-height local divisor is a zeta zero. -/
theorem riemannZetaLocalDivisor_support_mem_riemannZetaZeros
    {t : Real} (hT : 7 / 8 <= |t|) {rho : Complex}
    (hRho : rho ∈ (riemannZetaLocalDivisor t).support) :
    rho ∈ riemannZetaZeros := by
  exact riemannZetaLocalDivisor_support_zero hT hRho

/-- Every zero represented by the high-height local divisor lies strictly to
the left of the closed half-plane where zeta is known not to vanish. -/
theorem riemannZetaLocalDivisor_support_re_lt_one
    {t : Real} (hT : 7 / 8 <= |t|) {rho : Complex}
    (hRho : rho ∈ (riemannZetaLocalDivisor t).support) :
    rho.re < 1 := by
  have hZero := riemannZetaLocalDivisor_support_zero hT hRho
  by_contra hRe
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hRe) hZero

/-- Analyticity of zeta on the local disk makes every local multiplicity
nonnegative. -/
theorem riemannZetaLocalDivisor_nonneg
    {t : Real} (hT : 7 / 8 <= |t|) (rho : Complex) :
    0 <= riemannZetaLocalDivisor t rho := by
  exact (analyticOnNhd_riemannZeta_localDivisor_closedBall hT).divisor_nonneg rho

private lemma riemannZetaLocalDivisor_finiteOrder
    {t : Real} (hT : 7 / 8 <= |t|) {rho : Complex}
    (hRho : rho ∈ closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
      (5 / 6 : Real)) :
    analyticOrderAt riemannZeta rho ≠ ⊤ := by
  let c : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  have hf := analyticOnNhd_riemannZeta_localDivisor_closedBall hT
  have hcMem : c ∈ closedBall c (5 / 6 : Real) := by norm_num
  have hcZero : analyticOrderAt riemannZeta c = 0 := by
    apply (hf c hcMem).analyticOrderAt_eq_zero.mpr
    exact norm_pos_iff.mp
      ((by norm_num : (0 : Real) < 1 / 4).trans_le
        (one_fourth_le_norm_riemannZeta_three_halves_add_mul_I t))
  apply hf.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall c (5 / 6 : Real)).isPreconnected hcMem
    (by simpa [c] using hRho)
  simp [hcZero]

private lemma one_le_riemannZetaLocalDivisor_of_zero
    {t beta : Real} (hT : 7 / 8 <= |t|) (hBeta : 5 / 6 <= beta)
    (hZero : riemannZeta
      ((beta : Complex) + Complex.I * (t : Complex)) = 0) :
    1 <= riemannZetaLocalDivisor t
      ((beta : Complex) + Complex.I * (t : Complex)) := by
  let rho : Complex := (beta : Complex) + Complex.I * t
  have hBetaOne : beta < 1 := by
    by_contra hBetaOne
    exact riemannZeta_ne_zero_of_one_le_re (s := rho)
      (by simpa [rho] using not_lt.mp hBetaOne)
      (by simpa [rho] using hZero)
  have hRhoMem : rho ∈ closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
      (5 / 6 : Real) := by
    simp only [mem_closedBall, dist_eq_norm]
    have hEq :
        rho - (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex)) =
          ((beta - 3 / 2 : Real) : Complex) := by
      apply Complex.ext <;> simp [rho]
    rw [hEq, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hf := analyticOnNhd_riemannZeta_localDivisor_closedBall hT
  have hAt := hf rho hRhoMem
  have hOrderFinite := riemannZetaLocalDivisor_finiteOrder hT hRhoMem
  have hDivisorNat : riemannZetaLocalDivisor t rho =
      (analyticOrderNatAt riemannZeta rho : Int) := by
    rw [riemannZetaLocalDivisor, hf.divisor_apply hRhoMem,
      <- Nat.cast_analyticOrderNatAt hOrderFinite]
    simp
  have hOrderNe : analyticOrderNatAt riemannZeta rho ≠ 0 := by
    intro hOrderZero
    have : analyticOrderAt riemannZeta rho = 0 := by
      rw [<- Nat.cast_analyticOrderNatAt hOrderFinite, hOrderZero]
      simp
    exact hAt.analyticOrderAt_ne_zero.mpr (by simpa [rho] using hZero) this
  rw [hDivisorNat]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hOrderNe

private lemma localReciprocal_re_nonneg
    {sigma t : Real} {rho : Complex} (hRe : rho.re < sigma) :
    0 <= (1 / (((sigma : Complex) + Complex.I * (t : Complex)) - rho)).re := by
  rw [one_div, Complex.inv_re]
  apply div_nonneg
  · simpa using hRe.le
  · exact Complex.normSq_nonneg _

/-- Every multiplicity-weighted reciprocal term in the high-height local
divisor has nonnegative real part when evaluated to the right of one. -/
theorem riemannZetaLocalZeroTerm_re_nonneg
    {t sigma : Real} (hT : 7 / 8 <= |t|) (hSigma : 1 < sigma)
    (rho : Complex) :
    0 <= (((riemannZetaLocalDivisor t rho : Int) : Complex) /
      (((sigma : Complex) + Complex.I * (t : Complex)) - rho)).re := by
  by_cases hRho : rho ∈ (riemannZetaLocalDivisor t).support
  · have hCoeff : (0 : Real) <= (riemannZetaLocalDivisor t rho : Int) := by
      exact_mod_cast riemannZetaLocalDivisor_nonneg hT rho
    have hRecip := localReciprocal_re_nonneg
      (t := t) (show rho.re < sigma from
        (riemannZetaLocalDivisor_support_re_lt_one hT hRho).trans hSigma)
    rw [div_eq_mul_inv, Complex.mul_re]
    norm_num
    exact mul_nonneg hCoeff (by simpa [one_div, Complex.inv_re] using hRecip)
  · have hCoeff : riemannZetaLocalDivisor t rho = 0 := by
      simpa [Function.mem_support] using hRho
    simp [hCoeff]

/-- At every real coordinate strictly larger than one, the real part of the
full multiplicity-weighted local zero sum is nonnegative. -/
theorem riemannZetaLocalZeroSum_re_nonneg
    {t sigma : Real} (hT : 7 / 8 <= |t|) (hSigma : 1 < sigma) :
    0 <= (riemannZetaLocalZeroSum t
      ((sigma : Complex) + Complex.I * (t : Complex))).re := by
  let D := riemannZetaLocalDivisor t
  let phi : Complex -> Complex := fun rho =>
    ((D rho : Int) : Complex) /
      (((sigma : Complex) + Complex.I * (t : Complex)) - rho)
  have hD : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
      (5 / 6 : Real))
  have hPhiSupp : phi.support ⊆ D.support := by
    intro rho hRho
    contrapose! hRho
    have : D rho = 0 := by simpa [Function.mem_support] using hRho
    simp [phi, this]
  have hPhi : (∑ᶠ rho : Complex, phi rho) =
      ∑ rho ∈ hD.toFinset, phi rho :=
    finsum_eq_sum_of_support_subset _
      (hPhiSupp.trans (fun rho hRho => hD.mem_toFinset.mpr hRho))
  rw [riemannZetaLocalZeroSum]
  change 0 <= (∑ᶠ rho : Complex, phi rho).re
  rw [hPhi]
  change 0 <= Complex.reCLM (∑ rho ∈ hD.toFinset, phi rho)
  simp only [map_sum]
  exact Finset.sum_nonneg fun rho _ => by
    simpa [D, phi] using riemannZetaLocalZeroTerm_re_nonneg hT hSigma rho

/-- A zero at the evaluation height with real part at least `5 / 6`
contributes at least its simple reciprocal to the full local zero sum. The
divisor coefficient retains the zero's full analytic multiplicity. -/
theorem one_div_sub_le_riemannZetaLocalZeroSum_re
    {t beta sigma : Real} (hT : 7 / 8 <= |t|) (hBeta : 5 / 6 <= beta)
    (hZero : riemannZeta
      ((beta : Complex) + Complex.I * (t : Complex)) = 0)
    (hSigma : 1 < sigma) :
    1 / (sigma - beta) <=
      (riemannZetaLocalZeroSum t
        ((sigma : Complex) + Complex.I * (t : Complex))).re := by
  let D := riemannZetaLocalDivisor t
  let rho0 : Complex := (beta : Complex) + Complex.I * t
  let phi : Complex -> Complex := fun rho =>
    ((D rho : Int) : Complex) /
      (((sigma : Complex) + Complex.I * (t : Complex)) - rho)
  have hCoeff : 1 <= D rho0 := by
    simpa [D, rho0] using one_le_riemannZetaLocalDivisor_of_zero hT hBeta hZero
  have hRho0 : rho0 ∈ D.support := by
    rw [Function.mem_support]
    exact ne_of_gt (lt_of_lt_of_le Int.zero_lt_one hCoeff)
  have hD : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
      (5 / 6 : Real))
  have hPhiSupp : phi.support ⊆ D.support := by
    intro rho hRho
    contrapose! hRho
    have : D rho = 0 := by simpa [Function.mem_support] using hRho
    simp [phi, this]
  have hPhi : (∑ᶠ rho : Complex, phi rho) =
      ∑ rho ∈ hD.toFinset, phi rho :=
    finsum_eq_sum_of_support_subset _
      (hPhiSupp.trans (fun rho hRho => hD.mem_toFinset.mpr hRho))
  have hBetaOne : beta < 1 := by
    by_contra hBetaOne
    exact riemannZeta_ne_zero_of_one_le_re (s := rho0)
      (by simpa [rho0] using not_lt.mp hBetaOne)
      (by simpa [rho0] using hZero)
  have hDenom : 0 < sigma - beta := by linarith
  have hTerm : 1 / (sigma - beta) <= (phi rho0).re := by
    have hCoeffReal : (1 : Real) <= (D rho0 : Int) := by exact_mod_cast hCoeff
    have hDiff :
        ((sigma : Complex) + Complex.I * (t : Complex)) - rho0 =
          ((sigma - beta : Real) : Complex) := by
      apply Complex.ext <;> simp [rho0]
    dsimp [phi]
    rw [hDiff]
    rw [Complex.div_re, Complex.normSq_apply]
    norm_num
    field_simp [hDenom.ne']
    exact hCoeffReal
  rw [riemannZetaLocalZeroSum]
  change 1 / (sigma - beta) <= (∑ᶠ rho : Complex, phi rho).re
  rw [hPhi]
  change 1 / (sigma - beta) <=
    Complex.reCLM (∑ rho ∈ hD.toFinset, phi rho)
  simp only [map_sum]
  exact hTerm.trans (Finset.single_le_sum
    (fun rho _ => by
      simpa [D, phi] using riemannZetaLocalZeroTerm_re_nonneg hT hSigma rho)
    (hD.mem_toFinset.mpr hRho0))

end PrimesRestrictedDigits
