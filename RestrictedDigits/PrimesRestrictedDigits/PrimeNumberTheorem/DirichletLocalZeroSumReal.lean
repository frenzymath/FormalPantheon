import Mathlib.NumberTheory.LSeries.Nonvanishing
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletLocalZeros

/-!
# Real-part bounds for local Dirichlet zero sums

This file formalizes the positivity and selected-zero consequences used in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.3, Cases 1--2. The local
sum retains the closed disk and analytic multiplicities from Lemma 11.1.
-/

open Complex Metric Set
open MeromorphicOn

namespace PrimesRestrictedDigits

/-- The closed-disk divisor used by `dirichletLFunctionLocalZeroSum`. -/
noncomputable def dirichletLFunctionLocalDivisor
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q) (t : Real) :=
  MeromorphicOn.divisor chi.LFunction
    (closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
      (5 / 6 : Real))

private lemma analyticOnNhd_dirichletLFunction_localDivisor_closedBall
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (t : Real) :
    AnalyticOnNhd Complex chi.LFunction
      (closedBall
        (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
        (5 / 6 : Real)) := by
  have hEntire : AnalyticOnNhd Complex chi.LFunction Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (chi.differentiable_LFunction hchi)
  exact hEntire.mono (Set.subset_univ _)

/-- Every point in the support of a nonprincipal local divisor is an
L-function zero. -/
theorem dirichletLFunctionLocalDivisor_support_zero
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) {t : Real} {rho : Complex}
    (hRho : rho ∈ (dirichletLFunctionLocalDivisor chi t).support) :
    chi.LFunction rho = 0 := by
  have hf := analyticOnNhd_dirichletLFunction_localDivisor_closedBall hchi t
  have hMem := (dirichletLFunctionLocalDivisor chi t).supportWithinDomain hRho
  have hAt := hf rho hMem
  by_contra hZero
  have hOrder : analyticOrderAt chi.LFunction rho = 0 :=
    hAt.analyticOrderAt_eq_zero.mpr hZero
  have hDivisor : dirichletLFunctionLocalDivisor chi t rho = 0 := by
    rw [dirichletLFunctionLocalDivisor, hf.divisor_apply hMem, hOrder]
    simp
  exact hRho hDivisor

/-- Every zero represented by a nonprincipal local divisor lies strictly to
the left of the closed half-plane where its L-function is nonvanishing. -/
theorem dirichletLFunctionLocalDivisor_support_re_lt_one
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) {t : Real} {rho : Complex}
    (hRho : rho ∈ (dirichletLFunctionLocalDivisor chi t).support) :
    rho.re < 1 := by
  have hZero := dirichletLFunctionLocalDivisor_support_zero hchi hRho
  by_contra hRe
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (.inl hchi)
    (not_lt.mp hRe) hZero

/-- Analyticity of a nonprincipal L-function makes every local divisor
coefficient nonnegative. -/
theorem dirichletLFunctionLocalDivisor_nonneg
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (t : Real) (rho : Complex) :
    0 ≤ dirichletLFunctionLocalDivisor chi t rho := by
  exact (analyticOnNhd_dirichletLFunction_localDivisor_closedBall hchi t)
    |>.divisor_nonneg rho

private lemma dirichletLFunctionLocalDivisor_finiteOrder
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) {t : Real} {rho : Complex}
    (hRho : rho ∈ closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
      (5 / 6 : Real)) :
    analyticOrderAt chi.LFunction rho ≠ ⊤ := by
  let c : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  have hf := analyticOnNhd_dirichletLFunction_localDivisor_closedBall hchi t
  have hcMem : c ∈ closedBall c (5 / 6 : Real) := by norm_num
  have hcZero : analyticOrderAt chi.LFunction c = 0 := by
    apply (hf c hcMem).analyticOrderAt_eq_zero.mpr
    exact norm_pos_iff.mp
      ((by norm_num : (0 : Real) < 1 / 4).trans_le
        (one_fourth_le_norm_LFunction_three_halves_add_mul_I chi t))
  apply hf.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall c (5 / 6 : Real)).isPreconnected hcMem
    (by simpa [c] using hRho)
  simp [hcZero]

private lemma one_le_dirichletLFunctionLocalDivisor_of_zero
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) {t beta : Real} (hBeta : 5 / 6 ≤ beta)
    (hZero : chi.LFunction
      ((beta : Complex) + Complex.I * (t : Complex)) = 0) :
    1 ≤ dirichletLFunctionLocalDivisor chi t
      ((beta : Complex) + Complex.I * (t : Complex)) := by
  let rho : Complex := (beta : Complex) + Complex.I * t
  have hBetaOne : beta < 1 := by
    by_contra hBetaOne
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (.inl hchi)
      (s := rho) (by simpa [rho] using not_lt.mp hBetaOne)
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
  have hf := analyticOnNhd_dirichletLFunction_localDivisor_closedBall hchi t
  have hAt := hf rho hRhoMem
  have hOrderFinite :=
    dirichletLFunctionLocalDivisor_finiteOrder hchi hRhoMem
  have hDivisorNat : dirichletLFunctionLocalDivisor chi t rho =
      (analyticOrderNatAt chi.LFunction rho : Int) := by
    rw [dirichletLFunctionLocalDivisor, hf.divisor_apply hRhoMem,
      ← Nat.cast_analyticOrderNatAt hOrderFinite]
    simp
  have hOrderNe : analyticOrderNatAt chi.LFunction rho ≠ 0 := by
    intro hOrderZero
    have : analyticOrderAt chi.LFunction rho = 0 := by
      rw [← Nat.cast_analyticOrderNatAt hOrderFinite, hOrderZero]
      simp
    exact hAt.analyticOrderAt_ne_zero.mpr (by simpa [rho] using hZero) this
  rw [hDivisorNat]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hOrderNe

private lemma localDirichletReciprocal_re_nonneg
    {sigma t : Real} {rho : Complex} (hRe : rho.re < sigma) :
    0 ≤ (1 / (((sigma : Complex) + Complex.I * (t : Complex)) - rho)).re := by
  rw [one_div, Complex.inv_re]
  apply div_nonneg
  · simpa using hRe.le
  · exact Complex.normSq_nonneg _

/-- Every multiplicity-weighted reciprocal term in a nonprincipal local
divisor has nonnegative real part when evaluated to the right of one. -/
theorem dirichletLFunctionLocalZeroTerm_re_nonneg
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) {t sigma : Real} (hSigma : 1 < sigma)
    (rho : Complex) :
    0 ≤ (((dirichletLFunctionLocalDivisor chi t rho : Int) : Complex) /
      (((sigma : Complex) + Complex.I * (t : Complex)) - rho)).re := by
  by_cases hRho : rho ∈ (dirichletLFunctionLocalDivisor chi t).support
  · have hCoeff : (0 : Real) ≤
        (dirichletLFunctionLocalDivisor chi t rho : Int) := by
      exact_mod_cast dirichletLFunctionLocalDivisor_nonneg hchi t rho
    have hRecip := localDirichletReciprocal_re_nonneg
      (t := t) (show rho.re < sigma from
        (dirichletLFunctionLocalDivisor_support_re_lt_one hchi hRho).trans hSigma)
    rw [div_eq_mul_inv, Complex.mul_re]
    norm_num
    exact mul_nonneg hCoeff (by simpa [one_div, Complex.inv_re] using hRecip)
  · have hCoeff : dirichletLFunctionLocalDivisor chi t rho = 0 := by
      simpa [Function.mem_support] using hRho
    simp [hCoeff]

/-- At every same-height coordinate strictly larger than one, the real part
of the full nonprincipal local zero sum is nonnegative. -/
theorem dirichletLFunctionLocalZeroSum_re_nonneg
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) {t sigma : Real} (hSigma : 1 < sigma) :
    0 ≤ (dirichletLFunctionLocalZeroSum chi t
      ((sigma : Complex) + Complex.I * (t : Complex))).re := by
  let D := dirichletLFunctionLocalDivisor chi t
  let phi : Complex → Complex := fun rho =>
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
  rw [dirichletLFunctionLocalZeroSum]
  change 0 ≤ (∑ᶠ rho : Complex, phi rho).re
  rw [hPhi]
  change 0 ≤ Complex.reCLM (∑ rho ∈ hD.toFinset, phi rho)
  simp only [map_sum]
  exact Finset.sum_nonneg fun rho _ => by
    simpa [D, phi] using
      dirichletLFunctionLocalZeroTerm_re_nonneg hchi hSigma rho

/-- A same-height zero with real part at least `5 / 6` contributes at least
its simple reciprocal to the full nonprincipal local zero sum. -/
theorem one_div_sub_le_dirichletLFunctionLocalZeroSum_re
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) {t beta sigma : Real} (hBeta : 5 / 6 ≤ beta)
    (hZero : chi.LFunction
      ((beta : Complex) + Complex.I * (t : Complex)) = 0)
    (hSigma : 1 < sigma) :
    1 / (sigma - beta) ≤
      (dirichletLFunctionLocalZeroSum chi t
        ((sigma : Complex) + Complex.I * (t : Complex))).re := by
  let D := dirichletLFunctionLocalDivisor chi t
  let rho0 : Complex := (beta : Complex) + Complex.I * t
  let phi : Complex → Complex := fun rho =>
    ((D rho : Int) : Complex) /
      (((sigma : Complex) + Complex.I * (t : Complex)) - rho)
  have hCoeff : 1 ≤ D rho0 := by
    simpa [D, rho0] using
      one_le_dirichletLFunctionLocalDivisor_of_zero hchi hBeta hZero
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
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (.inl hchi)
      (s := rho0) (by simpa [rho0] using not_lt.mp hBetaOne)
      (by simpa [rho0] using hZero)
  have hDenom : 0 < sigma - beta := by linarith
  have hTerm : 1 / (sigma - beta) ≤ (phi rho0).re := by
    have hCoeffReal : (1 : Real) ≤ (D rho0 : Int) := by exact_mod_cast hCoeff
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
  rw [dirichletLFunctionLocalZeroSum]
  change 1 / (sigma - beta) ≤ (∑ᶠ rho : Complex, phi rho).re
  rw [hPhi]
  change 1 / (sigma - beta) ≤
    Complex.reCLM (∑ rho ∈ hD.toFinset, phi rho)
  simp only [map_sum]
  exact hTerm.trans (Finset.single_le_sum
    (fun rho _ => by
      simpa [D, phi] using
        dirichletLFunctionLocalZeroTerm_re_nonneg
          hchi (t := t) (sigma := sigma) hSigma rho)
    (hD.mem_toFinset.mpr hRho0))

end PrimesRestrictedDigits
