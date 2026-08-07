import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaHeightPole

/-!
# Selected radius-two divisors of regularized zeta

This module retains an arbitrary finite submultiset of the ordinary
radius-two divisor that SEM-482 previously discarded. It does not claim that
the radius-two disk contains every local-height nontrivial zeta zero.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 84,
Lemma 8.2(b), printed pp. 89--91, Lemmas 8.5--8.6, and printed p. 119,
Lemma 12.2. Semantic review: `SEM-490`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Metric

/-- A multiplicity-bounded submultiset contributes at most the full
radius-two ordinary divisor sum on `Re(s)>=1`. -/
theorem selected_radiusTwo_riemannZeta₁_subdivisor_sum_le_re_analyticOrder_finsum
    (t : ℝ) (s : ℂ) (hs : 1 ≤ s.re) (Z : ℂ →₀ ℕ)
    (hZ : ∀ rho : ℂ,
      Z rho ≤
        if dist rho ((2 : ℂ) + t * I) ≤ 2 then
          analyticOrderNatAt riemannZeta₁ rho
        else 0) :
    Z.sum (fun rho m =>
        (m : ℝ) * (((s - rho)⁻¹).re)) ≤
      (∑ᶠ rho : ℂ,
        ((if dist rho ((2 : ℂ) + t * I) ≤ 2 then
            analyticOrderNatAt riemannZeta₁ rho
          else 0 : ℕ) : ℂ) / (s - rho)).re := by
  let m : ℂ → ℕ := fun rho =>
    if dist rho ((2 : ℂ) + t * I) ≤ 2 then
      analyticOrderNatAt riemannZeta₁ rho
    else 0
  have hm : (Function.support m).Finite :=
    radiusTwoAnalyticOrder_hasFiniteSupport t
  have hZsupport : Z.support ⊆ hm.toFinset := by
    intro rho hrho
    apply hm.mem_toFinset.mpr
    rw [Function.mem_support]
    intro hmrho
    have hZrho : Z rho = 0 :=
      Nat.eq_zero_of_le_zero ((hZ rho).trans_eq hmrho)
    exact Finsupp.mem_support_iff.mp hrho hZrho
  have hfullSupport :
      Function.support (fun rho : ℂ => (m rho : ℂ) / (s - rho)) ⊆
        hm.toFinset := by
    intro rho hrho
    apply hm.mem_toFinset.mpr
    rw [Function.mem_support] at hrho ⊢
    exact fun hmrho => hrho (by simp [hmrho])
  have hfullSum :
      (∑ᶠ rho : ℂ, (m rho : ℂ) / (s - rho)) =
        ∑ rho ∈ hm.toFinset, (m rho : ℂ) / (s - rho) :=
    finsum_eq_sum_of_support_subset
      (fun rho : ℂ => (m rho : ℂ) / (s - rho)) hfullSupport
  rw [Finsupp.sum_of_support_subset Z hZsupport _ (by simp)]
  change (∑ rho ∈ hm.toFinset,
      (Z rho : ℝ) * ((s - rho)⁻¹).re) ≤
    (∑ᶠ rho : ℂ, (m rho : ℂ) / (s - rho)).re
  rw [hfullSum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro rho _
  by_cases hmrho : m rho = 0
  · have hZrho : Z rho = 0 :=
      Nat.eq_zero_of_le_zero ((hZ rho).trans_eq hmrho)
    simp [hZrho, hmrho]
  · have hzero : riemannZeta₁ rho = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero (by
        dsimp [m] at hmrho
        split at hmrho
        · exact hmrho
        · exact False.elim (hmrho rfl))
    have hrho : rho.re < 1 := riemannZeta₁_zero_re_lt_one hzero
    have hinv : 0 ≤ ((s - rho)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg (by simp only [Complex.sub_re]; linarith)
        (Complex.normSq_nonneg _)
    have hcoeff : (Z rho : ℝ) ≤ (m rho : ℝ) := by
      exact_mod_cast hZ rho
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hcoeff hinv

/-- The regularized-zeta fixed-disk lower bound for every
multiplicity-bounded radius-two submultiset. -/
theorem exists_nat_selected_radiusTwo_subdivisor_sum_sub_le_re_logDeriv_riemannZeta₁ :
    ∃ A : ℕ, 1 ≤ A ∧
      ∀ (t sigma : ℝ) (Z : ℂ →₀ ℕ),
        1 ≤ sigma → sigma ≤ 2 →
          riemannZeta₁ ((sigma : ℂ) + t * I) ≠ 0 →
            (∀ rho : ℂ,
              Z rho ≤
                if dist rho ((2 : ℂ) + t * I) ≤ 2 then
                  analyticOrderNatAt riemannZeta₁ rho
                else 0) →
              Z.sum (fun rho m =>
                  (m : ℝ) *
                    ((((sigma : ℂ) + t * I) - rho)⁻¹).re) -
                  16 * (A : ℝ) * Real.log (|t| + 2) ≤
                (logDeriv riemannZeta₁
                  ((sigma : ℂ) + t * I)).re := by
  obtain ⟨A, hA, hfixed⟩ :=
    exists_nat_norm_logDeriv_riemannZeta₁_sub_radiusTwo_finsum_le
  refine ⟨A, hA, ?_⟩
  intro t sigma Z hsigma1 hsigma2 hzs hZ
  let s : ℂ := (sigma : ℂ) + t * I
  let E : ℝ := 16 * (A : ℝ) * Real.log (|t| + 2)
  let S : ℂ := ∑ᶠ rho : ℂ,
    ((if dist rho ((2 : ℂ) + t * I) ≤ 2 then
        analyticOrderNatAt riemannZeta₁ rho
      else 0 : ℕ) : ℂ) / (s - rho)
  have hsball : s ∈ closedBall ((2 : ℂ) + t * I) 1 := by
    rw [mem_closedBall, Complex.dist_eq]
    have hdiff : s - ((2 : ℂ) + t * I) = ((sigma - 2 : ℝ) : ℂ) := by
      simp [s]
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hsre : 1 ≤ s.re := by
    simpa [s] using hsigma1
  have hnorm : ‖logDeriv riemannZeta₁ s - S‖ ≤ E := by
    simpa [S, E, s] using hfixed t s hsball (by simpa [s] using hzs)
  have hselected :
      Z.sum (fun rho m =>
        (m : ℝ) * (((s - rho)⁻¹).re)) ≤ S.re := by
    simpa [S] using
      selected_radiusTwo_riemannZeta₁_subdivisor_sum_le_re_analyticOrder_finsum
        t s hsre Z hZ
  have hnormSwap : ‖S - logDeriv riemannZeta₁ s‖ ≤ E := by
    rw [norm_sub_rev]
    exact hnorm
  have hreal :
      (S - logDeriv riemannZeta₁ s).re ≤
        ‖S - logDeriv riemannZeta₁ s‖ :=
    Complex.re_le_norm _
  have hresult :
      Z.sum (fun rho m =>
          (m : ℝ) * (((s - rho)⁻¹).re)) - E ≤
        (logDeriv riemannZeta₁ s).re := by
    rw [Complex.sub_re] at hreal
    linarith
  simpa [s, E] using hresult

/-- The selected regularized-zeta lower bound after restoring the exact
complex pole of the Riemann zeta function. -/
theorem exists_nat_selected_radiusTwo_subdivisor_sum_sub_pole_le_re_logDeriv_riemannZeta :
    ∃ A : ℕ, 1 ≤ A ∧
      ∀ (t sigma : ℝ) (Z : ℂ →₀ ℕ),
        1 < sigma → sigma ≤ 2 →
          (∀ rho : ℂ,
            Z rho ≤
              if dist rho ((2 : ℂ) + t * I) ≤ 2 then
                analyticOrderNatAt riemannZeta₁ rho
              else 0) →
            Z.sum (fun rho m =>
                (m : ℝ) *
                  ((((sigma : ℂ) + t * I) - rho)⁻¹).re) -
                ((((sigma : ℂ) + t * I) - 1)⁻¹).re -
                16 * (A : ℝ) * Real.log (|t| + 2) ≤
              (logDeriv riemannZeta
                ((sigma : ℂ) + t * I)).re := by
  obtain ⟨A, hA, hselected⟩ :=
    exists_nat_selected_radiusTwo_subdivisor_sum_sub_le_re_logDeriv_riemannZeta₁
  refine ⟨A, hA, ?_⟩
  intro t sigma Z hsigma1 hsigma2 hZ
  let s : ℂ := (sigma : ℂ) + t * I
  have hsre : 1 ≤ s.re := by simp [s]; linarith
  have hsne : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [s] at this
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hsre
  have hzeta₁ : riemannZeta₁ s ≠ 0 := by
    intro hzero
    have hfactor := riemannZeta_eq_inv_sub_mul hsne
    rw [hzero, mul_zero] at hfactor
    exact hzeta hfactor
  have hlower := hselected t sigma Z hsigma1.le hsigma2 hzeta₁ hZ
  have hpole := congrArg Complex.re
    (neg_logDeriv_riemannZeta_eq_pole_sub_regularized s hsre hsne)
  simp only [Complex.neg_re, Complex.sub_re] at hpole
  simpa [s] using (show
    Z.sum (fun rho m =>
        (m : ℝ) * (((s - rho)⁻¹).re)) - ((s - 1)⁻¹).re -
          16 * (A : ℝ) * Real.log (|t| + 2) ≤
        (logDeriv riemannZeta s).re by linarith)

end BoundedGaps.Maynard
