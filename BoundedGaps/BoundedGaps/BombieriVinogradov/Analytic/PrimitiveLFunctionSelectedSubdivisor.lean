import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionFixedDisk

/-!
# Selected subdivisors of primitive Dirichlet L-functions

This file turns the full ordinary radius-six zero sum into a one-sided bound
for every finite submultiset dominated by analytic multiplicity. It does not
identify the selected points as nontrivial zeros.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 90--91,
Lemma 8.6(a), pp. 112--114, Lemma 11.4 and its zero conventions, and
pp. 119--120, Lemma 12.2. Semantic review: `SEM-480`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

noncomputable section

/-- An ordinary zero of a primitive Dirichlet L-function of modulus greater
than one lies strictly to the left of the line `Re(s)=1`. -/
theorem LFunction_zero_re_lt_one_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {rho : ℂ} (hzero : DirichletCharacter.LFunction chi rho = 0) :
    rho.re < 1 := by
  by_contra hrho
  exact (chi.LFunction_ne_zero_of_one_le_re
    (.inl (character_ne_one_of_isPrimitive hq chi hchi))
    (le_of_not_gt hrho)) hzero

private theorem radiusSixAnalyticOrder_hasFiniteSupport
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) :
    Function.HasFiniteSupport fun rho : ℂ =>
      if dist rho ((2 : ℂ) + t * I) ≤ 6 then
        analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
      else 0 := by
  apply (divisor_LFunction_closedBall_support_finite
    (character_ne_one_of_isPrimitive hq chi hchi)
    ((2 : ℂ) + t * I) 6).subset
  intro rho hrho
  rw [Function.mem_support] at hrho ⊢
  rw [divisor_LFunction_radiusSix_apply hq chi hchi t rho]
  exact_mod_cast hrho

/-- A multiplicity-bounded submultiset contributes at most the full ordinary
radius-six zero sum on the half-plane `Re(s)>=1`. -/
theorem selected_radiusSix_subdivisor_sum_le_re_analyticOrder_finsum
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) (s : ℂ) (hs : 1 ≤ s.re) (Z : ℂ →₀ ℕ)
    (hZ : ∀ rho : ℂ,
      Z rho ≤
        if dist rho ((2 : ℂ) + t * I) ≤ 6 then
          analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
        else 0) :
    Z.sum (fun rho m =>
        (m : ℝ) * (((s - rho)⁻¹).re)) ≤
      (∑ᶠ rho : ℂ,
        ((if dist rho ((2 : ℂ) + t * I) ≤ 6 then
            analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
          else 0 : ℕ) : ℂ) / (s - rho)).re := by
  let m : ℂ → ℕ := fun rho =>
    if dist rho ((2 : ℂ) + t * I) ≤ 6 then
      analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
    else 0
  have hm : (Function.support m).Finite :=
    radiusSixAnalyticOrder_hasFiniteSupport hq chi hchi t
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
  · have hzero : DirichletCharacter.LFunction chi rho = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero (by
        dsimp [m] at hmrho
        split at hmrho
        · exact hmrho
        · exact False.elim (hmrho rfl))
    have hrho : rho.re < 1 :=
      LFunction_zero_re_lt_one_of_isPrimitive hq chi hchi hzero
    have hinv : 0 ≤ ((s - rho)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg (by simp only [Complex.sub_re]; linarith)
        (Complex.normSq_nonneg _)
    have hcoeff : (Z rho : ℝ) ≤ (m rho : ℝ) := by
      exact_mod_cast hZ rho
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hcoeff hinv

/-- The primitive fixed-disk lower bound for every multiplicity-bounded
submultiset of the ordinary radius-six divisor. -/
theorem exists_nat_selected_radiusSix_subdivisor_sum_sub_le_re_logDeriv_LFunction :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t sigma : ℝ) (Z : ℂ →₀ ℕ),
            1 ≤ sigma → sigma ≤ 2 →
              DirichletCharacter.LFunction chi
                  ((sigma : ℂ) + t * I) ≠ 0 →
                (∀ rho : ℂ,
                  Z rho ≤
                    if dist rho ((2 : ℂ) + t * I) ≤ 6 then
                      analyticOrderNatAt
                        (DirichletCharacter.LFunction chi) rho
                    else 0) →
                  Z.sum (fun rho m =>
                      (m : ℝ) *
                        ((((sigma : ℂ) + t * I) - rho)⁻¹).re) -
                      16 * ((A : ℝ) *
                        Real.log ((q : ℝ) * (|t| + 2))) / 3 ≤
                    (logDeriv (DirichletCharacter.LFunction chi)
                      ((sigma : ℂ) + t * I)).re := by
  obtain ⟨A, hA, hfixed⟩ :=
    exists_nat_norm_logDeriv_LFunction_sub_radiusSix_analyticOrder_finsum_le
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t sigma Z hsigma1 hsigma2 hLs hZ
  let s : ℂ := (sigma : ℂ) + t * I
  let E : ℝ :=
    16 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) / 3
  let S : ℂ := ∑ᶠ rho : ℂ,
    ((if dist rho ((2 : ℂ) + t * I) ≤ 6 then
        analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
      else 0 : ℕ) : ℂ) / (s - rho)
  have hsball : s ∈ closedBall ((2 : ℂ) + t * I) 3 := by
    rw [mem_closedBall, Complex.dist_eq]
    have hdiff :
        s - ((2 : ℂ) + t * I) = ((sigma - 2 : ℝ) : ℂ) := by
      simp [s]
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hsre : 1 ≤ s.re := by
    simpa [s] using hsigma1
  have hnorm :
      ‖logDeriv (DirichletCharacter.LFunction chi) s - S‖ ≤ E := by
    simpa [S, E] using
      hfixed q hq chi hchi t s hsball (by simpa [s] using hLs)
  have hselected :
      Z.sum (fun rho m =>
        (m : ℝ) * (((s - rho)⁻¹).re)) ≤ S.re := by
    simpa [S] using
      selected_radiusSix_subdivisor_sum_le_re_analyticOrder_finsum
        hq chi hchi t s hsre Z hZ
  have hnormSwap :
      ‖S - logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ E := by
    rw [norm_sub_rev]
    exact hnorm
  have hreal :
      (S - logDeriv (DirichletCharacter.LFunction chi) s).re ≤
        ‖S - logDeriv (DirichletCharacter.LFunction chi) s‖ :=
    Complex.re_le_norm _
  have hresult :
      Z.sum (fun rho m =>
          (m : ℝ) * (((s - rho)⁻¹).re)) - E ≤
        (logDeriv (DirichletCharacter.LFunction chi) s).re := by
    rw [Complex.sub_re] at hreal
    linarith
  simpa [s, E] using hresult

end

end BoundedGaps.Maynard
