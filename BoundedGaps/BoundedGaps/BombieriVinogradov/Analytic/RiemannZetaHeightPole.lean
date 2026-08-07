import BoundedGaps.BombieriVinogradov.Analytic.DirichletLZeroDivisor
import BoundedGaps.BombieriVinogradov.Analytic.FixedDiskLogDerivative
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusFour

/-!
# The arbitrary-height zeta pole estimate

The fixed-disk theorem is applied to the entire function `riemannZeta₁` with
inner radius one. Every zero in its closed radius-two divisor lies strictly
left of `Re(s)=1`, so the divisor sum has nonnegative real part throughout
the evaluation strip and can be discarded. The remaining identity exposes
the exact complex pole `1/(s-1)`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 84,
Lemma 8.2, printed pp. 89--91, Lemma 8.6 and its specialization, and printed
pp. 119--120, Lemma 12.2 and equation (12.5). Semantic review: `SEM-482`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Metric Set

private lemma analyticOnNhd_riemannZeta₁ :
    AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
  differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ

private lemma analyticOrderAt_riemannZeta₁_ne_top (s : ℂ) :
    analyticOrderAt riemannZeta₁ s ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
    (fun z => analyticOnNhd_riemannZeta₁ z (mem_univ z))]
  intro hzero
  have hone := congrFun hzero 1
  change riemannZeta₁ 1 = 0 at hone
  rw [riemannZeta₁_one] at hone
  exact one_ne_zero hone

private lemma divisor_riemannZeta₁_radiusTwo_apply
    (t : ℝ) (rho : ℂ) :
    MeromorphicOn.divisor riemannZeta₁
        (closedBall ((2 : ℂ) + t * I) 2) rho =
      ((if dist rho ((2 : ℂ) + t * I) ≤ 2 then
          analyticOrderNatAt riemannZeta₁ rho
        else 0 : ℕ) : ℤ) := by
  by_cases hrho : dist rho ((2 : ℂ) + t * I) ≤ 2
  · rw [if_pos hrho, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (analyticOnNhd_riemannZeta₁.mono
        (Set.subset_univ (closedBall ((2 : ℂ) + t * I) 2)))
      (mem_closedBall.mpr hrho)]
    have hfinite := analyticOrderAt_riemannZeta₁_ne_top rho
    rw [← Nat.cast_analyticOrderNatAt hfinite, ENat.map_coe,
      WithTop.untop₀_coe]
  · rw [if_neg hrho,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _
        (by simpa [mem_closedBall] using hrho)]
    norm_cast

/-- The radius-two ordinary analytic-order function for `riemannZeta₁` has
finite support. -/
lemma radiusTwoAnalyticOrder_hasFiniteSupport (t : ℝ) :
    Function.HasFiniteSupport fun rho : ℂ =>
      if dist rho ((2 : ℂ) + t * I) ≤ 2 then
        analyticOrderNatAt riemannZeta₁ rho
      else 0 := by
  have hfinite :
      (MeromorphicOn.divisor riemannZeta₁
        (closedBall ((2 : ℂ) + t * I) 2)).support.Finite :=
    (MeromorphicOn.divisor riemannZeta₁
      (closedBall ((2 : ℂ) + t * I) 2)).finiteSupport
        (isCompact_closedBall _ _)
  apply hfinite.subset
  intro rho hrho
  rw [Function.mem_support] at hrho ⊢
  rw [divisor_riemannZeta₁_radiusTwo_apply t rho]
  exact_mod_cast hrho

/-- Every zero of the entire regularization `riemannZeta₁` lies strictly left
of the line `Re(s)=1`. -/
lemma riemannZeta₁_zero_re_lt_one
    {rho : ℂ} (hzero : riemannZeta₁ rho = 0) :
    rho.re < 1 := by
  have hrho1 : rho ≠ 1 := by
    intro h
    subst rho
    rw [riemannZeta₁_one] at hzero
    exact one_ne_zero hzero
  have hzeta : riemannZeta rho = 0 := by
    rw [riemannZeta_eq_inv_sub_mul hrho1, hzero, mul_zero]
  by_contra hrho
  exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hrho)) hzeta

private lemma radiusTwoAnalyticOrder_finsum_re_nonneg
    (t : ℝ) (s : ℂ) (hs : 1 ≤ s.re) :
    0 ≤ (∑ᶠ rho : ℂ,
      ((if dist rho ((2 : ℂ) + t * I) ≤ 2 then
          analyticOrderNatAt riemannZeta₁ rho
        else 0 : ℕ) : ℂ) / (s - rho)).re := by
  let m : ℂ → ℕ := fun rho =>
    if dist rho ((2 : ℂ) + t * I) ≤ 2 then
      analyticOrderNatAt riemannZeta₁ rho
    else 0
  have hm : (Function.support m).Finite :=
    radiusTwoAnalyticOrder_hasFiniteSupport t
  have hsupport :
      Function.support (fun rho : ℂ => (m rho : ℂ) / (s - rho)) ⊆
        hm.toFinset := by
    intro rho hrho
    apply hm.mem_toFinset.mpr
    rw [Function.mem_support] at hrho ⊢
    exact fun hmrho => hrho (by simp [hmrho])
  rw [finsum_eq_sum_of_support_subset _ hsupport, Complex.re_sum]
  apply Finset.sum_nonneg
  intro rho _
  by_cases hmrho : m rho = 0
  · simp [hmrho]
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
    simpa [div_eq_mul_inv] using
      mul_nonneg (show (0 : ℝ) ≤ m rho by positivity) hinv

private lemma finsum_divisor_riemannZeta₁_radiusTwo_eq
    (t : ℝ) (s : ℂ) :
    (∑ᶠ rho : ℂ,
        ((MeromorphicOn.divisor riemannZeta₁
          (closedBall ((2 : ℂ) + t * I) 2)) rho : ℂ) / (s - rho)) =
      ∑ᶠ rho : ℂ,
        ((if dist rho ((2 : ℂ) + t * I) ≤ 2 then
            analyticOrderNatAt riemannZeta₁ rho
          else 0 : ℕ) : ℂ) / (s - rho) := by
  apply finsum_congr
  intro rho
  rw [divisor_riemannZeta₁_radiusTwo_apply t rho]
  norm_cast

/-- The SEM-482 fixed-disk estimate before its nonnegative zero sum is
discarded. -/
theorem exists_nat_norm_logDeriv_riemannZeta₁_sub_radiusTwo_finsum_le :
    ∃ A : ℕ, 1 ≤ A ∧
      ∀ (t : ℝ) (s : ℂ),
        s ∈ closedBall ((2 : ℂ) + t * I) 1 →
          riemannZeta₁ s ≠ 0 →
            ‖logDeriv riemannZeta₁ s -
                ∑ᶠ rho : ℂ,
                  ((if dist rho ((2 : ℂ) + t * I) ≤ 2 then
                      analyticOrderNatAt riemannZeta₁ rho
                    else 0 : ℕ) : ℂ) / (s - rho)‖ ≤
              16 * (A : ℝ) * Real.log (|t| + 2) := by
  obtain ⟨A, hA, hgrowth⟩ :=
    exists_nat_norm_riemannZeta₁_radiusFourSphere_le_exp_mul_center
  refine ⟨A, hA, ?_⟩
  intro t s hs hfs
  let c : ℂ := (2 : ℂ) + t * I
  let T : ℝ := |t| + 2
  let M : ℝ := (A : ℝ) * Real.log T
  have hT2 : (2 : ℝ) ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hM : 0 ≤ M :=
    mul_nonneg (Nat.cast_nonneg A) (Real.log_nonneg (by linarith))
  have hf : AnalyticOnNhd ℂ riemannZeta₁ (closedBall c (4 * (1 : ℝ))) :=
    analyticOnNhd_riemannZeta₁.mono
      (Set.subset_univ (closedBall c (4 * (1 : ℝ))))
  have hc1 : c ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [c] at this
  have hzeta : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [c])
  have hc : riemannZeta₁ c ≠ 0 := by
    intro hzero
    have hfactor := riemannZeta_eq_inv_sub_mul hc1
    rw [hzero, mul_zero] at hfactor
    exact hzeta hfactor
  have hbound : ∀ z ∈ sphere c (4 * (1 : ℝ)),
      ‖riemannZeta₁ z‖ ≤ Real.exp M * ‖riemannZeta₁ c‖ := by
    intro z hz
    norm_num at hz
    simpa [c, M, T] using
      hgrowth t z (by simpa [c] using hz)
  have hfixed := norm_logDeriv_sub_divisor_finsum_le
    (f := riemannZeta₁) (c := c) (s := s) (R := (1 : ℝ)) (M := M)
    (by norm_num) hM hf hc hbound (by simpa [c] using hs) hfs
  rw [show (2 : ℝ) * 1 = 2 by norm_num,
    finsum_divisor_riemannZeta₁_radiusTwo_eq t s] at hfixed
  simpa [M, T, mul_assoc] using hfixed

/-- The exact logarithmic-derivative relation between zeta and its entire
regularization on the closed right half-plane away from the pole. -/
lemma neg_logDeriv_riemannZeta_eq_pole_sub_regularized
    (s : ℂ) (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    -logDeriv riemannZeta s =
      (s - 1)⁻¹ - logDeriv riemannZeta₁ s := by
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hzeta1 : riemannZeta₁ s ≠ 0 := by
    intro hzero
    have hfactor := riemannZeta_eq_inv_sub_mul hs1
    rw [hzero, mul_zero] at hfactor
    exact hzeta hfactor
  rw [logDeriv_apply, logDeriv_apply,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs1,
    riemannZeta_eq_inv_sub_mul hs1]
  field_simp [hsub, hzeta1]
  ring

/-- The exact arbitrary-height coefficient-one zeta pole estimate. -/
theorem exists_nat_neg_logDeriv_riemannZeta_re_le_pole_add_log :
    ∃ A : ℕ, 1 ≤ A ∧
      ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → s ≠ 1 →
        (-logDeriv riemannZeta s).re ≤
          ((s - 1)⁻¹).re +
            16 * (A : ℝ) * Real.log (|s.im| + 2) := by
  obtain ⟨A, hA, hfixed⟩ :=
    exists_nat_norm_logDeriv_riemannZeta₁_sub_radiusTwo_finsum_le
  refine ⟨A, hA, ?_⟩
  intro s hs1 hs2 hsne
  let t : ℝ := s.im
  let S : ℂ := ∑ᶠ rho : ℂ,
    ((if dist rho ((2 : ℂ) + t * I) ≤ 2 then
        analyticOrderNatAt riemannZeta₁ rho
      else 0 : ℕ) : ℂ) / (s - rho)
  let E : ℝ := 16 * (A : ℝ) * Real.log (|t| + 2)
  have hsball : s ∈ closedBall ((2 : ℂ) + t * I) 1 := by
    rw [mem_closedBall, Complex.dist_eq]
    have hdiff : s - ((2 : ℂ) + t * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [t]
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hs1
  have hzeta1 : riemannZeta₁ s ≠ 0 := by
    intro hzero
    have hfactor := riemannZeta_eq_inv_sub_mul hsne
    rw [hzero, mul_zero] at hfactor
    exact hzeta hfactor
  have hnorm : ‖logDeriv riemannZeta₁ s - S‖ ≤ E := by
    simpa [S, E, t] using hfixed t s hsball hzeta1
  have hsum : 0 ≤ S.re := by
    simpa [S] using radiusTwoAnalyticOrder_finsum_re_nonneg t s hs1
  have hswap : ‖S - logDeriv riemannZeta₁ s‖ ≤ E := by
    rw [norm_sub_rev]
    exact hnorm
  have hreal :
      (S - logDeriv riemannZeta₁ s).re ≤
        ‖S - logDeriv riemannZeta₁ s‖ :=
    Complex.re_le_norm _
  have hregular : -(logDeriv riemannZeta₁ s).re ≤ E := by
    rw [Complex.sub_re] at hreal
    linarith
  have hpole := congrArg Complex.re
    (neg_logDeriv_riemannZeta_eq_pole_sub_regularized s hs1 hsne)
  simp only [Complex.sub_re] at hpole
  simpa [E, t] using (show
    (-logDeriv riemannZeta s).re ≤ ((s - 1)⁻¹).re + E by linarith)

end BoundedGaps.Maynard
