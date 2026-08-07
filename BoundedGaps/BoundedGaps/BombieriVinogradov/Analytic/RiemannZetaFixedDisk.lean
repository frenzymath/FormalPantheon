import BoundedGaps.BombieriVinogradov.Analytic.FixedDiskLogDerivative
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusTwelve

/-!
# Regularized zeta on the radius-three fixed disk

The entire function `riemannZeta₁` has a nonnegative analytic divisor. This
file records its reusable divisor API and applies the generic fixed-disk
theorem at radii `3`, `6`, and `12`. It also extends the exact zeta pole
identity from the right half-plane to every point away from the pole and
ordinary zeros.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 84 and
89--92, Lemmas 8.2 and 8.6. Semantic review: `SEM-529`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

noncomputable section

private lemma analyticOnNhd_riemannZeta₁_fixedDisk :
    AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
  fun z _ => differentiable_riemannZeta₁.analyticAt z

private lemma analyticOrderAt_riemannZeta₁_ne_top_fixedDisk (s : ℂ) :
    analyticOrderAt riemannZeta₁ s ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
    (fun z => analyticOnNhd_riemannZeta₁_fixedDisk z (mem_univ z))]
  intro hzero
  have hone := congrFun hzero 1
  rw [riemannZeta₁_one] at hone
  exact one_ne_zero hone

/-- On a set containing the point, the regularized-zeta divisor coefficient
is its exact natural analytic multiplicity. -/
theorem divisor_riemannZeta₁_apply_eq_analyticOrderNatAt
    {U : Set ℂ} {s : ℂ} (hsU : s ∈ U) :
    MeromorphicOn.divisor riemannZeta₁ U s =
      (analyticOrderNatAt riemannZeta₁ s : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    (analyticOnNhd_riemannZeta₁_fixedDisk.mono (Set.subset_univ U)) hsU]
  have hfinite := analyticOrderAt_riemannZeta₁_ne_top_fixedDisk s
  rw [← Nat.cast_analyticOrderNatAt hfinite, ENat.map_coe,
    WithTop.untop₀_coe]

/-- Regularized-zeta divisor support is exactly regularized-zeta vanishing. -/
theorem mem_support_divisor_riemannZeta₁_iff
    {U : Set ℂ} {s : ℂ} (hsU : s ∈ U) :
    s ∈ (MeromorphicOn.divisor riemannZeta₁ U).support ↔
      riemannZeta₁ s = 0 := by
  rw [Function.mem_support,
    MeromorphicOn.AnalyticOnNhd.divisor_apply
      (analyticOnNhd_riemannZeta₁_fixedDisk.mono (Set.subset_univ U)) hsU]
  have htop := analyticOrderAt_riemannZeta₁_ne_top_fixedDisk s
  lift analyticOrderAt riemannZeta₁ s to ℕ using htop with n hn
  simp only [ENat.map_coe, WithTop.untop₀_coe]
  constructor
  · intro hnInt
    have hnNat : n ≠ 0 := by exact_mod_cast hnInt
    have horder : analyticOrderAt riemannZeta₁ s ≠ 0 := by
      rw [← hn]
      exact_mod_cast hnNat
    exact (differentiable_riemannZeta₁.analyticAt s
      |>.analyticOrderAt_ne_zero).mp horder
  · intro hzero
    have horder : analyticOrderAt riemannZeta₁ s ≠ 0 :=
      (differentiable_riemannZeta₁.analyticAt s
        |>.analyticOrderAt_ne_zero).mpr hzero
    rw [← hn] at horder
    exact_mod_cast horder

/-- The divisor of the entire regularization has no negative coefficients. -/
theorem divisor_riemannZeta₁_nonneg (U : Set ℂ) :
    0 ≤ MeromorphicOn.divisor riemannZeta₁ U :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    (analyticOnNhd_riemannZeta₁_fixedDisk.mono (Set.subset_univ U))

/-- Only finitely many regularized-zeta zeros lie in a closed disk. -/
theorem divisor_riemannZeta₁_closedBall_support_finite (c : ℂ) (R : ℝ) :
    (MeromorphicOn.divisor riemannZeta₁
      (closedBall c R)).support.Finite :=
  (analyticOnNhd_riemannZeta₁_fixedDisk.mono
      (Set.subset_univ (closedBall c R))).meromorphicOn
    |>.divisor_support_finite_of_subset (isCompact_closedBall c R)
      Set.Subset.rfl

/-- The exact pole/regularization identity at every non-pole nonzero point. -/
lemma neg_logDeriv_riemannZeta_eq_pole_sub_regularized_of_ne_zero
    (s : ℂ) (hsOne : s ≠ 1) (hsZero : riemannZeta s ≠ 0) :
    -logDeriv riemannZeta s =
      (s - 1)⁻¹ - logDeriv riemannZeta₁ s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hsOne
  have hzetaOne : riemannZeta₁ s ≠ 0 := by
    intro hzero
    have hfactor := riemannZeta_eq_inv_sub_mul hsOne
    rw [hzero, mul_zero] at hfactor
    exact hsZero hfactor
  rw [logDeriv_apply, logDeriv_apply,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hsOne,
    riemannZeta_eq_inv_sub_mul hsOne]
  field_simp [hsub, hzetaOne]
  ring

/-- The regularized-zeta specialization of the fixed-disk theorem, retaining
the exact divisor of the closed radius-six disk. -/
theorem
    exists_nat_norm_logDeriv_riemannZeta₁_sub_radiusSix_divisor_finsum_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (t : ℝ) (s : ℂ),
        s ∈ closedBall ((2 : ℂ) + t * I) 3 →
          riemannZeta₁ s ≠ 0 →
            ‖logDeriv riemannZeta₁ s -
                ∑ᶠ rho : ℂ,
                  ((MeromorphicOn.divisor riemannZeta₁
                    (closedBall ((2 : ℂ) + t * I) 6)) rho : ℂ) /
                      (s - rho)‖ ≤
              16 * ((A : ℝ) * Real.log (|t| + 2)) / 3 := by
  obtain ⟨A, hA, hgrowth⟩ :=
    exists_nat_norm_riemannZeta₁_radiusTwelveSphere_le_exp_mul_center
  refine ⟨A, hA, ?_⟩
  intro t s hs hfs
  let c : ℂ := (2 : ℂ) + t * I
  let T : ℝ := |t| + 2
  let M : ℝ := (A : ℝ) * Real.log T
  have hT2 : (2 : ℝ) ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hM : 0 ≤ M :=
    mul_nonneg (Nat.cast_nonneg A) (Real.log_nonneg (by linarith))
  have hf : AnalyticOnNhd ℂ riemannZeta₁ (closedBall c (4 * (3 : ℝ))) :=
    analyticOnNhd_riemannZeta₁_fixedDisk.mono
      (Set.subset_univ (closedBall c (4 * (3 : ℝ))))
  have hcOne : c ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [c] at hre
  have hzeta : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [c])
  have hc : riemannZeta₁ c ≠ 0 := by
    intro hzero
    have hfactor := riemannZeta_eq_inv_sub_mul hcOne
    rw [hzero, mul_zero] at hfactor
    exact hzeta hfactor
  have hbound : ∀ z ∈ sphere c (4 * (3 : ℝ)),
      ‖riemannZeta₁ z‖ ≤ Real.exp M * ‖riemannZeta₁ c‖ := by
    intro z hz
    norm_num at hz
    simpa [c, M, T] using hgrowth t z (by simpa [c] using hz)
  have hfixed := norm_logDeriv_sub_divisor_finsum_le
    (f := riemannZeta₁) (c := c) (s := s) (R := (3 : ℝ)) (M := M)
    (by norm_num) hM hf hc hbound (by simpa [c] using hs) hfs
  rw [show (2 : ℝ) * 3 = 6 by norm_num] at hfixed
  simpa [M, T, mul_assoc] using hfixed

end

end BoundedGaps.Maynard
