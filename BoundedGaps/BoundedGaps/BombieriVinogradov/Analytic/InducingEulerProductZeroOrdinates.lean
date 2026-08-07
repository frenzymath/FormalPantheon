import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProductLocalDivisorSupport
import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProductZeroGeometry

/-!
# Ordinates of inducing Euler-product zeros

Zeros of the finite inducing product in a closed unit ordinate window inject
into the radius-three divisor support counted in SEM-508. This gives both
finiteness and the same modulus-logarithmic bound for distinct ordinates.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110,
equation (11.2), and printed pp. 112--113. The exact count is project-derived.
Semantic review: `SEM-510`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

noncomputable section

/-- Ordinates of inducing-product zeros in the closed unit window about `t`. -/
noncomputable def inducingEulerProductZeroOrdinatesInUnitWindow
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) : Set ℝ :=
  {gamma |
    inducingEulerProduct chi ((gamma : ℂ) * I) = 0 ∧
      |gamma - t| ≤ 1}

private theorem mem_support_divisor_inducingEulerProduct_iff
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {U : Set ℂ} {s : ℂ} (hsU : s ∈ U) :
    s ∈ (MeromorphicOn.divisor (inducingEulerProduct chi) U).support ↔
      inducingEulerProduct chi s = 0 := by
  have hA : AnalyticOnNhd ℂ (inducingEulerProduct chi) U :=
    fun z _ => (differentiable_inducingEulerProduct chi).analyticAt z
  have htop : analyticOrderAt (inducingEulerProduct chi) s ≠ ⊤ := by
    rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
      (fun z => (differentiable_inducingEulerProduct chi).analyticAt z)]
    intro hzeroFunction
    have hzeroTwo : inducingEulerProduct chi (2 : ℂ) = 0 := by
      rw [hzeroFunction]
      rfl
    exact (inducingEulerProduct_ne_zero_of_re_pos chi (by norm_num)) hzeroTwo
  rw [Function.mem_support,
    MeromorphicOn.AnalyticOnNhd.divisor_apply hA hsU]
  lift analyticOrderAt (inducingEulerProduct chi) s to ℕ using htop
    with n hn
  simp only [ENat.map_coe, WithTop.untop₀_coe]
  constructor
  · intro hnInt
    have hnNat : n ≠ 0 := by exact_mod_cast hnInt
    have horder : analyticOrderAt (inducingEulerProduct chi) s ≠ 0 := by
      rw [← hn]
      exact_mod_cast hnNat
    exact ((differentiable_inducingEulerProduct chi).analyticAt s
      |>.analyticOrderAt_ne_zero).mp horder
  · intro hzero
    have horder : analyticOrderAt (inducingEulerProduct chi) s ≠ 0 :=
      ((differentiable_inducingEulerProduct chi).analyticAt s
        |>.analyticOrderAt_ne_zero).mpr hzero
    rw [← hn] at horder
    exact_mod_cast horder

private theorem inducingEulerProduct_ordinate_injective :
    Function.Injective (fun gamma : ℝ => (gamma : ℂ) * I) := by
  intro gamma delta h
  have him := congrArg Complex.im h
  simpa using him

private theorem inducingEulerProductZeroOrdinates_mapsTo_divisorSupport
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    Set.MapsTo (fun gamma : ℝ => (gamma : ℂ) * I)
      (inducingEulerProductZeroOrdinatesInUnitWindow chi t)
      (MeromorphicOn.divisor (inducingEulerProduct chi)
        (closedBall ((2 : ℂ) + t * I) 3)).support := by
  intro gamma hgamma
  rcases hgamma with ⟨hzero, hheight⟩
  have hmem : (gamma : ℂ) * I ∈ closedBall ((2 : ℂ) + t * I) 3 :=
    inducingEulerProduct_zero_mem_closedBall_radiusThree chi t hzero
      (by simpa using hheight)
  exact (mem_support_divisor_inducingEulerProduct_iff chi hmem).2 hzero

private theorem support_divisor_inducingEulerProduct_radiusThree_finite
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    (MeromorphicOn.divisor (inducingEulerProduct chi)
      (closedBall ((2 : ℂ) + t * I) 3)).support.Finite := by
  have hA : AnalyticOnNhd ℂ (inducingEulerProduct chi)
      (closedBall ((2 : ℂ) + t * I) 3) :=
    fun z _ => (differentiable_inducingEulerProduct chi).analyticAt z
  exact hA.meromorphicOn.divisor_support_finite_of_subset
    (isCompact_closedBall ((2 : ℂ) + t * I) 3) Set.Subset.rfl

/-- The local product-zero ordinate set is finite. -/
theorem inducingEulerProductZeroOrdinatesInUnitWindow_finite
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    (inducingEulerProductZeroOrdinatesInUnitWindow chi t).Finite :=
  Set.Finite.of_injOn
    (inducingEulerProductZeroOrdinates_mapsTo_divisorSupport chi t)
    inducingEulerProduct_ordinate_injective.injOn
    (support_divisor_inducingEulerProduct_radiusThree_finite chi t)

/-- The number of distinct local product-zero ordinates has the SEM-508
modulus-logarithmic bound. -/
theorem ncard_inducingEulerProductZeroOrdinatesInUnitWindow_le
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ((inducingEulerProductZeroOrdinatesInUnitWindow chi t).ncard : ℝ) ≤
      12 * Real.log (q : ℝ) := by
  have hnat :
      (inducingEulerProductZeroOrdinatesInUnitWindow chi t).ncard ≤
        (MeromorphicOn.divisor (inducingEulerProduct chi)
          (closedBall ((2 : ℂ) + t * I) 3)).support.ncard :=
    Set.ncard_le_ncard_of_injOn
      (fun gamma : ℝ => (gamma : ℂ) * I)
      (inducingEulerProductZeroOrdinates_mapsTo_divisorSupport chi t)
      inducingEulerProduct_ordinate_injective.injOn
      (support_divisor_inducingEulerProduct_radiusThree_finite chi t)
  have hreal :
      ((inducingEulerProductZeroOrdinatesInUnitWindow chi t).ncard : ℝ) ≤
        ((MeromorphicOn.divisor (inducingEulerProduct chi)
          (closedBall ((2 : ℂ) + t * I) 3)).support.ncard : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans
    (ncard_support_divisor_inducingEulerProduct_radiusThree_le chi t)

end

end BoundedGaps.Maynard
