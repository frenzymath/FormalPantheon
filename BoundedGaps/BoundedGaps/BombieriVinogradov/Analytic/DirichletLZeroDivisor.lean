import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The zero divisor of a nontrivial Dirichlet L-function

For a nontrivial Dirichlet character, Mathlib's continued `LFunction` is
entire and is nonzero at `s = 2`. Its divisor therefore records every ordinary
zero with its exact finite analytic multiplicity, and has finite support on a
closed disk.

This is intentionally the divisor of the ordinary L-function: it includes
trivial zeros and zeros introduced by imprimitive Euler factors. Identifying a
filtered part of it with completed primitive nontrivial zeros is a later
bridge.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 112--114,
zero conventions and Lemma 11.4(a)--(b). Convention checks:
`ElkiesM229PNTAP2018`, p. 1, and `ElkiesM229NearlyZeroFree2018`, pp. 2--3.
Semantic review: `SEM-470`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

private theorem analyticOnNhd_LFunction_of_nontrivial
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
  fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z

private theorem LFunction_ne_zero_function_of_nontrivial
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ ≠ 0 := by
  intro hzero
  have hz : DirichletCharacter.LFunction χ (2 : ℂ) = 0 := by
    rw [hzero]
    rfl
  exact (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by norm_num)) hz

private theorem analyticOrderAt_LFunction_ne_top
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
    (fun z => analyticOnNhd_LFunction_of_nontrivial hχ z (Set.mem_univ z))]
  exact LFunction_ne_zero_function_of_nontrivial hχ

/-- The divisor coefficient is the exact natural analytic multiplicity. -/
theorem divisor_LFunction_apply_eq_analyticOrderNatAt
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {U : Set ℂ} {s : ℂ} (hsU : s ∈ U) :
    MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U s =
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) s : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    ((analyticOnNhd_LFunction_of_nontrivial hχ).mono (Set.subset_univ U)) hsU]
  have hfinite := analyticOrderAt_LFunction_ne_top hχ s
  rw [← Nat.cast_analyticOrderNatAt hfinite, ENat.map_coe,
    WithTop.untop₀_coe]

/-- On a set containing `s`, divisor support is exactly ordinary vanishing. -/
theorem mem_support_divisor_LFunction_iff
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {U : Set ℂ} {s : ℂ} (hsU : s ∈ U) :
    s ∈ (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U).support ↔
      DirichletCharacter.LFunction χ s = 0 := by
  rw [Function.mem_support,
    MeromorphicOn.AnalyticOnNhd.divisor_apply
      ((analyticOnNhd_LFunction_of_nontrivial hχ).mono (Set.subset_univ U)) hsU]
  have htop := analyticOrderAt_LFunction_ne_top hχ s
  lift analyticOrderAt (DirichletCharacter.LFunction χ) s to ℕ using htop
    with n hn
  simp only [ENat.map_coe, WithTop.untop₀_coe]
  constructor
  · intro hnInt
    have hnNat : n ≠ 0 := by exact_mod_cast hnInt
    have horder : analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ 0 := by
      rw [← hn]
      exact_mod_cast hnNat
    exact ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s
      |>.analyticOrderAt_ne_zero).mp horder
  · intro hzero
    have horder : analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ 0 :=
      ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s
        |>.analyticOrderAt_ne_zero).mpr hzero
    rw [← hn] at horder
    exact_mod_cast horder

/-- The complete ordinary zero set is the support of the global divisor. -/
theorem LFunction_zero_set_eq_divisor_support
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    (DirichletCharacter.LFunction χ) ⁻¹' {0} =
      Function.support
        (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) Set.univ) := by
  ext s
  change DirichletCharacter.LFunction χ s = 0 ↔
    s ∈ (MeromorphicOn.divisor
      (DirichletCharacter.LFunction χ) Set.univ).support
  exact (mem_support_divisor_LFunction_iff hχ (Set.mem_univ s)).symm

/-- The divisor of an entire nontrivial L-function has no pole coefficients. -/
theorem divisor_LFunction_nonneg
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (U : Set ℂ) :
    0 ≤ MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    ((analyticOnNhd_LFunction_of_nontrivial hχ).mono (Set.subset_univ U))

/-- Only finitely many ordinary zeros lie in a closed disk. -/
theorem divisor_LFunction_closedBall_support_finite
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (c : ℂ) (R : ℝ) :
    (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (Metric.closedBall c R)).support.Finite :=
  ((analyticOnNhd_LFunction_of_nontrivial hχ).mono
    (Set.subset_univ (Metric.closedBall c R))).meromorphicOn
      |>.divisor_support_finite_of_subset (isCompact_closedBall c R)
        Set.Subset.rfl

/-- Every ordinary zero has positive integer divisor multiplicity. -/
theorem one_le_divisor_LFunction_of_zero
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {U : Set ℂ} {s : ℂ}
    (hsU : s ∈ U) (hsZero : DirichletCharacter.LFunction χ s = 0) :
    1 ≤ MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U s := by
  have hne : MeromorphicOn.divisor
      (DirichletCharacter.LFunction χ) U s ≠ 0 :=
    Function.mem_support.mp
      ((mem_support_divisor_LFunction_iff hχ hsU).2 hsZero)
  have hnonneg : 0 ≤ MeromorphicOn.divisor
      (DirichletCharacter.LFunction χ) U s :=
    (divisor_LFunction_nonneg hχ U) s
  omega

end BoundedGaps.Maynard
