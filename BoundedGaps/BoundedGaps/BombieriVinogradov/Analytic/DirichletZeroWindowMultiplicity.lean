import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaZeroShell
import BoundedGaps.BombieriVinogradov.Analytic.DirichletLocalDivisorMass
import BoundedGaps.BombieriVinogradov.Analytic.FiniteDivisorSubmassBound
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaFixedDisk
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusSixDivisorMass
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaZeroShell

/-!
# Unit-height Dirichlet zero multiplicity

This file exports the closed unit-ordinate-window form of the local zero count
in `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 114, Lemma
11.4(a). The level-one branch uses the analogous zeta count from printed
p. 84, Lemma 8.2(a).

Zeros are grouped by location and weighted by exact analytic multiplicity.
Semantic review: `SEM-537`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set
open scoped BigOperators

noncomputable section

/-- The distinct nontrivial zero locations in the closed ordinate window
`|Im(rho)-t|<=1`. -/
noncomputable def dirichletNontrivialLFunctionZeroWindowFinset
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (t : ℝ) : Finset ℂ :=
  (dirichletNontrivialLFunctionZerosFinset chi (|t| + 1)).filter
    fun rho => |rho.im - t| ≤ 1

@[simp]
theorem mem_dirichletNontrivialLFunctionZeroWindowFinset_iff
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {t : ℝ} {rho : ℂ} :
    rho ∈ dirichletNontrivialLFunctionZeroWindowFinset chi t ↔
      IsDirichletNontrivialLFunctionZero chi rho ∧
        |rho.im - t| ≤ 1 := by
  classical
  rw [dirichletNontrivialLFunctionZeroWindowFinset, Finset.mem_filter,
    mem_dirichletNontrivialLFunctionZerosFinset_iff]
  have hcutoff : 0 ≤ |t| + 1 := by linarith [abs_nonneg t]
  rw [abs_of_nonneg hcutoff]
  constructor
  · rintro ⟨⟨hzero, _⟩, hwindow⟩
    exact ⟨hzero, hwindow⟩
  · rintro ⟨hzero, hwindow⟩
    refine ⟨⟨hzero, ?_⟩, hwindow⟩
    calc
      |rho.im| = |(rho.im - t) + t| := by ring_nf
      _ ≤ |rho.im - t| + |t| := abs_add_le _ _
      _ ≤ 1 + |t| := by
        simpa [add_comm] using add_le_add_right hwindow |t|
      _ = |t| + 1 := add_comm _ _

private theorem sum_natCast_le_finsum_intCast
    {α : Type*} (S : Finset α) (m : α → ℕ) (D : α → ℤ)
    (hDfinite : D.support.Finite) (hDnonneg : 0 ≤ D)
    (hm : ∀ a ∈ S, (m a : ℤ) ≤ D a) :
    (∑ a ∈ S, (m a : ℝ)) ≤ ((∑ᶠ a, D a : ℤ) : ℝ) := by
  have hzeroFinite : (0 : α → ℤ).support.Finite := by simp
  have hzeroNonneg : (0 : α → ℤ) ≤ 0 := le_rfl
  have hpair := sum_natCast_le_finsum_intCast_pair
    S m D 0 hDfinite hzeroFinite hDnonneg hzeroNonneg
    (fun a ha => by simpa using hm a ha)
  simpa using hpair

/-- One absolute witness bounds the complete analytic multiplicity in every
closed unit-height window for every primitive character, including level one.
-/
theorem
    exists_nat_sum_dirichletNontrivialZeroWindowMultiplicity_of_isPrimitive_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ t : ℝ,
            (∑ rho ∈ dirichletNontrivialLFunctionZeroWindowFinset chi t,
              (analyticOrderNatAt
                (DirichletCharacter.LFunction chi) rho : ℝ)) ≤
              2 * (A : ℝ) *
                Real.log ((q : ℝ) * (|t| + 2)) := by
  obtain ⟨Ap, hAp, hp⟩ :=
    exists_nat_finsum_divisor_LFunction_radiusSix_le
  obtain ⟨Az, hAz, hz⟩ :=
    exists_nat_finsum_divisor_riemannZeta₁_radiusSix_le
  let A := max Ap Az
  refine ⟨A, hAp.trans (Nat.le_max_left Ap Az), ?_⟩
  intro q _ chi hchi t
  by_cases hqOne : q = 1
  · subst q
    have hchiOne : chi = 1 := Subsingleton.elim _ _
    subst chi
    let D : ℂ → ℤ :=
      MeromorphicOn.divisor riemannZeta₁
        (closedBall ((2 : ℂ) + t * I) 6)
    have hDfinite : D.support.Finite := by
      simpa [D] using divisor_riemannZeta₁_closedBall_support_finite
        ((2 : ℂ) + t * I) 6
    have hDnonneg : 0 ≤ D := by
      intro rho
      exact (divisor_riemannZeta₁_nonneg
        (closedBall ((2 : ℂ) + t * I) 6)) rho
    have hcoeff : ∀ rho ∈
        dirichletNontrivialLFunctionZeroWindowFinset
          (1 : DirichletCharacter ℂ 1) t,
        (analyticOrderNatAt
            (DirichletCharacter.LFunction
              (1 : DirichletCharacter ℂ 1)) rho : ℤ) ≤ D rho := by
      intro rho hrho
      obtain ⟨hzero, hheight⟩ :=
        mem_dirichletNontrivialLFunctionZeroWindowFinset_iff.mp hrho
      have hrhoOne : rho ≠ 1 := by
        intro hrho
        have hre := congrArg Complex.re hrho
        norm_num at hre
        linarith [hzero.2.2]
      have hdisk := hzero.dist_two_add_mul_I_le_six hheight
      have horder :=
        analyticOrderNatAt_LFunction_modOne_eq_riemannZeta₁_of_ne_one
          hrhoOne
      have hD : D rho = (analyticOrderNatAt riemannZeta₁ rho : ℤ) := by
        dsimp [D]
        exact divisor_riemannZeta₁_apply_eq_analyticOrderNatAt
          (mem_closedBall.mpr hdisk)
      rw [horder, hD]
    have hsubmass := sum_natCast_le_finsum_intCast
      (dirichletNontrivialLFunctionZeroWindowFinset
        (1 : DirichletCharacter ℂ 1) t)
      (fun rho => analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho)
      D hDfinite hDnonneg hcoeff
    have hAzA : (Az : ℝ) ≤ A := by
      exact_mod_cast Nat.le_max_right Ap Az
    have hlogNonneg : 0 ≤ Real.log (|t| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    calc
      (∑ rho ∈ dirichletNontrivialLFunctionZeroWindowFinset
          (1 : DirichletCharacter ℂ 1) t,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℝ)) ≤
          ((∑ᶠ rho, D rho : ℤ) : ℝ) := hsubmass
      _ ≤ 2 * (Az : ℝ) * Real.log (|t| + 2) := by
        simpa [D] using hz t
      _ ≤ 2 * (A : ℝ) * Real.log (|t| + 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAzA (by norm_num)) hlogNonneg
      _ = 2 * (A : ℝ) *
          Real.log (((1 : ℕ) : ℝ) * (|t| + 2)) := by simp
  · have hq : 1 < q := by
      have hqpos := NeZero.pos q
      omega
    have hchiNe : chi ≠ 1 :=
      character_ne_one_of_isPrimitive hq chi hchi
    let D : ℂ → ℤ :=
      MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
        (closedBall ((2 : ℂ) + t * I) 6)
    have hDfinite : D.support.Finite := by
      simpa [D] using divisor_LFunction_closedBall_support_finite
        hchiNe ((2 : ℂ) + t * I) 6
    have hDnonneg : 0 ≤ D := by
      intro rho
      exact (divisor_LFunction_nonneg hchiNe
        (closedBall ((2 : ℂ) + t * I) 6)) rho
    have hcoeff : ∀ rho ∈
        dirichletNontrivialLFunctionZeroWindowFinset chi t,
        (analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℤ) ≤ D rho := by
      intro rho hrho
      obtain ⟨hzero, hheight⟩ :=
        mem_dirichletNontrivialLFunctionZeroWindowFinset_iff.mp hrho
      have hdisk := hzero.dist_two_add_mul_I_le_six hheight
      have hD : D rho =
          (analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℤ) := by
        dsimp [D]
        exact divisor_LFunction_apply_eq_analyticOrderNatAt
          hchiNe (mem_closedBall.mpr hdisk)
      rw [hD]
    have hsubmass := sum_natCast_le_finsum_intCast
      (dirichletNontrivialLFunctionZeroWindowFinset chi t)
      (fun rho => analyticOrderNatAt
        (DirichletCharacter.LFunction chi) rho)
      D hDfinite hDnonneg hcoeff
    have hApA : (Ap : ℝ) ≤ A := by
      exact_mod_cast Nat.le_max_left Ap Az
    have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have hscale : (1 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
      nlinarith [mul_le_mul hqReal
        (show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
        (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ q)]
    have hlogNonneg :
        0 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
      Real.log_nonneg hscale
    calc
      (∑ rho ∈ dirichletNontrivialLFunctionZeroWindowFinset chi t,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℝ)) ≤
          ((∑ᶠ rho, D rho : ℤ) : ℝ) := hsubmass
      _ ≤ 2 * (Ap : ℝ) *
          Real.log ((q : ℝ) * (|t| + 2)) := by
        simpa [D] using hp q hq chi hchi t
      _ ≤ 2 * (A : ℝ) *
          Real.log ((q : ℝ) * (|t| + 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hApA (by norm_num)) hlogNonneg

end

end BoundedGaps.Maynard
