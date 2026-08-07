import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaZeroShell
import BoundedGaps.BombieriVinogradov.Analytic.FiniteDivisorSubmassBound
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaFixedDisk
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusSixDivisorMass

/-!
# Modulus-one Dirichlet zero-shell mass

The primitive conductor-one branch of the Dirichlet explicit formula is the
Riemann zeta function. Away from its pole, the entire regularization
`riemannZeta₁` has the same analytic zero order. Its two signed radius-six
divisors therefore control the selected-height zero shell with multiplicity.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 85--86 and
114--115, Lemma 8.2(a) and Theorems 5.1 and 11.3. Semantic review: `SEM-531`.
-/

namespace BoundedGaps.Maynard

open Complex Filter Metric Set
open scoped BigOperators Topology

noncomputable section

/-- Away from the zeta pole, the modulus-one L-function and the entire
regularization `riemannZeta₁` have the same natural analytic order. -/
theorem analyticOrderNatAt_LFunction_modOne_eq_riemannZeta₁_of_ne_one
    {rho : ℂ} (hrho : rho ≠ 1) :
    analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho =
      analyticOrderNatAt riemannZeta₁ rho := by
  rw [DirichletCharacter.LFunction_modOne_eq]
  have heq : riemannZeta₁ =ᶠ[𝓝 rho]
      fun s => (s - 1) * riemannZeta s := by
    filter_upwards [eventually_ne_nhds hrho] with s hs
    rw [riemannZeta_eq_inv_sub_mul hs]
    field_simp [sub_ne_zero.mpr hs]
  have hlinear : AnalyticAt ℂ (fun s : ℂ => s - 1) rho := by fun_prop
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho (by simpa using hrho)
  have horder :
      analyticOrderAt riemannZeta₁ rho =
        analyticOrderAt riemannZeta rho := by
    calc
      analyticOrderAt riemannZeta₁ rho =
          analyticOrderAt (fun s => (s - 1) * riemannZeta s) rho :=
        analyticOrderAt_congr heq
      _ = analyticOrderAt (fun s : ℂ => s - 1) rho +
          analyticOrderAt riemannZeta rho :=
        analyticOrderAt_mul hlinear hzeta
      _ = 0 + analyticOrderAt riemannZeta rho := by
        rw [hlinear.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hrho)]
      _ = analyticOrderAt riemannZeta rho := zero_add _
  exact congrArg ENat.toNat horder.symm

/-- The complete multiplicity in the modulus-one selected-height zero shell
is controlled by two regularized-zeta divisor masses. -/
theorem
    exists_nat_sum_dirichletNontrivialZeroShellMultiplicity_modOne_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (T U : ℝ), 2 ≤ T → U ∈ Set.Icc T (T + 1) →
        (∑ rho ∈ dirichletNontrivialLFunctionZeroShellFinset
            (1 : DirichletCharacter ℂ 1) T U,
          (analyticOrderNatAt
            (DirichletCharacter.LFunction
              (1 : DirichletCharacter ℂ 1)) rho : ℝ)) ≤
          4 * (A : ℝ) * Real.log (T + 2) := by
  obtain ⟨A, hA, hmass⟩ :=
    exists_nat_finsum_divisor_riemannZeta₁_radiusSix_le
  refine ⟨A, hA, ?_⟩
  intro T U hT hU
  let Dplus : ℂ → ℤ :=
    MeromorphicOn.divisor riemannZeta₁
      (closedBall ((2 : ℂ) + T * I) 6)
  let Dminus : ℂ → ℤ :=
    MeromorphicOn.divisor riemannZeta₁
      (closedBall ((2 : ℂ) + ((-T : ℝ) : ℂ) * I) 6)
  have hDplusFinite : Dplus.support.Finite := by
    simpa [Dplus] using divisor_riemannZeta₁_closedBall_support_finite
      ((2 : ℂ) + T * I) 6
  have hDminusFinite : Dminus.support.Finite := by
    simpa [Dminus] using divisor_riemannZeta₁_closedBall_support_finite
      ((2 : ℂ) + ((-T : ℝ) : ℂ) * I) 6
  have hDplusNonneg : 0 ≤ Dplus := by
    intro rho
    exact (divisor_riemannZeta₁_nonneg
      (closedBall ((2 : ℂ) + T * I) 6)) rho
  have hDminusNonneg : 0 ≤ Dminus := by
    intro rho
    exact (divisor_riemannZeta₁_nonneg
      (closedBall ((2 : ℂ) + ((-T : ℝ) : ℂ) * I) 6)) rho
  have hcoeff : ∀ rho ∈ dirichletNontrivialLFunctionZeroShellFinset
      (1 : DirichletCharacter ℂ 1) T U,
      (analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℤ) ≤
        Dplus rho + Dminus rho := by
    intro rho hrho
    obtain ⟨hzero, hlower, hupper⟩ :=
      (mem_dirichletNontrivialLFunctionZeroShellFinset_iff
        (show 0 ≤ T by linarith) hU.1).mp hrho
    have hrhoOne : rho ≠ 1 := by
      intro hrho
      have hre := congrArg Complex.re hrho
      norm_num at hre
      linarith [hzero.2.2]
    have horder :=
      analyticOrderNatAt_LFunction_modOne_eq_riemannZeta₁_of_ne_one hrhoOne
    by_cases him : 0 ≤ rho.im
    · rw [abs_of_nonneg him] at hlower hupper
      have hheight : |rho.im - T| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hU.2]
      have hdisk := hzero.dist_two_add_mul_I_le_six hheight
      have hDplus : Dplus rho =
          (analyticOrderNatAt riemannZeta₁ rho : ℤ) := by
        dsimp [Dplus]
        exact divisor_riemannZeta₁_apply_eq_analyticOrderNatAt
          (mem_closedBall.mpr hdisk)
      rw [horder, hDplus]
      exact le_add_of_nonneg_right (hDminusNonneg rho)
    · have himNonpos : rho.im ≤ 0 := le_of_not_ge him
      rw [abs_of_nonpos himNonpos] at hlower hupper
      have hheight : |rho.im - (-T)| ≤ 1 := by
        rw [sub_neg_eq_add, abs_le]
        constructor <;> linarith [hU.2]
      have hdisk := hzero.dist_two_add_mul_I_le_six hheight
      have hDminus : Dminus rho =
          (analyticOrderNatAt riemannZeta₁ rho : ℤ) := by
        dsimp [Dminus]
        exact divisor_riemannZeta₁_apply_eq_analyticOrderNatAt
          (mem_closedBall.mpr hdisk)
      rw [horder, hDminus]
      exact le_add_of_nonneg_left (hDplusNonneg rho)
  have hsubmass := sum_natCast_le_finsum_intCast_pair
    (dirichletNontrivialLFunctionZeroShellFinset
      (1 : DirichletCharacter ℂ 1) T U)
    (fun rho => analyticOrderNatAt
      (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1)) rho)
    Dplus Dminus hDplusFinite hDminusFinite
    hDplusNonneg hDminusNonneg hcoeff
  have hplus : ((∑ᶠ rho, Dplus rho : ℤ) : ℝ) ≤
      2 * (A : ℝ) * Real.log (T + 2) := by
    simpa [Dplus, abs_of_nonneg (show 0 ≤ T by linarith)] using hmass T
  have hminus : ((∑ᶠ rho, Dminus rho : ℤ) : ℝ) ≤
      2 * (A : ℝ) * Real.log (T + 2) := by
    simpa [Dminus, abs_of_nonneg (show 0 ≤ T by linarith)] using hmass (-T)
  calc
    (∑ rho ∈ dirichletNontrivialLFunctionZeroShellFinset
        (1 : DirichletCharacter ℂ 1) T U,
      (analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℝ)) ≤
        ((∑ᶠ rho, Dplus rho : ℤ) : ℝ) +
          ((∑ᶠ rho, Dminus rho : ℤ) : ℝ) := hsubmass
    _ ≤ 2 * (A : ℝ) * Real.log (T + 2) +
        2 * (A : ℝ) * Real.log (T + 2) := add_le_add hplus hminus
    _ = 4 * (A : ℝ) * Real.log (T + 2) := by ring

end

end BoundedGaps.Maynard
