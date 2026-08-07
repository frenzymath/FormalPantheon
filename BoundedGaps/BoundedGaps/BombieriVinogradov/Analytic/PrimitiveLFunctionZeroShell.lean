import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaZeroShell
import BoundedGaps.BombieriVinogradov.Analytic.DirichletLocalDivisorMass
import BoundedGaps.BombieriVinogradov.Analytic.FiniteDivisorSubmassBound
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionFixedDisk

/-!
# Primitive Dirichlet zero-shell mass

For a primitive nonprincipal character, the positive and negative halves of
the selected-height zero shell lie in the complete ordinary radius-six
divisors centered at `2+i*T` and `2-i*T`. Their combined multiplicity is
therefore logarithmically bounded without invoking zero conjugation.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115,
Lemma 11.4(a) and Theorem 11.3. Semantic review: `SEM-531`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set
open scoped BigOperators

noncomputable section

/-- The complete multiplicity in a primitive nonprincipal selected-height
zero shell is controlled by the two signed local divisor masses. -/
theorem
    exists_nat_sum_dirichletNontrivialZeroShellMultiplicity_primitive_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (T U : ℝ), 2 ≤ T → U ∈ Set.Icc T (T + 1) →
            (∑ rho ∈
                dirichletNontrivialLFunctionZeroShellFinset chi T U,
              (analyticOrderNatAt
                (DirichletCharacter.LFunction chi) rho : ℝ)) ≤
              4 * (A : ℝ) * Real.log ((q : ℝ) * (T + 2)) := by
  obtain ⟨A, hA, hmass⟩ :=
    exists_nat_finsum_divisor_LFunction_radiusSix_le
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi T U hT hU
  let Dplus : ℂ → ℤ :=
    MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
      (closedBall ((2 : ℂ) + T * I) 6)
  let Dminus : ℂ → ℤ :=
    MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
      (closedBall ((2 : ℂ) + ((-T : ℝ) : ℂ) * I) 6)
  have hchiNe : chi ≠ 1 := character_ne_one_of_isPrimitive hq chi hchi
  have hDplusFinite : Dplus.support.Finite := by
    simpa [Dplus] using divisor_LFunction_closedBall_support_finite
      hchiNe ((2 : ℂ) + T * I) 6
  have hDminusFinite : Dminus.support.Finite := by
    simpa [Dminus] using divisor_LFunction_closedBall_support_finite
      hchiNe ((2 : ℂ) + ((-T : ℝ) : ℂ) * I) 6
  have hDplusNonneg : 0 ≤ Dplus := by
    intro rho
    exact (divisor_LFunction_nonneg hchiNe
      (closedBall ((2 : ℂ) + T * I) 6)) rho
  have hDminusNonneg : 0 ≤ Dminus := by
    intro rho
    exact (divisor_LFunction_nonneg hchiNe
      (closedBall ((2 : ℂ) + ((-T : ℝ) : ℂ) * I) 6)) rho
  have hcoeff : ∀ rho ∈
      dirichletNontrivialLFunctionZeroShellFinset chi T U,
      (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℤ) ≤
        Dplus rho + Dminus rho := by
    intro rho hrho
    obtain ⟨hzero, hlower, hupper⟩ :=
      (mem_dirichletNontrivialLFunctionZeroShellFinset_iff
        (show 0 ≤ T by linarith) hU.1).mp hrho
    by_cases him : 0 ≤ rho.im
    · rw [abs_of_nonneg him] at hlower hupper
      have hheight : |rho.im - T| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hU.2]
      have hdisk := hzero.dist_two_add_mul_I_le_six hheight
      have hDplus : Dplus rho =
          (analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℤ) := by
        have happly := divisor_LFunction_radiusSix_apply hq chi hchi T rho
        rw [if_pos hdisk] at happly
        simpa [Dplus] using happly
      rw [hDplus]
      exact le_add_of_nonneg_right (hDminusNonneg rho)
    · have himNonpos : rho.im ≤ 0 := le_of_not_ge him
      rw [abs_of_nonpos himNonpos] at hlower hupper
      have hheight : |rho.im - (-T)| ≤ 1 := by
        rw [sub_neg_eq_add, abs_le]
        constructor <;> linarith [hU.2]
      have hdisk := hzero.dist_two_add_mul_I_le_six hheight
      have hDminus : Dminus rho =
          (analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℤ) := by
        have happly := divisor_LFunction_radiusSix_apply hq chi hchi (-T) rho
        rw [if_pos hdisk] at happly
        simpa [Dminus] using happly
      rw [hDminus]
      exact le_add_of_nonneg_left (hDplusNonneg rho)
  have hsubmass := sum_natCast_le_finsum_intCast_pair
    (dirichletNontrivialLFunctionZeroShellFinset chi T U)
    (fun rho => analyticOrderNatAt
      (DirichletCharacter.LFunction chi) rho)
    Dplus Dminus hDplusFinite hDminusFinite
    hDplusNonneg hDminusNonneg hcoeff
  have hplus : ((∑ᶠ rho, Dplus rho : ℤ) : ℝ) ≤
      2 * (A : ℝ) * Real.log ((q : ℝ) * (T + 2)) := by
    simpa [Dplus, abs_of_nonneg (show 0 ≤ T by linarith)] using
      hmass q hq chi hchi T
  have hminus : ((∑ᶠ rho, Dminus rho : ℤ) : ℝ) ≤
      2 * (A : ℝ) * Real.log ((q : ℝ) * (T + 2)) := by
    simpa [Dminus, abs_of_nonneg (show 0 ≤ T by linarith)] using
      hmass q hq chi hchi (-T)
  calc
    (∑ rho ∈ dirichletNontrivialLFunctionZeroShellFinset chi T U,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℝ)) ≤
        ((∑ᶠ rho, Dplus rho : ℤ) : ℝ) +
          ((∑ᶠ rho, Dminus rho : ℤ) : ℝ) := hsubmass
    _ ≤ 2 * (A : ℝ) * Real.log ((q : ℝ) * (T + 2)) +
        2 * (A : ℝ) * Real.log ((q : ℝ) * (T + 2)) :=
      add_le_add hplus hminus
    _ = 4 * (A : ℝ) * Real.log ((q : ℝ) * (T + 2)) := by ring

end

end BoundedGaps.Maynard
