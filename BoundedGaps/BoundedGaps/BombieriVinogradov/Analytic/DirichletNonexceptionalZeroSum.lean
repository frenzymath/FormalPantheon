import BoundedGaps.BombieriVinogradov.Analytic.DirichletNonexceptionalZeroKernel
import BoundedGaps.BombieriVinogradov.Analytic.DirichletZeroReciprocalSum

/-!
# Summed nonexceptional Dirichlet zero kernels

This file combines the pointwise equation-(12.9) bound with the
multiplicity-weighted reciprocal-height estimate. The result is the squared-
log zero-sum bound used in `KoukoulopoulosDistributionPrimesPrelim2022`,
printed pp. 121--122, proof of Theorem 12.4.

The exceptional predicate retains the complete SEM-536 structure and the
modified kernel retains its denominator. Semantic review: `SEM-537`.
-/

namespace BoundedGaps.Maynard

open Complex
open scoped BigOperators

noncomputable section

/-- The complete exceptional alternative at the synchronized zero-free scale.
No existence is asserted. -/
def IsDirichletExceptionalLFunctionZeroAtScale
    (M : ℕ) {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (rho : ℂ) : Prop :=
  1 - 1 / ((M : ℝ) ^ 2 *
      Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re ∧
    regularizedDirichletLFunctionProduct q rho = 0 ∧
      analyticOrderNatAt
          (regularizedDirichletLFunctionProduct q) rho = 1 ∧
        (∀ zeta : ℂ,
          1 - 1 / ((M : ℝ) ^ 2 *
              Real.log ((q : ℝ) * (|zeta.im| + 2))) ≤ zeta.re →
            regularizedDirichletLFunctionProduct q zeta = 0 →
              zeta = rho) ∧
          ∃ psi : DirichletCharacter ℂ q,
            IsNonprincipalNontrivialLFunctionZero psi rho ∧
              chi = psi ∧ psi ^ 2 = 1 ∧ rho.im = 0 ∧
                analyticOrderNatAt
                    (DirichletCharacter.LFunction psi) rho = 1 ∧
                  ∀ eta : DirichletCharacter ℂ q,
                    IsDirichletNontrivialLFunctionZero eta rho →
                      eta = psi

/-- The exceptional members of one character's finite nontrivial-zero set. -/
noncomputable def dirichletExceptionalLFunctionZerosFinset
    (M : ℕ) {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (T : ℝ) : Finset ℂ := by
  classical
  exact (dirichletNontrivialLFunctionZerosFinset chi T).filter
    (IsDirichletExceptionalLFunctionZeroAtScale M chi)

/-- The complementary nonexceptional members of the finite zero set. -/
noncomputable def dirichletNonexceptionalLFunctionZerosFinset
    (M : ℕ) {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (T : ℝ) : Finset ℂ := by
  classical
  exact (dirichletNontrivialLFunctionZerosFinset chi T).filter
    fun rho => ¬ IsDirichletExceptionalLFunctionZeroAtScale M chi rho

@[simp]
theorem mem_dirichletExceptionalLFunctionZerosFinset_iff
    {M q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {T : ℝ} {rho : ℂ} :
    rho ∈ dirichletExceptionalLFunctionZerosFinset M chi T ↔
      IsDirichletNontrivialLFunctionZero chi rho ∧
        |rho.im| ≤ |T| ∧
          IsDirichletExceptionalLFunctionZeroAtScale M chi rho := by
  classical
  rw [dirichletExceptionalLFunctionZerosFinset, Finset.mem_filter,
    mem_dirichletNontrivialLFunctionZerosFinset_iff, and_assoc]

@[simp]
theorem mem_dirichletNonexceptionalLFunctionZerosFinset_iff
    {M q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {T : ℝ} {rho : ℂ} :
    rho ∈ dirichletNonexceptionalLFunctionZerosFinset M chi T ↔
      IsDirichletNontrivialLFunctionZero chi rho ∧
        |rho.im| ≤ |T| ∧
          ¬ IsDirichletExceptionalLFunctionZeroAtScale M chi rho := by
  classical
  rw [dirichletNonexceptionalLFunctionZerosFinset, Finset.mem_filter,
    mem_dirichletNontrivialLFunctionZerosFinset_iff, and_assoc]

/-- The grouped modified-kernel contribution of the exceptional filter. -/
noncomputable def dirichletExceptionalZeroKernelSum
    (M : ℕ) {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x T : ℝ) : ℂ :=
  ∑ rho ∈ dirichletExceptionalLFunctionZerosFinset M chi T,
    (analyticOrderNatAt
      (DirichletCharacter.LFunction chi) rho : ℂ) *
        dirichletExplicitFormulaKernel x rho

/-- The grouped modified-kernel contribution of the nonexceptional filter. -/
noncomputable def dirichletNonexceptionalZeroKernelSum
    (M : ℕ) {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x T : ℝ) : ℂ :=
  ∑ rho ∈ dirichletNonexceptionalLFunctionZerosFinset M chi T,
    (analyticOrderNatAt
      (DirichletCharacter.LFunction chi) rho : ℂ) *
        dirichletExplicitFormulaKernel x rho

/-- The two logical filters partition the complete grouped zero sum exactly.
-/
theorem dirichletNontrivialZeroKernelSum_eq_nonexceptional_add_exceptional
    (M : ℕ) {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x T : ℝ) :
    dirichletNontrivialZeroKernelSum chi x T =
      dirichletNonexceptionalZeroKernelSum M chi x T +
        dirichletExceptionalZeroKernelSum M chi x T := by
  classical
  rw [dirichletNontrivialZeroKernelSum,
    dirichletNonexceptionalZeroKernelSum,
    dirichletExceptionalZeroKernelSum,
    dirichletNonexceptionalLFunctionZerosFinset,
    dirichletExceptionalLFunctionZerosFinset]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (dirichletNontrivialLFunctionZerosFinset chi T)
    (IsDirichletExceptionalLFunctionZeroAtScale M chi)
    (fun rho =>
      (analyticOrderNatAt
        (DirichletCharacter.LFunction chi) rho : ℂ) *
          dirichletExplicitFormulaKernel x rho)
  simpa [add_comm] using hsplit.symm

/-- The complete exceptional predicate itself identifies every two filtered
points, so the exceptional finite set has cardinality at most one. -/
theorem card_dirichletExceptionalLFunctionZerosFinset_le_one
    (M : ℕ) {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (T : ℝ) :
    (dirichletExceptionalLFunctionZerosFinset M chi T).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro rho hrho zeta hzeta
  have hr :=
    (mem_dirichletExceptionalLFunctionZerosFinset_iff.mp hrho).2.2
  have hz :=
    (mem_dirichletExceptionalLFunctionZerosFinset_iff.mp hzeta).2.2
  exact (hr.2.2.2.1 zeta hz.1 hz.2.1).symm

/-- One synchronized zero-free witness and one local-count witness bound the
entire nonexceptional kernel sum and leave at most one exceptional location. -/
theorem
    exists_nat_card_dirichletExceptionalLFunctionZerosFinset_le_one_and_norm_dirichletNonexceptionalZeroKernelSum_le :
    ∃ M A : ℕ, 2 ≤ M ∧ 37 ≤ A ∧
      (∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (T : ℝ),
          (dirichletExceptionalLFunctionZerosFinset M chi T).card ≤ 1) ∧
        ∀ (q : ℕ) [NeZero q]
          (chi : DirichletCharacter ℂ q) (x T : ℝ),
            4 ≤ x → 2 ≤ T → T ≤ x →
              ‖dirichletNonexceptionalZeroKernelSum M chi x T‖ ≤
                96 * (A : ℝ) *
                  x ^ (1 - 1 / ((M : ℝ) ^ 2 *
                    Real.log ((q : ℝ) * (T + 2)))) *
                      Real.log ((q : ℝ) * (T + 2)) ^ 2 := by
  classical
  obtain ⟨M, hM, hpointwise⟩ :=
    exists_nat_norm_dirichletExplicitFormulaKernel_le_or_exceptional
  obtain ⟨A, hA, hreciprocal⟩ :=
    exists_nat_dirichletNontrivialZeroReciprocalMultiplicitySum_le
  refine ⟨M, A, hM, hA,
    fun q _ chi T =>
      card_dirichletExceptionalLFunctionZerosFinset_le_one M chi T, ?_⟩
  intro q _ chi x T hx hT hTx
  let alpha : ℝ := 1 - 1 / ((M : ℝ) ^ 2 *
    Real.log ((q : ℝ) * (T + 2)))
  let C : ℝ := 12 * x ^ alpha
  let w : ℂ → ℝ := fun rho =>
    (analyticOrderNatAt
      (DirichletCharacter.LFunction chi) rho : ℝ) /
        (1 + |rho.im|)
  have hT0 : 0 ≤ T := by linarith
  have hC0 : 0 ≤ C := by positivity
  have hsubset :
      dirichletNonexceptionalLFunctionZerosFinset M chi T ⊆
        dirichletNontrivialLFunctionZerosFinset chi T := by
    intro rho hrho
    rw [dirichletNonexceptionalLFunctionZerosFinset] at hrho
    exact (Finset.mem_filter.mp hrho).1
  have hsumSubset :
      (∑ rho ∈ dirichletNonexceptionalLFunctionZerosFinset M chi T,
          w rho) ≤
        ∑ rho ∈ dirichletNontrivialLFunctionZerosFinset chi T,
          w rho :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun rho _ _ => by simp [w]; positivity)
  have hterm : ∀ rho ∈
      dirichletNonexceptionalLFunctionZerosFinset M chi T,
      ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ ≤ C * w rho := by
    intro rho hrho
    obtain ⟨hzero, hheight, hnotExceptional⟩ :=
      mem_dirichletNonexceptionalLFunctionZerosFinset_iff.mp hrho
    have hheight' : |rho.im| ≤ T := by
      simpa [abs_of_nonneg hT0] using hheight
    have hsplit := hpointwise q chi rho hzero x T hx hT hTx hheight'
    have hkernel :
        ‖dirichletExplicitFormulaKernel x rho‖ ≤
          12 * x ^ alpha / (1 + |rho.im|) := by
      rcases hsplit with hbound | hexceptional
      · simpa only [alpha] using hbound
      · exact (hnotExceptional (by
          simpa only [IsDirichletExceptionalLFunctionZeroAtScale] using
            hexceptional)).elim
    rw [norm_mul, Complex.norm_natCast]
    calc
      (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℝ) *
            ‖dirichletExplicitFormulaKernel x rho‖ ≤
          (analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℝ) *
              (12 * x ^ alpha / (1 + |rho.im|)) :=
        mul_le_mul_of_nonneg_left hkernel (by positivity)
      _ = C * w rho := by
        dsimp [C, w]
        ring
  have hreciprocalBound := hreciprocal q chi T hT
  rw [dirichletNonexceptionalZeroKernelSum]
  calc
    ‖∑ rho ∈ dirichletNonexceptionalLFunctionZerosFinset M chi T,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ ≤
        ∑ rho ∈ dirichletNonexceptionalLFunctionZerosFinset M chi T,
          ‖(analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℂ) *
              dirichletExplicitFormulaKernel x rho‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ dirichletNonexceptionalLFunctionZerosFinset M chi T,
        C * w rho := Finset.sum_le_sum hterm
    _ = C *
        ∑ rho ∈ dirichletNonexceptionalLFunctionZerosFinset M chi T,
          w rho := by rw [Finset.mul_sum]
    _ ≤ C *
        ∑ rho ∈ dirichletNontrivialLFunctionZerosFinset chi T,
          w rho := mul_le_mul_of_nonneg_left hsumSubset hC0
    _ = C * dirichletNontrivialZeroReciprocalMultiplicitySum chi T := by
      rw [dirichletNontrivialZeroReciprocalMultiplicitySum]
    _ ≤ C * (8 * (A : ℝ) *
        Real.log ((q : ℝ) * (T + 2)) ^ 2) :=
      mul_le_mul_of_nonneg_left hreciprocalBound hC0
    _ = 96 * (A : ℝ) *
        x ^ (1 - 1 / ((M : ℝ) ^ 2 *
          Real.log ((q : ℝ) * (T + 2)))) *
            Real.log ((q : ℝ) * (T + 2)) ^ 2 := by
      dsimp [C, alpha]
      ring

end

end BoundedGaps.Maynard
