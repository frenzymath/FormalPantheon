import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaCandidateCircleContribution

/-!
# Dirichlet explicit-formula candidate circle sum

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115, sums the
ordinary-zero and principal-pole contributions crossed by the modified
explicit-formula contour. This file converts SEM-502's finite candidate set to
a `Finset` and sums SEM-517's positively oriented local circle identities.
Semantic review: `SEM-518`.

Multiplicity remains inside each grouped ordinary-zero contribution. The
clockwise orientation of holes in a later perforated rectangle is not asserted
here.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set
open scoped BigOperators Topology

noncomputable section

/-- The finite index of distinct ordinary-zero and principal-pole candidate
locations in a closed rectangle. -/
noncomputable def dirichletExplicitFormulaCandidateSingularitiesFinset
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (z w : ℂ) : Finset ℂ :=
  (dirichletExplicitFormulaCandidateSingularities_finite chi z w).toFinset

@[simp]
theorem mem_dirichletExplicitFormulaCandidateSingularitiesFinset_iff
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    {z w rho : ℂ} :
    rho ∈ dirichletExplicitFormulaCandidateSingularitiesFinset chi z w ↔
      rho ∈ dirichletExplicitFormulaCandidateSingularities chi z w := by
  simp [dirichletExplicitFormulaCandidateSingularitiesFinset]

/-- The sum of all positively oriented candidate circles is `2 * pi * I`
times the sum of their exact grouped local contributions. -/
theorem
    sum_circleIntegral_dirichletExplicitFormulaIntegrand_eq_mul_sum_candidateContribution
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (x : ℝ) (z w : ℂ) {R : ℝ} (hR : 0 < R)
    (hcontained :
      ∀ rho ∈ dirichletExplicitFormulaCandidateSingularities chi z w,
        Metric.closedBall rho R ⊆ interior (Complex.Rectangle z w))
    (hdisjoint :
      (dirichletExplicitFormulaCandidateSingularities chi z w).PairwiseDisjoint
        (fun rho => Metric.closedBall rho R)) :
    (∑ rho ∈ dirichletExplicitFormulaCandidateSingularitiesFinset chi z w,
      ∮ s in C(rho, R), dirichletExplicitFormulaIntegrand chi x s) =
      (2 * Real.pi * Complex.I) *
        ∑ rho ∈ dirichletExplicitFormulaCandidateSingularitiesFinset chi z w,
          dirichletExplicitFormulaCandidateContribution chi x rho := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  exact
    circleIntegral_dirichletExplicitFormulaIntegrand_eq_candidateContribution
      chi x z w hR hcontained hdisjoint rho
        (mem_dirichletExplicitFormulaCandidateSingularitiesFinset_iff.mp hrho)

end

end BoundedGaps.Maynard
