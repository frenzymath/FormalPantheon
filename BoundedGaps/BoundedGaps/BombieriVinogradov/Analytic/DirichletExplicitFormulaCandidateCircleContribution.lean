import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaCandidateSingularities
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaZeroCircleIntegral
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaPrincipalZeroCircleIntegral

/-!
# Dirichlet explicit-formula candidate circle contribution

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115,
crosses ordinary Dirichlet-L zeros and the principal pole separately while
moving the modified explicit-formula contour. This file supplies the local
composition that attaches the correct residue coefficient to every selected
candidate disk. Semantic review: `SEM-517`.

The radius, rectangle interior, and pairwise-disjoint disks are hypotheses.
This theorem does not select a radius or perform a global contour shift.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set
open scoped Topology

noncomputable section

/-- The exact local coefficient attached to one distinct candidate location.

The principal-pole branch is selected only when both the character is
principal and the location is `1`. Otherwise the grouped ordinary-zero
coefficient retains its analytic multiplicity and source sign. -/
noncomputable def dirichletExplicitFormulaCandidateContribution
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (x : ℝ) (rho : ℂ) : ℂ := by
  classical
  exact if chi = 1 ∧ rho = 1 then
      dirichletExplicitFormulaPrincipalPoleResidue x
    else
      dirichletExplicitFormulaZeroResidue chi x rho

/-- Pairwise-disjoint candidate disks provide the zero-free hypotheses for the
appropriate ordinary-zero or principal-pole circle identity at every center.

For a principal ordinary zero, disjointness also excludes the pole at `1`.
The rectangle containment premise is needed to turn any additional zero in a
disk into a member of the candidate inventory. -/
theorem circleIntegral_dirichletExplicitFormulaIntegrand_eq_candidateContribution
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (x : ℝ) (z w : ℂ) {R : ℝ} (hR : 0 < R)
    (hcontained :
      ∀ sigma ∈ dirichletExplicitFormulaCandidateSingularities chi z w,
        Metric.closedBall sigma R ⊆ interior (Complex.Rectangle z w))
    (hdisjoint :
      (dirichletExplicitFormulaCandidateSingularities chi z w).PairwiseDisjoint
        (fun sigma => Metric.closedBall sigma R)) :
    ∀ rho ∈ dirichletExplicitFormulaCandidateSingularities chi z w,
      (∮ s in C(rho, R),
        dirichletExplicitFormulaIntegrand chi x s) =
        (2 * Real.pi * Complex.I) *
          dirichletExplicitFormulaCandidateContribution chi x rho := by
  intro rho hrho
  have hballRect : Metric.closedBall rho R ⊆ Complex.Rectangle z w :=
    (hcontained rho hrho).trans interior_subset
  by_cases hchi : chi = 1
  · subst chi
    by_cases hrhoOne : rho = 1
    · subst rho
      have hzeroFree : ∀ s ∈ Metric.closedBall (1 : ℂ) R \ {1},
          DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ N) s ≠ 0 := by
        intro s hs hzero
        have hsOne : s ≠ 1 := by simpa using hs.2
        have hsCandidate : s ∈
            dirichletExplicitFormulaCandidateSingularities
              (1 : DirichletCharacter ℂ N) z w := by
          rw [mem_dirichletExplicitFormulaCandidateSingularities_iff]
          exact ⟨hballRect hs.1, Or.inr ⟨Or.inl hsOne, hzero⟩⟩
        have hcenter := hdisjoint.elim_set hrho hsCandidate s hs.1
          (Metric.mem_closedBall_self hR.le)
        exact hsOne hcenter.symm
      simpa [dirichletExplicitFormulaCandidateContribution] using
        (circleIntegral_dirichletExplicitFormulaIntegrand_one_eq_principalPoleResidue
          (N := N) x hR hzeroFree)
    · have hpoleFree : (1 : ℂ) ∉ Metric.closedBall rho R := by
        intro hOneBall
        have hOneCandidate : (1 : ℂ) ∈
            dirichletExplicitFormulaCandidateSingularities
              (1 : DirichletCharacter ℂ N) z w := by
          rw [mem_dirichletExplicitFormulaCandidateSingularities_iff]
          exact ⟨hballRect hOneBall, Or.inl ⟨rfl, rfl⟩⟩
        exact hrhoOne (hdisjoint.elim_set hrho hOneCandidate 1 hOneBall
          (Metric.mem_closedBall_self hR.le))
      have hzeroFree : ∀ s ∈ Metric.closedBall rho R \ {rho},
          DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ N) s ≠ 0 := by
        intro s hs hzero
        have hsOne : s ≠ 1 := fun hsOne => hpoleFree (hsOne ▸ hs.1)
        have hsCandidate : s ∈
            dirichletExplicitFormulaCandidateSingularities
              (1 : DirichletCharacter ℂ N) z w := by
          rw [mem_dirichletExplicitFormulaCandidateSingularities_iff]
          exact ⟨hballRect hs.1, Or.inr ⟨Or.inl hsOne, hzero⟩⟩
        have hcenter := hdisjoint.elim_set hrho hsCandidate s hs.1
          (Metric.mem_closedBall_self hR.le)
        have hsRho : s ≠ rho := by simpa using hs.2
        exact hsRho hcenter.symm
      simpa [dirichletExplicitFormulaCandidateContribution, hrhoOne] using
        (circleIntegral_dirichletExplicitFormulaIntegrand_one_eq_zeroResidue
          (N := N) x rho hrhoOne hR hpoleFree hzeroFree)
  · have hzeroFree : ∀ s ∈ Metric.closedBall rho R \ {rho},
        DirichletCharacter.LFunction chi s ≠ 0 := by
      intro s hs hzero
      have hsCandidate : s ∈
          dirichletExplicitFormulaCandidateSingularities chi z w := by
        rw [mem_dirichletExplicitFormulaCandidateSingularities_iff]
        exact ⟨hballRect hs.1, Or.inr ⟨Or.inr hchi, hzero⟩⟩
      have hcenter := hdisjoint.elim_set hrho hsCandidate s hs.1
        (Metric.mem_closedBall_self hR.le)
      have hsRho : s ≠ rho := by simpa using hs.2
      exact hsRho hcenter.symm
    simpa [dirichletExplicitFormulaCandidateContribution, hchi] using
      (circleIntegral_dirichletExplicitFormulaIntegrand_eq_zeroResidue
        hchi x rho hR hzeroFree)

end

end BoundedGaps.Maynard
