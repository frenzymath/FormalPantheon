import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaCandidateInterior
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaCandidateIsolation

/-!
# Selected Dirichlet explicit-formula candidate isolation

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115, moves the
Dirichlet explicit-formula contour across finitely many ordinary L-function
zeros and the separate principal pole. This file combines SEM-515's selected
rectangle with SEM-503's finite metric isolation theorem.

The quantitative horizontal clearances remain attached to the same selected
height. Candidate-to-circle conversion and finite residue summation remain
separate. Semantic review: `SEM-516`.
-/

namespace BoundedGaps.Maynard

open Complex Set

noncomputable section

/-- A selected explicit-formula rectangle admits one common positive radius
of contained, pairwise-disjoint candidate disks. -/
theorem exists_nat_dirichletExplicitFormulaCandidateSingularityRadius :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q)
        (x T : ℝ) (N : ℕ),
          1 < x → 2 ≤ T →
            ∃ T' : ℝ, T' ∈ Set.Icc T (T + 1) ∧
              (∀ rho : ℂ,
                (rho ≠ 1 ∨ chi ≠ 1) →
                  DirichletCharacter.LFunction chi rho = 0 →
                    (1 / ((C : ℝ) *
                        Real.log ((q : ℝ) * (T + 2))) ≤
                      |T' - rho.im|) ∧
                    (1 / ((C : ℝ) *
                        Real.log ((q : ℝ) * (T + 2))) ≤
                      |T' + rho.im|)) ∧
              ∃ R : ℝ, 0 < R ∧
                (∀ rho ∈
                    dirichletExplicitFormulaCandidateSingularities chi
                      (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) -
                        T' * Complex.I)
                      (((1 + 1 / Real.log x : ℝ) : ℂ) +
                        T' * Complex.I),
                  Metric.closedBall rho R ⊆
                    interior
                      (Complex.Rectangle
                        (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) -
                          T' * Complex.I)
                        (((1 + 1 / Real.log x : ℝ) : ℂ) +
                          T' * Complex.I))) ∧
                (dirichletExplicitFormulaCandidateSingularities chi
                    (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) -
                      T' * Complex.I)
                    (((1 + 1 / Real.log x : ℝ) : ℂ) +
                      T' * Complex.I)).PairwiseDisjoint
                  (fun rho => Metric.closedBall rho R) := by
  obtain ⟨C, hC, hselect⟩ :=
    exists_nat_dirichletExplicitFormulaCandidateSingularities_subset_interior
  refine ⟨C, hC, ?_⟩
  intro q _ chi x T N hx hT
  obtain ⟨T', hT', hclear, hinterior⟩ := hselect q chi x T N hx hT
  obtain ⟨R, hR, hcontained, hdisjoint⟩ :=
    exists_dirichletExplicitFormulaCandidateSingularityRadius chi
      (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) - T' * Complex.I)
      (((1 + 1 / Real.log x : ℝ) : ℂ) + T' * Complex.I)
      hinterior
  exact ⟨T', hT', hclear, R, hR, hcontained, hdisjoint⟩

end

end BoundedGaps.Maynard
