import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaCandidateCircleSum

/-!
# Dirichlet explicit-formula perforated regularity

`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 115, moves the
modified Dirichlet contour across ordinary zeros and the principal pole. This
file proves that SEM-497's integrand is complex differentiable at every
rectangle point outside SEM-502's guarded candidate set and hence on the
rectangle with open candidate balls removed.

Open balls are removed so their boundary circles remain available for the
later finite-excision theorem. No contour identity or orientation is asserted
here. Semantic review: `SEM-519`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

noncomputable section

/-- The modified integrand is regular at every rectangle point not listed as
an ordinary-zero or principal-pole candidate. -/
theorem
    differentiableAt_dirichletExplicitFormulaIntegrand_of_mem_rectangle_of_not_candidate
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (x : ℝ) {z w s : ℂ} (hsRect : s ∈ Complex.Rectangle z w)
    (hsNot :
      s ∉ dirichletExplicitFormulaCandidateSingularities chi z w) :
    DifferentiableAt ℂ (dirichletExplicitFormulaIntegrand chi x) s := by
  by_cases hchi : chi = 1
  · subst chi
    have hsOne : s ≠ 1 := by
      intro hs
      apply hsNot
      exact
        mem_dirichletExplicitFormulaCandidateSingularities_iff.mpr
          ⟨hsRect, Or.inl ⟨rfl, hs⟩⟩
    have hsL : DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ N) s ≠ 0 := by
      intro hsZero
      apply hsNot
      exact
        mem_dirichletExplicitFormulaCandidateSingularities_iff.mpr
          ⟨hsRect, Or.inr ⟨Or.inl hsOne, hsZero⟩⟩
    exact
      differentiableAt_dirichletExplicitFormulaIntegrand_one_of_ne_one_of_ne_zero
        x hsOne hsL
  · have hsL : DirichletCharacter.LFunction chi s ≠ 0 := by
      intro hsZero
      apply hsNot
      exact
        mem_dirichletExplicitFormulaCandidateSingularities_iff.mpr
          ⟨hsRect, Or.inr ⟨Or.inr hchi, hsZero⟩⟩
    exact
      differentiableAt_dirichletExplicitFormulaIntegrand_of_ne_zero
        hchi x hsL

/-- Removing positive-radius open balls at every candidate leaves a region on
which the modified integrand is complex differentiable. -/
theorem
    differentiableOn_dirichletExplicitFormulaIntegrand_perforatedRectangle
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (x : ℝ) (z w : ℂ) {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (dirichletExplicitFormulaIntegrand chi x)
      (Complex.Rectangle z w \
        ⋃ rho ∈
          dirichletExplicitFormulaCandidateSingularitiesFinset chi z w,
          Metric.ball rho R) := by
  intro s hs
  apply
    (differentiableAt_dirichletExplicitFormulaIntegrand_of_mem_rectangle_of_not_candidate
      chi x hs.1 ?_).differentiableWithinAt
  intro hsCandidate
  apply hs.2
  apply Set.mem_iUnion.2
  refine ⟨s, Set.mem_iUnion.2 ⟨?_, Metric.mem_ball_self hR⟩⟩
  exact
    mem_dirichletExplicitFormulaCandidateSingularitiesFinset_iff.mpr
      hsCandidate

end

end BoundedGaps.Maynard
