import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaSelectedContour
import BoundedGaps.BombieriVinogradov.Analytic.DirichletModifiedPerron

/-!
# Primitive Dirichlet explicit formula

This file composes the independently audited selected-height contour estimate
and modified Perron inversion into the primitive natural-endpoint
specialization of `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 11.3.
The selected height is chosen before the arithmetic endpoint and disappears
from the source-facing conclusion. Semantic review: `SEM-534`.
-/

namespace BoundedGaps.Maynard

open Complex Set

noncomputable section

/-- The primitive natural-endpoint specialization of Koukoulopoulos
Theorem 11.3. -/
theorem
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaMainZeroTerms_le_of_isPrimitive :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ T : ℝ, 2 ≤ T →
            ∀ x : ℕ, 4 ≤ x → T ≤ (x : ℝ) →
              ‖twistedChebyshevSum x q chi -
                  dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T‖ ≤
                (K : ℝ) *
                  dirichletExplicitFormulaErrorScale (x : ℝ) q T := by
  obtain ⟨A, hA, C, hC, hcontour⟩ :=
    exists_nat_norm_dirichletExplicitFormulaNormalizedRightEdge_sub_mainZeroTerms_le
  obtain ⟨P, hP, hperron⟩ :=
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaNormalizedRightEdge_le
  let K : ℕ := P + 1700 * A * C
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  intro q _ chi hchi T hT
  obtain ⟨U, hU, _, hcontourU⟩ := hcontour q chi hchi T hT
  intro x hx hTx
  have hperronU := hperron q chi x T U hx hT hTx hU
  have hcontourX := hcontourU (x : ℝ) hTx
  let E : ℝ := dirichletExplicitFormulaErrorScale (x : ℝ) q T
  calc
    ‖twistedChebyshevSum x q chi -
          dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T‖ =
        ‖(twistedChebyshevSum x q chi -
            dirichletExplicitFormulaNormalizedRightEdge chi (x : ℝ) U) +
          (dirichletExplicitFormulaNormalizedRightEdge chi (x : ℝ) U -
            dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T)‖ := by
      congr 1
      ring
    _ ≤ ‖twistedChebyshevSum x q chi -
            dirichletExplicitFormulaNormalizedRightEdge chi (x : ℝ) U‖ +
          ‖dirichletExplicitFormulaNormalizedRightEdge chi (x : ℝ) U -
            dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T‖ :=
      norm_add_le _ _
    _ ≤ (P : ℝ) * E + 1700 * (A : ℝ) * C * E :=
      add_le_add hperronU hcontourX
    _ = (K : ℝ) *
        dirichletExplicitFormulaErrorScale (x : ℝ) q T := by
      dsimp [K, E]
      push_cast
      ring

end

end BoundedGaps.Maynard
