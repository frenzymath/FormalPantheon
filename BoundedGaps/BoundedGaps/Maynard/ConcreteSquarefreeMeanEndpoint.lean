import BoundedGaps.Maynard.ReciprocalTotientPrimorialMainTerm
import BoundedGaps.Maynard.ConcreteCoprimeEndpoint

noncomputable section

namespace BoundedGaps.Maynard

open Filter

/-! The scalar squarefree mean estimate at the frozen Engelsma endpoint. -/

theorem eventually_abs_engelsmaSquarefreeMean_sub_mainTerm
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      |squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          (Real.log (engelsmaMaynardRadius alpha N) +
            Real.log (tripleLogCutoff (N - 1)))| ≤
        2 * (Real.exp 16 +
          4 * reciprocalTotientCorrectionQuarterConstant) +
          engelsmaMaynardModulus N +
          preSieveSingularSeries (tripleLogCutoff (N - 1)) * C := by
  obtain ⟨C, hC⟩ := exists_uniform_abs_primorialSquarefreeMean_sub_mainTerm
  refine ⟨C, ?_⟩
  filter_upwards [eventually_engelsmaMaynardModulus_le_radius halpha] with N hN
  unfold engelsmaMaynardModulus at hN ⊢
  exact hC (tripleLogCutoff (N - 1))
    (engelsmaMaynardRadius alpha N) hN

end BoundedGaps.Maynard
