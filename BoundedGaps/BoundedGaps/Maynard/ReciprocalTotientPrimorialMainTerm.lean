import BoundedGaps.Maynard.ReciprocalTotientCorrectionEndpoint
import BoundedGaps.Maynard.PrimorialMainTermBound

noncomputable section

namespace BoundedGaps.Maynard

/-! Primorial main term after inserting the exact correction endpoint. -/

theorem exists_uniform_abs_primorialSquarefreeMean_sub_mainTerm :
    ∃ C : ℝ, ∀ D Q : ℕ, primorial D ≤ Q →
      |squarefreeCoprimeInvTotientMean (primorial D) Q -
          preSieveSingularSeries D * (Real.log Q + Real.log D)| ≤
        2 * (Real.exp 16 +
          4 * reciprocalTotientCorrectionQuarterConstant) +
          primorial D + preSieveSingularSeries D * C := by
  obtain ⟨C, hC⟩ := exists_uniform_abs_primorialMainTerm_sub_logQ_logD
  refine ⟨C, fun D Q hQ => ?_⟩
  have hEndpoint :=
    abs_squarefreeCoprimeInvTotientMean_sub_coprimeHarmonicSum_le
      (primorial D) Q
  have hMain := hC D Q
  have hHMain := abs_coprimeHarmonicSum_sub_primorialMainTerm_le hQ
  calc
    |squarefreeCoprimeInvTotientMean (primorial D) Q -
          preSieveSingularSeries D * (Real.log Q + Real.log D)| ≤
        |squarefreeCoprimeInvTotientMean (primorial D) Q -
            coprimeHarmonicSum (primorial D) Q| +
          |coprimeHarmonicSum (primorial D) Q -
            preSieveSingularSeries D * (Real.log Q + Real.log D)| := by
      exact abs_sub_le _ _ _
    _ ≤ |squarefreeCoprimeInvTotientMean (primorial D) Q -
            coprimeHarmonicSum (primorial D) Q| +
          (|coprimeHarmonicSum (primorial D) Q -
            primorialCoprimeHarmonicMainTerm D Q| +
          |primorialCoprimeHarmonicMainTerm D Q -
            preSieveSingularSeries D * (Real.log Q + Real.log D)|) := by
      have h := abs_sub_le (coprimeHarmonicSum (primorial D) Q)
        (primorialCoprimeHarmonicMainTerm D Q)
        (preSieveSingularSeries D * (Real.log Q + Real.log D))
      linarith
    _ ≤ 2 * (Real.exp 16 +
          4 * reciprocalTotientCorrectionQuarterConstant) +
          primorial D + preSieveSingularSeries D * C := by
      have hMain' := add_le_add hHMain hMain
      linarith

end BoundedGaps.Maynard
