import BoundedGaps.Maynard.PrimorialCoprimeHarmonic
import BoundedGaps.Maynard.PrimePredecessorMertens

noncomputable section

/-! The prime-log lower-order term in the primorial coprime-harmonic main term. -/

namespace BoundedGaps.Maynard

open Real

theorem exists_uniform_abs_primorialMainTerm_sub_logQ_logD :
    ∃ C : ℝ, ∀ D Q : ℕ,
      |primorialCoprimeHarmonicMainTerm D Q -
          preSieveSingularSeries D * (Real.log Q + Real.log D)| ≤
        preSieveSingularSeries D * C := by
  obtain ⟨C, hC⟩ := exists_uniform_abs_primeLogPredecessorSum_sub_log
  refine ⟨C, fun D Q => ?_⟩
  have hS : 0 ≤ preSieveSingularSeries D := by
    rw [preSieveSingularSeries_eq_totient_div]
    positivity
  unfold primorialCoprimeHarmonicMainTerm
  calc
    |preSieveSingularSeries D *
          (Real.log Q + primeLogPredecessorSum D) -
        preSieveSingularSeries D * (Real.log Q + Real.log D)| =
        preSieveSingularSeries D *
          |primeLogPredecessorSum D - Real.log D| := by
      have hfactor :
          preSieveSingularSeries D *
              (Real.log Q + primeLogPredecessorSum D) -
            preSieveSingularSeries D * (Real.log Q + Real.log D) =
            preSieveSingularSeries D *
              (primeLogPredecessorSum D - Real.log D) := by ring
      rw [hfactor, abs_mul, abs_of_nonneg hS]
    _ ≤ preSieveSingularSeries D * C := by
      exact mul_le_mul_of_nonneg_left (hC D) hS

end BoundedGaps.Maynard
