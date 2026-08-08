import Waring.Analytic.WeylShiftReindex

/-!
# The finite Weyl difference inequality

This file takes the triangle inequality after reindexing a strict correlation
by its positive shift.
-/

namespace Waring.Analytic

open scoped BigOperators ComplexConjugate

/-- A unit-norm finite sequence is bounded by the sum of the norms of its
positive-shift correlations. -/
theorem norm_sum_range_sq_le_sum_shiftCorrelation
    (z : Nat → Complex) (P : Nat) (hz : ∀ x < P, ‖z x‖ = 1) :
    ‖∑ x ∈ Finset.range P, z x‖ ^ 2 ≤
      P + 2 * ∑ h ∈ Finset.range P,
        ‖∑ y ∈ Finset.range (P - h - 1),
          z (y + h + 1) * conj (z y)‖ := by
  have hbase := norm_sum_range_sq_le_add_two_norm_strictUpper z P hz
  rw [strictUpperCorrelation_eq_sum_positiveShift] at hbase
  calc
    ‖∑ x ∈ Finset.range P, z x‖ ^ 2 ≤
        P + 2 * ‖∑ h ∈ Finset.range P,
          ∑ y ∈ Finset.range (P - h - 1),
            z (y + h + 1) * conj (z y)‖ := hbase
    _ ≤ P + 2 * ∑ h ∈ Finset.range P,
        ‖∑ y ∈ Finset.range (P - h - 1),
          z (y + h + 1) * conj (z y)‖ := by
      gcongr
      exact norm_sum_le _ _

end Waring.Analytic
