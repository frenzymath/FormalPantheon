import Waring.Analytic.WeylShiftReindex
import Mathlib.Algebra.Order.Chebyshev

/-!
# The triangular Cauchy step in fifth-degree Weyl differencing

This file records the exact number of positive-shift pairs and the resulting
Cauchy bound.  The factor is important because Chen's equation (10) has a
factor-of-two defect [CHEN1964-EN, p. 1555].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The zero-based positive-shift pairs `(h,y)` with actual shift `h+1`. -/
def positiveShiftPairs (P : Nat) : Finset (Sigma fun _ : Nat ↦ Nat) :=
  (Finset.range P).sigma fun h ↦ Finset.range (P - h - 1)

/-- There are exactly `P*(P-1)/2` positive-shift pairs. -/
theorem card_positiveShiftPairs (P : Nat) :
    (positiveShiftPairs P).card = P * (P - 1) / 2 := by
  rw [positiveShiftPairs, Finset.card_sigma]
  simp only [Finset.card_range]
  calc
    (∑ h ∈ Finset.range P, (P - h - 1)) =
        ∑ h ∈ Finset.range P, (P - 1 - h) := by
      apply Finset.sum_congr rfl
      intro h hh
      have hhP : h < P := Finset.mem_range.mp hh
      omega
    _ = ∑ h ∈ Finset.range P, h :=
      Finset.sum_range_reflect id P
    _ = P * (P - 1) / 2 := Finset.sum_range_id P

/-- Cauchy-Schwarz over the exact triangular positive-shift range. -/
theorem sq_sum_positiveShift_le_card_mul_sum_sq
    (F : Nat → Nat → Real) (P : Nat) :
    (∑ h ∈ Finset.range P, ∑ y ∈ Finset.range (P - h - 1),
        F h y) ^ 2 ≤
      ((P * (P - 1) / 2 : Nat) : Real) *
        ∑ h ∈ Finset.range P, ∑ y ∈ Finset.range (P - h - 1),
          F h y ^ 2 := by
  let pairs := positiveShiftPairs P
  have hCauchy := sq_sum_le_card_mul_sum_sq
    (s := pairs) (f := fun p ↦ F p.1 p.2)
  rw [show pairs.card = P * (P - 1) / 2 by
    simpa [pairs] using card_positiveShiftPairs P] at hCauchy
  simpa only [pairs, positiveShiftPairs, Finset.sum_sigma'] using hCauchy

end Waring.Analytic
