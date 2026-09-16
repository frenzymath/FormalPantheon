import Waring.Analytic.ChenNineBackSubstitution
import Waring.Analytic.ChenNineProductAggregate
import Waring.Analytic.PositiveShiftProductReindex

/-!
# Corrected rational-phase estimate in Chen's Lemma 9

This file assembles the valid three-step Weyl chain with the direct product
aggregate.  It retains the corrected triangular Cauchy factor from D-013.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The third Weyl aggregate for the rational fifth-power character satisfies
the direct product-fiber square bound. -/
theorem sq_weylDThree_fifthPowerChar_le_direct
    {P q : Nat} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (hP : 10 ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q)
    (hqUpper : (q : Real) ≤ 10 * (P : Real) ^ 4) :
    weylDThree (fifthPowerChar a) P ^ 2 ≤
      160 * (P : Real) ^ (36 / 5 : Real) *
        (Real.log P + 4) ^ (74 / 5 : Real) := by
  rw [weylDThree_fifthPowerChar_eq_restrictedQuadraticValue]
  exact sq_sum_restrictedQuadraticValue_le_direct
    a ha hP hqLower hqUpper

/-- Corrected rational-phase form of Chen's Lemma 9.  The coefficient uses
the valid triangular Cauchy factor rather than the stronger factor printed in
both source editions. -/
theorem norm_sum_fifthPowerChar_le
    {P q : Nat} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (hP : 10 ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q)
    (hqUpper : (q : Real) ≤ 10 * (P : Real) ^ 4) :
    ‖∑ x ∈ Finset.range P, fifthPowerChar a x‖ ≤
      (2 : Real) ^ (6 / 8 : Real) * (161 : Real) ^ (1 / 16 : Real) *
        (P : Real) ^ (19 / 20 : Real) *
          (Real.log P + 4) ^ (15 / 16 : Real) := by
  let z : Nat → Complex := fifthPowerChar a
  let T : Real := ‖∑ x ∈ Finset.range P, z x‖
  let B : Real := weylDOne z P
  let A : Real := weylDTwo z P
  let S : Real := weylDThree z P
  have hz : ∀ x, ‖z x‖ = 1 := fun x ↦ norm_fifthPowerChar_eq_one a x
  have hS : S ^ 2 ≤
      160 * (P : Real) ^ (36 / 5 : Real) *
        (Real.log P + 4) ^ (74 / 5 : Real) := by
    dsimp [S, z]
    exact sq_weylDThree_fifthPowerChar_le_direct
      a ha hP hqLower hqUpper
  have hresult := chenNine_corrected_backSubstitution T B A S hP
    (weylDOne_nonneg z P) (weylDTwo_nonneg z P)
    (weylDOne_le_sq z P hz) (weylDTwo_le_cube z P hz)
    (weylDThree_le_fourth z P hz)
    (norm_sum_range_sq_le_add_two_weylDOne z P hz)
    (weylDOne_sq_le z P hz) (two_mul_weylDTwo_sq_le z P hz) hS
  simpa only [T, z] using hresult

end Waring.Analytic
