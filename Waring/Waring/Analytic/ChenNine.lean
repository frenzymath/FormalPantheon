import Waring.Analytic.ChenNineRationalPhase
import Waring.Analytic.PhasePerturbation

/-!
# Corrected Chen Lemma 9

This file combines the corrected rational-phase Weyl estimate with the finite
phase perturbation.  It exports no theorem with the unsupported coefficient
printed in the source editions.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Corrected Lemma 9 when the real frequency is displayed as its rational
center plus the approximation error. -/
theorem chen_lemma_nine_corrected_rational_add
    {P q : Nat} [NeZero q] (a : Nat) (epsilon : Real)
    (ha : IsUnit ((a : Nat) : ZMod q))
    (hP : 10 ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q)
    (hqUpper : (q : Real) ≤ 10 * (P : Real) ^ 4)
    (hepsilon : |epsilon| ≤
      1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖∑ x ∈ Finset.range P,
        realFifthPowerExponential ((a : Real) / q + epsilon) x‖ ≤
      (2 : Real) ^ (6 / 8 : Real) * (161 : Real) ^ (1 / 16 : Real) *
          (P : Real) ^ (19 / 20 : Real) *
            (Real.log P + 4) ^ (15 / 16 : Real) +
        (P : Real) ^ (24 / 25 : Real) := by
  have hPReal : (10 : Real) ^ 150 ≤ P := by exact_mod_cast hP
  have hperturbation :=
    norm_sum_realFifthPowerExponential_le_rational_add_error
      q a P epsilon hPReal hqLower hepsilon
  have hrational := norm_sum_fifthPowerChar_le
    ((a : Nat) : ZMod q) ha hP hqLower hqUpper
  exact hperturbation.trans (add_le_add hrational le_rfl)

/-- Source-facing corrected Lemma 9 for a separately named real frequency
`alpha = a / q + epsilon`. -/
theorem chen_lemma_nine_corrected
    {P q : Nat} [NeZero q] (a : Nat) (alpha epsilon : Real)
    (ha : IsUnit ((a : Nat) : ZMod q))
    (halpha : alpha = (a : Real) / q + epsilon)
    (hP : 10 ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q)
    (hqUpper : (q : Real) ≤ 10 * (P : Real) ^ 4)
    (hepsilon : |epsilon| ≤
      1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖∑ x ∈ Finset.range P, realFifthPowerExponential alpha x‖ ≤
      (2 : Real) ^ (6 / 8 : Real) * (161 : Real) ^ (1 / 16 : Real) *
          (P : Real) ^ (19 / 20 : Real) *
            (Real.log P + 4) ^ (15 / 16 : Real) +
        (P : Real) ^ (24 / 25 : Real) := by
  rw [halpha]
  exact chen_lemma_nine_corrected_rational_add
    a epsilon ha hP hqLower hqUpper hepsilon

end Waring.Analytic
