import PrimesRestrictedDigits.Foundations.Intervals
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Elementary positivity of the restricted carrier

Every excluded decimal digit leaves at least one one-digit prime in the
carrier.  This is used only to turn a weak upper comparison into a strict one;
it is not a prime-distribution estimate.
-/

namespace PrimesRestrictedDigits

theorem restrictedCount_pos_of_four_le {a : Fin 10} {X : ℝ} (hX : 4 ≤ X) :
    0 < (restrictedCount a X : ℝ) := by
  have htwo : (2 : ℝ) < X := by linarith
  have hthree : (3 : ℝ) < X := by linarith
  by_cases ha2 : a.val = 2
  · have hne : (3 : ℕ) ≠ a.val := by omega
    have hmem : (3 : ℕ) ∈ restrictedNumbers a X := by
      rw [mem_restrictedNumbers]
      refine ⟨hthree, ?_⟩
      simp [omitsDecimalDigit, standardDecimalDigits, hne]
    exact_mod_cast (Finset.card_pos.mpr ⟨3, hmem⟩)
  · have hne : (2 : ℕ) ≠ a.val := by omega
    have hmem : (2 : ℕ) ∈ restrictedNumbers a X := by
      rw [mem_restrictedNumbers]
      refine ⟨htwo, ?_⟩
      simp [omitsDecimalDigit, standardDecimalDigits, hne]
    exact_mod_cast (Finset.card_pos.mpr ⟨2, hmem⟩)

end PrimesRestrictedDigits
