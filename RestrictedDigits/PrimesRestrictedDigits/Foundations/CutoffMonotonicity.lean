import PrimesRestrictedDigits.Digits.Cardinality
import PrimesRestrictedDigits.Foundations.Intervals

/-!
# Cutoff monotonicity and the nonzero-digit power sandwich

These are the elementary set-theoretic pieces of the paper's power-of-ten
reduction (`MAYNARD-PRD-PUBLISHED`, Sections 2 and 6). The excluded-zero block
model and all prime estimates remain separate.
-/

namespace PrimesRestrictedDigits

theorem restrictedNumbers_subset_of_le {a : Fin 10} {X Y : ℝ} (hXY : X ≤ Y) :
    restrictedNumbers a X ⊆ restrictedNumbers a Y := by
  intro n hn
  rw [mem_restrictedNumbers] at hn ⊢
  exact ⟨lt_of_lt_of_le hn.1 hXY, hn.2⟩

theorem restrictedCount_le_of_le {a : Fin 10} {X Y : ℝ} (hXY : X ≤ Y) :
    restrictedCount a X ≤ restrictedCount a Y := by
  exact Finset.card_le_card (restrictedNumbers_subset_of_le hXY)

theorem restrictedPrimeCount_le_of_le {a : Fin 10} {X Y : ℝ} (hXY : X ≤ Y) :
    restrictedPrimeCount a X ≤ restrictedPrimeCount a Y := by
  apply Finset.card_le_card
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hn, hp⟩
  refine Finset.mem_filter.mpr ⟨restrictedNumbers_subset_of_le hXY hn, hp⟩

theorem restrictedCount_bounds_of_decimalPower_interval_of_ne_zero
    {a : Fin 10} (ha : a.val ≠ 0) {X : ℝ} {k : ℕ}
    (hlo : ((10 ^ k : ℕ) : ℝ) ≤ X)
    (hupp : X < ((10 ^ (k + 1) : ℕ) : ℝ)) :
    9 ^ k ≤ restrictedCount a X ∧
      restrictedCount a X ≤ 9 ^ (k + 1) := by
  have hlow := restrictedNumbers_eq_paddedRestrictedNumbers_of_ne_zero ha k
  have hupp' := restrictedNumbers_eq_paddedRestrictedNumbers_of_ne_zero ha (k + 1)
  constructor
  · calc
      9 ^ k = (paddedRestrictedNumbers a k).card :=
        (card_paddedRestrictedNumbers a k).symm
      _ = (restrictedNumbers a ((10 ^ k : ℕ) : ℝ)).card := by rw [hlow]
      _ ≤ (restrictedNumbers a X).card :=
        Finset.card_le_card (restrictedNumbers_subset_of_le hlo)
      _ = restrictedCount a X := rfl
  · calc
      restrictedCount a X = (restrictedNumbers a X).card := rfl
      _ ≤ (restrictedNumbers a ((10 ^ (k + 1) : ℕ) : ℝ)).card :=
        Finset.card_le_card (restrictedNumbers_subset_of_le hupp.le)
      _ = (paddedRestrictedNumbers a (k + 1)).card := by rw [hupp']
      _ = 9 ^ (k + 1) := card_paddedRestrictedNumbers a (k + 1)

end PrimesRestrictedDigits
