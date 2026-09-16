import Waring.LargeNumber.ScaleProduct

/-!
# Chen's Lemma 11

This file packages the digit construction as English Lemma 11 / Chinese
Lemma 12 [CHEN1964-EN, pp. 1567-1568; CHEN1964-ZH, p. 733].
-/

namespace Waring.LargeNumber

open scoped BigOperators

noncomputable section

/-- The finite family of eleven-fifth-power sums attached to the source input
`N`. -/
def chenElevenSums (N : Nat) : Finset Nat :=
  chenDigitSums (firstScale (mainScale N))

/-- Membership in the digit image is exactly witnessed by one permitted
eleven-tuple. -/
theorem mem_chenDigitSums_iff {p₁ u : Nat} :
    u ∈ chenDigitSums p₁ ↔
      ∃ x : ∀ i, DigitChoice p₁ i, u = ∑ i, (x i).1 ^ 5 := by
  constructor
  · intro hu
    rw [chenDigitSums, Finset.mem_image] at hu
    obtain ⟨x, _, rfl⟩ := hu
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    rw [chenDigitSums, Finset.mem_image]
    exact ⟨x, Finset.mem_univ x, rfl⟩

/-- Every member of the source family is a sum of eleven fifth powers of
natural numbers.  The last base may be zero, as in the source. -/
theorem mem_chenElevenSums_has_fifthPowers {N u : Nat}
    (hu : u ∈ chenElevenSums N) :
    ∃ x : Fin 11 → Nat, u = ∑ i, x i ^ 5 := by
  obtain ⟨x, hx⟩ := mem_chenDigitSums_iff.mp hu
  exact ⟨fun i ↦ (x i).1, hx⟩

/-- Every member of Chen's family lies in the weak range `u ≤ N / 4`
printed in the English proof. -/
theorem mem_chenElevenSums_le_quarter {N u : Nat} (hN : 10 ^ 780 ≤ N)
    (hu : u ∈ chenElevenSums N) :
    u ≤ N / 4 := by
  obtain ⟨x, hx⟩ := mem_chenDigitSums_iff.mp hu
  rw [hx]
  exact chenDigitCode_le_quarter hN x

/-- Chen's English Lemma 11 / Chinese Lemma 12: for `N ≥ 10^780` there
is a family of distinct eleven-fifth-power sums, all at most `N / 4`, with the
source's explicit cardinal lower bound. -/
theorem chen_lemma_eleven {N : Nat} (hN : 10 ^ 780 ≤ N) :
    (∀ u ∈ chenElevenSums N,
      u ≤ N / 4 ∧ ∃ x : Fin 11 → Nat, u = ∑ i, x i ^ 5) ∧
    (17 / 10 : Real) / 2 ^ 17 *
        (mainScale N : Real) ^ (5 - 5 * scaleRatio ^ 11) ≤
      ((chenElevenSums N).card : Real) := by
  constructor
  · intro u hu
    exact ⟨mem_chenElevenSums_le_quarter hN hu,
      mem_chenElevenSums_has_fifthPowers hu⟩
  · exact chenDigitSums_card_lower hN

end

end Waring.LargeNumber
