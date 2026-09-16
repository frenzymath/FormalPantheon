import PrimesRestrictedDigits.Digits.ZeroCount
import PrimesRestrictedDigits.Foundations.CutoffMonotonicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Excluded-zero prime blocks

This file applies the primality filter to the exact positive digit-length
partition from `Digits.ZeroCount`.  It is an exact bridge only: estimates for
the individual prime blocks remain part of the later sieve argument.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 136.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Primes in the positive `(index + 1)`-digit block omitting decimal zero. -/
def zeroRestrictedPrimeBlock (index : ℕ) : Finset ℕ :=
  (zeroRestrictedNumberBlock index).filter Nat.Prime

private theorem paddedDecimalDigits_eq_digits_of_mem_zeroRestrictedNumberBlock
    {index n : ℕ} (hn : n ∈ zeroRestrictedNumberBlock index) :
    paddedDecimalDigits (index + 1) n = Nat.digits 10 n := by
  rcases Finset.mem_image.mp hn with ⟨L, hL, hLn⟩
  have hfixed := (Finset.mem_filter.mp hL).1
  have hvalid := (List.mem_fixedLengthDigits_iff (by norm_num : 1 < 10)).mp hfixed
  have hdigits : Nat.digits 10 n = L := by
    rw [← hLn]
    exact digits_ofDigits_zeroRestrictedBlock hL
  have hlen : (Nat.digits 10 n).length = index + 1 := by
    rw [hdigits]
    exact hvalid.1
  unfold paddedDecimalDigits Nat.digitsAppend
  rw [hlen]
  simp

theorem zeroRestrictedNumberBlock_eq_paddedRestrictedNumbers (index : ℕ) :
    zeroRestrictedNumberBlock index =
      paddedRestrictedNumbers (0 : Fin 10) (index + 1) := by
  classical
  ext n
  constructor
  · intro hn
    rw [mem_paddedRestrictedNumbers]
    have hblock := hn
    rcases Finset.mem_image.mp hblock with ⟨L, hL, hLn⟩
    have hfixed := (Finset.mem_filter.mp hL).1
    have hdigits : Nat.digits 10 n = L := by
      rw [← hLn]
      exact digits_ofDigits_zeroRestrictedBlock hL
    have hlt : n < 10 ^ (index + 1) := by
      rw [← hLn]
      exact Finset.mem_range.mp
        ((Nat.bijOn_ofDigits' (by norm_num : 1 < 10) (index + 1)).mapsTo hfixed)
    refine ⟨hlt, ?_⟩
    unfold paddedOmitsDecimalDigit
    rw [paddedDecimalDigits_eq_digits_of_mem_zeroRestrictedNumberBlock hn]
    have hnzero : n ≠ 0 := by
      intro hnzero
      have hcanon := digits_ofDigits_zeroRestrictedBlock hL
      rw [hLn, hnzero, Nat.digits_zero] at hcanon
      have hlen := (List.mem_fixedLengthDigits_iff (by norm_num : 1 < 10)).mp hfixed |>.1
      simp_all
    intro hzero
    apply (Finset.mem_filter.mp hL).2
    rw [← hdigits]
    exact hzero
  · intro hn
    rw [mem_paddedRestrictedNumbers] at hn
    rcases hn with ⟨hlt, homit⟩
    apply Finset.mem_image.mpr
    refine ⟨paddedDecimalDigits (index + 1) n, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · apply (List.mem_fixedLengthDigits_iff (by norm_num : 1 < 10)).mpr
        exact ⟨paddedDecimalDigits_length hlt,
          fun d hd => paddedDecimalDigits_lt_base hd⟩
      · simpa [paddedOmitsDecimalDigit, paddedDecimalDigits] using homit
    · exact ofDigits_paddedDecimalDigits (index + 1) n

@[simp] theorem mem_zeroRestrictedPrimeBlock {index n : ℕ} :
    n ∈ zeroRestrictedPrimeBlock index ↔
      n ∈ zeroRestrictedNumberBlock index ∧ n.Prime := by
  simp [zeroRestrictedPrimeBlock]

theorem zeroRestrictedPrimeBlock_pairwiseDisjoint (k : ℕ) :
    ((Finset.range k : Set ℕ).PairwiseDisjoint fun index =>
      zeroRestrictedPrimeBlock index) := by
  exact Finset.pairwiseDisjoint_filter
    (zeroRestrictedNumberBlock_pairwiseDisjoint k) Nat.Prime

theorem restrictedPrimeNumbers_zero_power_eq_biUnion (k : ℕ) :
    (restrictedNumbers (0 : Fin 10) (((10 ^ k : ℕ) : ℝ))).filter Nat.Prime =
      (Finset.range k).biUnion zeroRestrictedPrimeBlock := by
  rw [restrictedNumbers_zero_power_eq_biUnion, Finset.filter_biUnion]
  rfl

theorem restrictedPrimeCount_zero_power (k : ℕ) :
    restrictedPrimeCount (0 : Fin 10) (((10 ^ k : ℕ) : ℝ)) =
      ∑ i ∈ Finset.range k, (zeroRestrictedPrimeBlock i).card := by
  rw [restrictedPrimeCount, restrictedPrimeNumbers_zero_power_eq_biUnion,
    Finset.card_biUnion (zeroRestrictedPrimeBlock_pairwiseDisjoint k)]

/- The strict public cutoff is sandwiched by the two neighboring decimal
   powers; rewriting both endpoints exposes the corresponding finite prime
   block sums. -/
theorem restrictedPrimeCount_zero_cutoff_block_sandwich
    {X : ℝ} {k : ℕ}
    (hlo : ((10 ^ k : ℕ) : ℝ) ≤ X)
    (hupp : X < ((10 ^ (k + 1) : ℕ) : ℝ)) :
    (∑ i ∈ Finset.range k, (zeroRestrictedPrimeBlock i).card) ≤
        restrictedPrimeCount (0 : Fin 10) X ∧
      restrictedPrimeCount (0 : Fin 10) X ≤
        ∑ i ∈ Finset.range (k + 1), (zeroRestrictedPrimeBlock i).card := by
  constructor
  · rw [← restrictedPrimeCount_zero_power k]
    exact restrictedPrimeCount_le_of_le hlo
  · rw [← restrictedPrimeCount_zero_power (k + 1)]
    exact restrictedPrimeCount_le_of_le hupp.le

end

end PrimesRestrictedDigits
