import PrimesRestrictedDigits.Digits.Cardinality
import PrimesRestrictedDigits.Foundations.Intervals
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Excluded-zero power counts

The published proof handles excluded zero by successive positive digit-length
blocks (`MAYNARD-PRD-PUBLISHED`, Section 6, p. 136). This file formalizes that
finite decomposition while retaining the public strict cutoff and standard
representation of zero.
-/

namespace PrimesRestrictedDigits

noncomputable def zeroRestrictedNumberBlock (index : ℕ) : Finset ℕ := by
  classical
  exact (restrictedDigitLists (0 : Fin 10) (index + 1)).image (Nat.ofDigits 10)

theorem digits_ofDigits_zeroRestrictedBlock {index : ℕ} {L : List ℕ}
    (hL : L ∈ restrictedDigitLists (0 : Fin 10) (index + 1)) :
    Nat.digits 10 (Nat.ofDigits 10 L) = L := by
  rcases Finset.mem_filter.mp hL with ⟨hfixed, hzero⟩
  have hvalid := (List.mem_fixedLengthDigits_iff (by norm_num : 1 < 10)).mp hfixed
  apply Nat.digits_ofDigits 10 (by norm_num) L hvalid.2
  intro hne hlast
  have hmem : L.getLast hne ∈ L := List.getLast_mem hne
  apply hzero
  simpa [hlast] using hmem

theorem card_zeroRestrictedNumberBlock (index : ℕ) :
    (zeroRestrictedNumberBlock index).card = 9 ^ (index + 1) := by
  rw [zeroRestrictedNumberBlock, Finset.card_image_of_injOn,
    card_restrictedDigitLists]
  apply Set.InjOn.mono _
    (Nat.bijOn_ofDigits' (by norm_num : 1 < 10) (index + 1)).injOn
  intro L hL
  exact (Finset.mem_filter.mp hL).1

theorem zeroRestrictedNumberBlock_pairwiseDisjoint (k : ℕ) :
    ((Finset.range k : Set ℕ).PairwiseDisjoint fun index =>
      zeroRestrictedNumberBlock index) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro i hi j hj hinter
  rcases hinter with ⟨n, hn⟩
  have hni : n ∈ zeroRestrictedNumberBlock i :=
    (Finset.mem_inter.mp hn).1
  have hnj : n ∈ zeroRestrictedNumberBlock j :=
    (Finset.mem_inter.mp hn).2
  rcases Finset.mem_image.mp hni with ⟨Li, hLi, hEq_i⟩
  rcases Finset.mem_image.mp hnj with ⟨Lj, hLj, hEq_j⟩
  have hdLi := digits_ofDigits_zeroRestrictedBlock hLi
  have hdLj := digits_ofDigits_zeroRestrictedBlock hLj
  have hdigitsEq : Li = Lj := by
    calc
      Li = Nat.digits 10 (Nat.ofDigits 10 Li) := hdLi.symm
      _ = Nat.digits 10 n := by rw [hEq_i]
      _ = Nat.digits 10 (Nat.ofDigits 10 Lj) := by rw [hEq_j]
      _ = Lj := hdLj
  have hlenLi := (List.mem_fixedLengthDigits_iff (by norm_num : 1 < 10)).mp
    (Finset.mem_filter.mp hLi).1 |>.1
  have hlenLj := (List.mem_fixedLengthDigits_iff (by norm_num : 1 < 10)).mp
    (Finset.mem_filter.mp hLj).1 |>.1
  have hlenEq : Li.length = Lj.length := by rw [hdigitsEq]
  omega

theorem restrictedNumbers_zero_power_eq_biUnion (k : ℕ) :
    restrictedNumbers (0 : Fin 10) (((10 ^ k : ℕ) : ℝ)) =
      (Finset.range k).biUnion zeroRestrictedNumberBlock := by
  classical
  apply Finset.ext
  intro n
  constructor
  · intro hn
    have hn' := (mem_restrictedNumbers.mp hn)
    have hnat : n < 10 ^ k := by exact_mod_cast hn'.1
    have hnzero : n ≠ 0 := by
      intro hnzero
      subst n
      simpa using hn'.2
    have hLpos : 0 < (Nat.digits 10 n).length := by
      exact List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hnzero)
    have hLle : (Nat.digits 10 n).length ≤ k :=
      (Nat.digits_length_le_iff (by norm_num : 1 < 10) n).mpr hnat
    have hi : (Nat.digits 10 n).length - 1 ∈ Finset.range k := by
      rw [Finset.mem_range]
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨(Nat.digits 10 n).length - 1, hi, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨Nat.digits 10 n, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨(List.mem_fixedLengthDigits_iff (by norm_num : 1 < 10)).mpr
        ⟨by omega, ?_⟩, ?_⟩
      · intro d hd
        exact Nat.digits_lt_base (by norm_num) hd
      · rw [← standardDecimalDigits_eq_digits hnzero]
        exact (omitsDecimalDigit_iff _ _).mp hn'.2
    · exact Nat.ofDigits_digits 10 n
  · intro hn
    rcases Finset.mem_biUnion.mp hn with ⟨i, hi, hni⟩
    rcases Finset.mem_image.mp hni with ⟨L, hL, hEq⟩
    subst n
    rcases Finset.mem_filter.mp hL with ⟨hfixed, hzero⟩
    have hvalid := (List.mem_fixedLengthDigits_iff (by norm_num : 1 < 10)).mp hfixed
    have hcanon := digits_ofDigits_zeroRestrictedBlock hL
    have hnatlt : Nat.ofDigits 10 L < 10 ^ (i + 1) := by
      apply Finset.mem_range.mp
      exact (Nat.bijOn_ofDigits' (by norm_num : 1 < 10) (i + 1)).mapsTo hfixed
    have hi' : i < k := Finset.mem_range.mp hi
    have hik : i + 1 ≤ k := by omega
    have hnltk : Nat.ofDigits 10 L < 10 ^ k :=
      hnatlt.trans_le (Nat.pow_le_pow_right (by norm_num) hik)
    have hnzero : Nat.ofDigits 10 L ≠ 0 := by
      intro hz
      rw [hz, Nat.digits_zero] at hcanon
      have hlen := hvalid.1
      simp_all
    refine (mem_restrictedNumbers).mpr ⟨by exact_mod_cast hnltk, ?_⟩
    rw [omitsDecimalDigit_iff, standardDecimalDigits_eq_digits hnzero, hcanon]
    exact hzero

theorem restrictedCount_zero_power (k : ℕ) :
    restrictedCount (0 : Fin 10) (((10 ^ k : ℕ) : ℝ)) =
      ∑ i ∈ Finset.range k, 9 ^ (i + 1) := by
  rw [restrictedCount, restrictedNumbers_zero_power_eq_biUnion,
    Finset.card_biUnion (zeroRestrictedNumberBlock_pairwiseDisjoint k)]
  apply Finset.sum_congr rfl
  intro i hi
  exact card_zeroRestrictedNumberBlock i

end PrimesRestrictedDigits
