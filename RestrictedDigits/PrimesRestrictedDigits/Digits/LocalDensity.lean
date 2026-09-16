import PrimesRestrictedDigits.Digits.Cardinality
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FinCases

/-!
# Decimal local density

This proves the fixed-length coprime digit proportion used in the M3
calculation on `MAYNARD-PRD-PUBLISHED`, p. 189.
-/

namespace PrimesRestrictedDigits

/-- The source's decimal local factor `kappa_A`, kept in exact rational form. -/
def restrictedDigitDensity (a : Fin 10) : Rat :=
  if Nat.Coprime a.val 10 then
    10 * ((Nat.totient 10 : Rat) - 1) /
      (9 * (Nat.totient 10 : Rat))
  else 10 / 9

/-- The two explicit values of the decimal local factor. -/
theorem restrictedDigitDensity_eq (a : Fin 10) :
    restrictedDigitDensity a =
      if Nat.Coprime a.val 10 then 5 / 6 else 10 / 9 := by
  have htotient : Nat.totient 10 = 4 := by decide
  unfold restrictedDigitDensity
  rw [htotient]
  by_cases ha : Nat.Coprime a.val 10
  · rw [if_pos ha, if_pos ha]
    norm_num
  · rw [if_neg ha, if_neg ha]

private theorem card_filter_coprime_paddedRestrictedNumbers_succ
    (a : Fin 10) (k : Nat) :
    ((paddedRestrictedNumbers a (k + 1)).filter
      (fun n => Nat.Coprime n 10)).card =
      (if Nat.Coprime a.val 10 then 3 else 4) * 9 ^ k := by
  let source := (paddedRestrictedNumbers a (k + 1)).filter
    fun n => Nat.Coprime n 10
  let target := (restrictedDigitLists a (k + 1)).filter
    fun L => Nat.Coprime (Nat.ofDigits 10 L) 10
  have hcard : source.card = target.card := by
    apply Finset.card_nbij (Nat.digitsAppend 10 (k + 1))
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnPadded, hnCoprime⟩
      apply Finset.mem_filter.mpr
      refine ⟨(bijOn_digitsAppend_paddedRestrictedNumbers a (k + 1)).mapsTo
        hnPadded, ?_⟩
      rw [show Nat.ofDigits 10 (Nat.digitsAppend 10 (k + 1) n) = n by
        exact ofDigits_paddedDecimalDigits (k + 1) n]
      exact hnCoprime
    · intro n hn m hm hnm
      exact (bijOn_digitsAppend_paddedRestrictedNumbers a (k + 1)).injOn
        (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hm).1 hnm
    · intro L hL
      rcases Finset.mem_filter.mp hL with ⟨hLList, hLCoprime⟩
      rcases (bijOn_digitsAppend_paddedRestrictedNumbers a (k + 1)).surjOn
          hLList with ⟨n, hnPadded, hnL⟩
      refine ⟨n, Finset.mem_filter.mpr ⟨hnPadded, ?_⟩, hnL⟩
      have hof : Nat.ofDigits 10 L = n := by
        rw [← hnL]
        exact ofDigits_paddedDecimalDigits (k + 1) n
      simpa [hof] using hLCoprime
  have hfiber (d : Nat) :
      ((((List.consFixedLengthDigits (by omega : 1 < 10) k d).filter
          fun L => a.val ∉ L).filter
          fun L => Nat.Coprime (Nat.ofDigits 10 L) 10).card) =
        if d = a.val then 0
        else if Nat.Coprime d 10 then 9 ^ k else 0 := by
    by_cases hda : d = a.val
    · rw [if_pos hda]
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro L hL
      rcases Finset.mem_filter.mp hL with ⟨hL, hnot⟩
      rcases Finset.mem_image.mp hL with ⟨T, hT, rfl⟩
      simp [hda] at hnot
    · rw [if_neg hda]
      by_cases hdCoprime : Nat.Coprime d 10
      · rw [if_pos hdCoprime]
        have heq :
            ((List.consFixedLengthDigits (by omega : 1 < 10) k d).filter
                fun L => a.val ∉ L).filter
                (fun L => Nat.Coprime (Nat.ofDigits 10 L) 10) =
              (restrictedDigitLists a k).image fun T => d :: T := by
          ext L
          constructor
          · intro hL
            rcases Finset.mem_filter.mp hL with ⟨hL, hcoprime⟩
            rcases Finset.mem_filter.mp hL with ⟨hL, hnot⟩
            rcases Finset.mem_image.mp hL with ⟨T, hT, rfl⟩
            apply Finset.mem_image.mpr
            refine ⟨T, Finset.mem_filter.mpr ⟨hT, ?_⟩, rfl⟩
            intro haT
            exact hnot (by simp [haT])
          · intro hL
            rcases Finset.mem_image.mp hL with ⟨T, hT, rfl⟩
            rcases Finset.mem_filter.mp hT with ⟨hT, hnot⟩
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_filter.mpr
              ⟨Finset.mem_image.mpr ⟨T, hT, rfl⟩, ?_⟩, ?_⟩
            · simpa [Ne.symm hda] using hnot
            · simpa only [Nat.ofDigits_cons,
                Nat.coprime_add_mul_left_left] using hdCoprime
        rw [heq, Finset.card_image_of_injective _]
        · exact card_restrictedDigitLists a k
        · intro T U hTU
          exact List.cons.inj hTU |>.2
      · rw [if_neg hdCoprime]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro L hL hcoprime
        rcases Finset.mem_filter.mp hL with ⟨hL, hnot⟩
        rcases Finset.mem_image.mp hL with ⟨T, hT, rfl⟩
        apply hdCoprime
        simpa only [Nat.ofDigits_cons,
          Nat.coprime_add_mul_left_left] using hcoprime
  change source.card = _
  rw [hcard]
  unfold target restrictedDigitLists
  rw [List.fixedLengthDigits_succ_eq_disjiUnion,
    Finset.filter_disjiUnion, Finset.filter_disjiUnion,
    Finset.card_disjiUnion]
  simp_rw [hfiber]
  have hc3 : Nat.gcd 3 10 = 1 := by decide
  have hc4 : Nat.gcd 4 10 ≠ 1 := by decide
  have hc5 : Nat.gcd 5 10 ≠ 1 := by decide
  have hc6 : Nat.gcd 6 10 ≠ 1 := by decide
  have hc7 : Nat.gcd 7 10 = 1 := by decide
  have hc8 : Nat.gcd 8 10 ≠ 1 := by decide
  have hc9 : Nat.gcd 9 10 = 1 := by decide
  have heven : ¬Odd 10 := by decide
  fin_cases a <;>
    simp [Finset.sum_range_succ, Nat.coprime_iff_gcd_eq_one, hc3, hc4,
      hc5, hc6, hc7, hc8, hc9] <;> ring

/-- Among positive-length restricted decimal words, coprimality to ten is
controlled by the final digit. -/
theorem card_filter_coprime_paddedRestrictedNumbers
    (a : Fin 10) {K : Nat} (hK : 0 < K) :
    ((paddedRestrictedNumbers a K).filter
      (fun n => Nat.Coprime n 10)).card =
      (if Nat.Coprime a.val 10 then 3 else 4) * 9 ^ (K - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  simpa [Nat.succ_eq_add_one] using
    card_filter_coprime_paddedRestrictedNumbers_succ a k

/-- The coprime restricted-digit count gives exactly the source local
density. -/
theorem ten_div_totient_mul_card_coprime_paddedRestrictedNumbers
    (a : Fin 10) {K : Nat} (hK : 0 < K) :
    (10 : Rat) / (Nat.totient 10 : Rat) *
        (((paddedRestrictedNumbers a K).filter
          (fun n => Nat.Coprime n 10)).card : Rat) =
      restrictedDigitDensity a *
        ((paddedRestrictedNumbers a K).card : Rat) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  have htotient : Nat.totient 10 = 4 := by decide
  rw [card_filter_coprime_paddedRestrictedNumbers_succ,
    card_paddedRestrictedNumbers, restrictedDigitDensity, htotient]
  by_cases ha : Nat.Coprime a.val 10
  · simp only [if_pos ha]
    norm_num [pow_succ]
    ring
  · simp only [if_neg ha]
    norm_num [pow_succ]
    ring

end PrimesRestrictedDigits
