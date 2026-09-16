import PrimesRestrictedDigits.Digits.PaddedExpansion
/-! # Cardinality -/

namespace PrimesRestrictedDigits

noncomputable def paddedRestrictedNumbers (a : Fin 10) (length : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (10 ^ length)).filter fun n =>
    paddedOmitsDecimalDigit a length n

noncomputable def restrictedDigitLists (a : Fin 10) (length : ℕ) : Finset (List ℕ) := by
  classical
  exact (List.fixedLengthDigits (by omega : 1 < 10) length).filter fun L =>
    a.val ∉ L

theorem mem_paddedRestrictedNumbers {a : Fin 10} {length n : ℕ} :
    n ∈ paddedRestrictedNumbers a length ↔
      n < 10 ^ length ∧ paddedOmitsDecimalDigit a length n := by
  classical
  simp [paddedRestrictedNumbers]

private theorem card_filter_consFixedLengthDigits (a : Fin 10) (length d : ℕ)
    (hrec : (restrictedDigitLists a length).card = 9 ^ length) :
    ((List.consFixedLengthDigits (by omega : 1 < 10) length d).filter
        (fun L => a.val ∉ L)).card =
      if d = a.val then 0 else 9 ^ length := by
  classical
  by_cases hda : d = a.val
  · rw [if_pos hda, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro L hL
    obtain ⟨tail, htail, rfl⟩ := Finset.mem_image.mp hL
    simp [hda]
  · have hda' : a.val ≠ d := Ne.symm hda
    have heq :
        (List.consFixedLengthDigits (by omega : 1 < 10) length d).filter
            (fun L => a.val ∉ L) =
          (restrictedDigitLists a length).image (fun L => d :: L) := by
      ext L
      constructor
      · intro hL
        rcases Finset.mem_filter.mp hL with ⟨hL, hnot⟩
        obtain ⟨tail, htail, rfl⟩ := Finset.mem_image.mp hL
        refine Finset.mem_image.mpr ⟨tail,
          Finset.mem_filter.mpr ⟨htail, ?_⟩, rfl⟩
        intro ha
        exact hnot (by simp [ha])
      · intro hL
        rcases Finset.mem_image.mp hL with ⟨tail, htail, rfl⟩
        rcases Finset.mem_filter.mp htail with ⟨htail, hnot⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨tail, htail, rfl⟩, ?_⟩
        simpa [hda'] using hnot
    rw [heq, Finset.card_image_of_injective _ (by
      intro L₁ L₂ h
      exact List.cons.inj h |>.2)]
    rw [if_neg hda]
    simpa [restrictedDigitLists] using hrec

theorem card_restrictedDigitLists (a : Fin 10) (length : ℕ) :
    (restrictedDigitLists a length).card = 9 ^ length := by
  classical
  induction length with
  | zero =>
      rw [restrictedDigitLists, List.fixedLengthDigits_zero, Finset.filter_singleton]
      simp
  | succ length ih =>
      rw [restrictedDigitLists, List.fixedLengthDigits_succ_eq_disjiUnion,
        Finset.filter_disjiUnion, Finset.card_disjiUnion]
      have hcard : ∀ d ∈ Finset.range 10,
          ((List.consFixedLengthDigits (by omega : 1 < 10) length d).filter
              (fun L => a.val ∉ L)).card =
            if d = a.val then 0 else 9 ^ length := by
        intro d hd
        exact card_filter_consFixedLengthDigits a length d ih
      have hsum :
          (∑ d ∈ Finset.range 10,
              ((List.consFixedLengthDigits (by omega : 1 < 10) length d).filter
                (fun L => a.val ∉ L)).card) =
            ∑ d ∈ Finset.range 10, (if d = a.val then 0 else 9 ^ length) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hcard d hd
      rw [hsum]
      have ha : a.val ∈ Finset.range 10 := by simp [a.isLt]
      simp [Finset.sum_ite, Finset.sum_const]
      rw [Finset.filter_ne', Finset.card_erase_of_mem ha]
      simp [pow_succ, Nat.mul_comm]

theorem bijOn_digitsAppend_paddedRestrictedNumbers (a : Fin 10) (length : ℕ) :
    Set.BijOn (Nat.digitsAppend 10 length)
      (paddedRestrictedNumbers a length) (restrictedDigitLists a length) := by
  classical
  let hb : 1 < 10 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hnrange := (Finset.mem_filter.mp hn).1
    have hbase := (Nat.bijOn_digitsAppend' hb length).mapsTo hnrange
    exact Finset.mem_filter.mpr ⟨hbase, by
      simpa [paddedOmitsDecimalDigit, paddedDecimalDigits] using
        (Finset.mem_filter.mp hn).2⟩
  · intro n₁ hn₁ n₂ hn₂ hEq
    exact (Nat.bijOn_digitsAppend' hb length).injOn
      (Finset.mem_filter.mp hn₁).1 (Finset.mem_filter.mp hn₂).1 hEq
  · intro L hL
    have hbase := (Nat.bijOn_digitsAppend' hb length).surjOn
      (Finset.mem_filter.mp hL).1
    rcases hbase with ⟨n, hn, hEq⟩
    refine ⟨n, Finset.mem_filter.mpr ⟨hn, ?_⟩, hEq⟩
    simpa [paddedOmitsDecimalDigit, paddedDecimalDigits, hEq] using
      (Finset.mem_filter.mp hL).2

theorem card_paddedRestrictedNumbers (a : Fin 10) (length : ℕ) :
    (paddedRestrictedNumbers a length).card = 9 ^ length := by
  rw [(bijOn_digitsAppend_paddedRestrictedNumbers a length).finsetCard_eq,
    card_restrictedDigitLists]

theorem restrictedNumbers_eq_paddedRestrictedNumbers_of_ne_zero {a : Fin 10}
    (ha : a.val ≠ 0) (length : ℕ) :
    restrictedNumbers a ((10 ^ length : ℕ) : ℝ) =
      paddedRestrictedNumbers a length := by
  classical
  ext n
  have hmem : n ∈ restrictedNumbers a ((10 ^ length : ℕ) : ℝ) ↔
      (n : ℝ) < ((10 ^ length : ℕ) : ℝ) ∧ omitsDecimalDigit a n := by
    simp [restrictedNumbers, Nat.lt_ceil]
  rw [hmem, mem_paddedRestrictedNumbers]
  constructor
  · rintro ⟨hn, homit⟩
    refine ⟨by exact_mod_cast hn, ?_⟩
    exact (paddedOmitsDecimalDigit_iff_omitsDecimalDigit a ha length n).2 homit
  · rintro ⟨hn, homit⟩
    refine ⟨by exact_mod_cast hn, ?_⟩
    exact (paddedOmitsDecimalDigit_iff_omitsDecimalDigit a ha length n).1 homit

end PrimesRestrictedDigits
