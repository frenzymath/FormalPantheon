import PrimesRestrictedDigits.Digits.Cardinality

/-!
# Fixed-length digit Fourier factorization

This is the exact finite product identity underlying the transform
`S_A` in `MAYNARD-PRD-PUBLISHED`, Section 4. Analytic norm and moment estimates
are intentionally separate proof nodes.
-/

namespace PrimesRestrictedDigits

def allowedDecimalDigits (a : Fin 10) : Finset ℕ :=
  (Finset.range 10).filter fun d => d ≠ a.val

noncomputable def digitPhase (length frequency n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    ((n * frequency : ℕ) : ℂ) / ((10 ^ length : ℕ) : ℂ))

noncomputable def digitListFourierSum (a : Fin 10) (length frequency : ℕ) : ℂ :=
  ∑ L ∈ restrictedDigitLists a length, digitPhase length frequency (Nat.ofDigits 10 L)

noncomputable def paddedDigitFourierSum (a : Fin 10) (length frequency : ℕ) : ℂ :=
  ∑ n ∈ paddedRestrictedNumbers a length, digitPhase length frequency n

noncomputable def digitFourierFactor (a : Fin 10) : ℕ → ℕ → ℂ
  | 0, _ => 1
  | length + 1, frequency =>
      (∑ d ∈ allowedDecimalDigits a, digitPhase (length + 1) frequency d) *
        digitFourierFactor a length frequency

private theorem digitPhase_cons (length frequency d : ℕ) (tail : List ℕ) :
    digitPhase (length + 1) frequency (Nat.ofDigits 10 (d :: tail)) =
      digitPhase (length + 1) frequency d *
        digitPhase length frequency (Nat.ofDigits 10 tail) := by
  rw [digitPhase, digitPhase, digitPhase, Nat.ofDigits_cons, ← Complex.exp_add]
  congr 1
  have hden : ((10 ^ (length + 1) : ℕ) : ℂ) =
      ((10 ^ length : ℕ) : ℂ) * 10 := by
    rw [pow_succ]
    norm_num
  rw [hden]
  field_simp
  push_cast
  ring

theorem digitListFourierSum_eq_factor (a : Fin 10) (length frequency : ℕ) :
    digitListFourierSum a length frequency =
      digitFourierFactor a length frequency := by
  induction length with
  | zero =>
      rw [digitListFourierSum, restrictedDigitLists, List.fixedLengthDigits_zero,
        Finset.filter_singleton]
      simp [digitFourierFactor, digitPhase]
  | succ length ih =>
      rw [digitListFourierSum, restrictedDigitLists,
        List.fixedLengthDigits_succ_eq_disjiUnion, Finset.filter_disjiUnion,
        Finset.sum_disjiUnion]
      rw [digitFourierFactor]
      have hhead (d : ℕ) :
          (∑ L ∈ (List.consFixedLengthDigits (by omega : 1 < 10) length d).filter
              (fun L => a.val ∉ L),
            digitPhase (length + 1) frequency (Nat.ofDigits 10 L)) =
            if d = a.val then 0 else
              ∑ T ∈ restrictedDigitLists a length,
                digitPhase (length + 1) frequency (Nat.ofDigits 10 (d :: T)) := by
        classical
        by_cases hda : d = a.val
        · rw [if_pos hda]
          have hempty :
              (List.consFixedLengthDigits (by omega : 1 < 10) length d).filter
                  (fun L => a.val ∉ L) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro L hL
            obtain ⟨tail, htail, rfl⟩ := Finset.mem_image.mp hL
            simp [hda]
          rw [hempty]
          simp
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
              refine Finset.mem_filter.mpr
                ⟨Finset.mem_image.mpr ⟨tail, htail, rfl⟩, ?_⟩
              simpa [hda'] using hnot
          rw [heq, Finset.sum_image]
          · rw [if_neg hda]
          · intro L₁ hL₁ L₂ hL₂ h
            exact List.cons.inj h |>.2
      calc
        (∑ i ∈ Finset.range 10,
            ∑ L ∈ (List.consFixedLengthDigits (by omega : 1 < 10) length i).filter
              (fun L => a.val ∉ L),
              digitPhase (length + 1) frequency (Nat.ofDigits 10 L)) =
            ∑ i ∈ Finset.range 10,
              (if i = a.val then 0 else
                ∑ T ∈ restrictedDigitLists a length,
                  digitPhase (length + 1) frequency (Nat.ofDigits 10 (i :: T))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hhead i
        _ = ∑ i ∈ allowedDecimalDigits a,
              ∑ T ∈ restrictedDigitLists a length,
                digitPhase (length + 1) frequency (Nat.ofDigits 10 (i :: T)) := by
          rw [allowedDecimalDigits]
          calc
            (∑ i ∈ Finset.range 10,
                (if i = a.val then 0 else
                  ∑ T ∈ restrictedDigitLists a length,
                    digitPhase (length + 1) frequency (Nat.ofDigits 10 (i :: T)))) =
                ∑ i ∈ Finset.range 10,
                  (if i ≠ a.val then
                    ∑ T ∈ restrictedDigitLists a length,
                      digitPhase (length + 1) frequency (Nat.ofDigits 10 (i :: T))
                   else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases h : i = a.val <;> simp [h]
            _ = ∑ i ∈ (Finset.range 10).filter (fun i => i ≠ a.val),
                  ∑ T ∈ restrictedDigitLists a length,
                    digitPhase (length + 1) frequency (Nat.ofDigits 10 (i :: T)) := by
              rw [Finset.sum_filter]
        _ = (∑ i ∈ allowedDecimalDigits a,
              digitPhase (length + 1) frequency i) *
            (∑ T ∈ restrictedDigitLists a length,
              digitPhase length frequency (Nat.ofDigits 10 T)) := by
          rw [Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro T hT
          exact digitPhase_cons length frequency i T
        _ = digitFourierFactor a (length + 1) frequency := by
          change (∑ i ∈ allowedDecimalDigits a,
              digitPhase (length + 1) frequency i) *
                digitListFourierSum a length frequency =
            (∑ i ∈ allowedDecimalDigits a,
              digitPhase (length + 1) frequency i) *
                digitFourierFactor a length frequency
          rw [ih]

theorem paddedDigitFourierSum_eq_factor (a : Fin 10) (length frequency : ℕ) :
    paddedDigitFourierSum a length frequency =
      digitFourierFactor a length frequency := by
  rw [← digitListFourierSum_eq_factor]
  apply Finset.sum_nbij (Nat.digitsAppend 10 length)
  · exact (bijOn_digitsAppend_paddedRestrictedNumbers a length).mapsTo
  · exact (bijOn_digitsAppend_paddedRestrictedNumbers a length).injOn
  · exact (bijOn_digitsAppend_paddedRestrictedNumbers a length).surjOn
  · intro n hn
    change digitPhase length frequency n =
      digitPhase length frequency (Nat.ofDigits 10 (paddedDecimalDigits length n))
    rw [ofDigits_paddedDecimalDigits]

end PrimesRestrictedDigits
