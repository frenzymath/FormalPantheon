import PrimesRestrictedDigits.Fourier.ContinuousTransformProperties
import PrimesRestrictedDigits.Fourier.FirstMoment
import PrimesRestrictedDigits.Fourier.ShiftedFrequencyWindow
import PrimesRestrictedDigits.Fourier.WordProduct

/-!
# Continuous first-moment cell bound

This implements the repaired equal-scale cell estimate downstream of `MAYNARD-PRD-PUBLISHED`,
Lemma 10.3, pp. 173--175. Four explicit terminal digits replace the source's undefined
trailing windows.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem concatenatedDigitWindow_frequencySplit
    (steps : Nat) (frequency : Fin (10 ^ (steps + 4))) (start : Fin steps) :
    let split := (Fin.appendEquiv steps 4).symm
      (frequencyDigitWord (steps + 4) frequency)
    concatenatedDigitWindow split.1 split.2 start =
      frequencyDigitWindow (steps + 4) frequency.val start.val 4
        frequency.isLt := by
  dsimp only
  funext offset
  have happly := congrFun
    ((Fin.appendEquiv steps 4).apply_symm_apply
      (frequencyDigitWord (steps + 4) frequency))
    (⟨start.val + offset.val, by omega⟩ : Fin (steps + 4))
  simpa [concatenatedDigitWindow, concatenatedDigitWord,
    frequencyDigitWindow, shiftedFrequencyDecimalDigit,
    frequencyDigitWord] using happly

theorem shiftedCellMagnitude_le_digitWordPathProduct
    (digit : Fin 10) (steps : Nat) (frequency : Fin (10 ^ (steps + 4)))
    {offset : Real} (hoffset : offset ∈ Set.Icc (0 : Real) 1) :
    let split := (Fin.appendEquiv steps 4).symm
      (frequencyDigitWord (steps + 4) frequency)
    normalizedPaddedDigitFourierMagnitudeAt digit (steps + 4)
        (((frequency.val : Real) + offset) / (10 : Real) ^ (steps + 4)) <=
      digitWordPathProduct (poweredWindowMajorantWeight digit 4 1)
        split.1 split.2 := by
  dsimp only
  rw [normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct,
    Fin.prod_univ_add]
  let split := (Fin.appendEquiv steps 4).symm
    (frequencyDigitWord (steps + 4) frequency)
  have hprefixNonneg :
      0 <= ∏ start : Fin steps,
        digitKernel digit ((10 : Real) ^ (Fin.castAdd 4 start).val *
          (((frequency.val : Real) + offset) / (10 : Real) ^ (steps + 4))) := by
    apply Finset.prod_nonneg
    intro start _
    exact digitKernel_nonneg _ _
  have hterminal :
      (∏ start : Fin 4,
        digitKernel digit ((10 : Real) ^ (Fin.natAdd steps start).val *
          (((frequency.val : Real) + offset) / (10 : Real) ^ (steps + 4)))) <= 1 := by
    exact Finset.prod_le_one
      (fun start _ => digitKernel_nonneg _ _)
      (fun start _ => digitKernel_le_one _ _)
  have hprefix :
      (∏ start : Fin steps,
        digitKernel digit ((10 : Real) ^ (Fin.castAdd 4 start).val *
          (((frequency.val : Real) + offset) / (10 : Real) ^ (steps + 4)))) <=
        digitWordPathProduct (poweredWindowMajorantWeight digit 4 1)
          split.1 split.2 := by
    unfold digitWordPathProduct
    apply Finset.prod_le_prod
    · intro start _
      exact digitKernel_nonneg _ _
    · intro start _
      have hlocal := digitKernel_shiftedCell_le_windowMajorant digit
        (length := steps + 4) (frequency := frequency.val)
        (start := start.val) (offset := offset)
        (by omega) frequency.isLt hoffset
      rw [concatenatedDigitWindow_frequencySplit]
      simpa [poweredWindowMajorantWeight] using hlocal
  calc
    (∏ start : Fin steps,
          digitKernel digit ((10 : Real) ^ (Fin.castAdd 4 start).val *
            (((frequency.val : Real) + offset) / (10 : Real) ^ (steps + 4)))) *
        ∏ start : Fin 4,
          digitKernel digit ((10 : Real) ^ (Fin.natAdd steps start).val *
            (((frequency.val : Real) + offset) / (10 : Real) ^ (steps + 4))) <=
        (∏ start : Fin steps,
          digitKernel digit ((10 : Real) ^ (Fin.castAdd 4 start).val *
            (((frequency.val : Real) + offset) / (10 : Real) ^ (steps + 4)))) * 1 :=
      mul_le_mul_of_nonneg_left hterminal hprefixNonneg
    _ = ∏ start : Fin steps,
          digitKernel digit ((10 : Real) ^ (Fin.castAdd 4 start).val *
            (((frequency.val : Real) + offset) / (10 : Real) ^ (steps + 4))) := by
      rw [mul_one]
    _ <= digitWordPathProduct (poweredWindowMajorantWeight digit 4 1)
        split.1 split.2 := hprefix

private noncomputable def frequencySplitEquiv (steps : Nat) :
    Fin (10 ^ (steps + 4)) ≃
      DigitWindowState steps × DigitWindowState 4 :=
  (frequencyDigitWordEquiv (steps + 4)).trans (Fin.appendEquiv steps 4).symm

private theorem firstMomentContinuousCellSum_add_four_le
    (digit : Fin 10) (steps : Nat) {offset : Real}
    (hoffset : offset ∈ Set.Icc (0 : Real) 1) :
    (∑ frequency : Fin (10 ^ (steps + 4)),
      normalizedPaddedDigitFourierMagnitudeAt digit (steps + 4)
        (((frequency.val : Real) + offset) / (10 : Real) ^ (steps + 4))) <=
      20000 * (((10 ^ (steps + 4) : Nat) : Real) ^ (27 / 77 : Real)) := by
  let weight := poweredWindowMajorantWeight digit 4 1
  let splitEquiv := frequencySplitEquiv steps
  calc
    (∑ frequency : Fin (10 ^ (steps + 4)),
        normalizedPaddedDigitFourierMagnitudeAt digit (steps + 4)
          (((frequency.val : Real) + offset) / (10 : Real) ^ (steps + 4))) <=
        ∑ frequency : Fin (10 ^ (steps + 4)),
          digitWordPathProduct weight (splitEquiv frequency).1
            (splitEquiv frequency).2 := by
      apply Finset.sum_le_sum
      intro frequency _
      exact shiftedCellMagnitude_le_digitWordPathProduct digit steps frequency hoffset
    _ = ∑ pair : DigitWindowState steps × DigitWindowState 4,
          digitWordPathProduct weight pair.1 pair.2 := by
      exact Equiv.sum_comp splitEquiv
        (fun pair : DigitWindowState steps × DigitWindowState 4 =>
          digitWordPathProduct weight pair.1 pair.2)
    _ = ∑ future : DigitWindowState 4,
          digitWordPathSum weight steps future := by
      rw [Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro future _
      exact (digitWordPathSum_eq_sum_wordProduct weight future).symm
    _ <= ∑ _future : DigitWindowState 4,
          2 * (((10 ^ steps : Nat) : Real) ^ (27 / 77 : Real)) := by
      apply Finset.sum_le_sum
      intro future _
      exact digitWordPathSum_firstMoment_le digit steps future
    _ = 20000 * (((10 ^ steps : Nat) : Real) ^ (27 / 77 : Real)) := by
      simp [DigitWindowState]
      ring
    _ <= 20000 *
        (((10 ^ (steps + 4) : Nat) : Real) ^ (27 / 77 : Real)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      norm_num [pow_add, Nat.cast_pow]

theorem firstMomentContinuousCellSum_le
    (digit : Fin 10) (length : Nat) {offset : Real}
    (hoffset : offset ∈ Set.Icc (0 : Real) 1) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitudeAt digit length
        (((frequency.val : Real) + offset) / (10 : Real) ^ length)) <=
      20000 * (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
  by_cases hlength : 4 <= length
  · obtain ⟨steps, hsteps⟩ := Nat.exists_eq_add_of_le hlength
    have hlengthEq : length = steps + 4 := by omega
    clear hsteps
    subst length
    exact firstMomentContinuousCellSum_add_four_le digit steps hoffset
  · have hlengthLt : length < 4 := Nat.lt_of_not_ge hlength
    have hsum :
        (∑ frequency : Fin (10 ^ length),
          normalizedPaddedDigitFourierMagnitudeAt digit length
            (((frequency.val : Real) + offset) / (10 : Real) ^ length)) <=
          ∑ _frequency : Fin (10 ^ length), (1 : Real) := by
      apply Finset.sum_le_sum
      intro frequency _
      exact normalizedPaddedDigitFourierMagnitudeAt_le_one digit length _
    have hcardBound : ((10 ^ length : Nat) : Real) <= 20000 := by
      interval_cases length <;> norm_num
    have hrpow :
        1 <= (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
      apply Real.one_le_rpow
      · exact_mod_cast Nat.one_le_pow length 10 (by norm_num)
      · norm_num
    calc
      (∑ frequency : Fin (10 ^ length),
          normalizedPaddedDigitFourierMagnitudeAt digit length
            (((frequency.val : Real) + offset) / (10 : Real) ^ length)) <=
          ∑ _frequency : Fin (10 ^ length), (1 : Real) := hsum
      _ = ((10 ^ length : Nat) : Real) := by simp
      _ <= 20000 := hcardBound
      _ <= 20000 * (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hrpow (by norm_num : (0 : Real) <= 20000)

end PrimesRestrictedDigits
