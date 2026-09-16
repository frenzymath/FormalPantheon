import PrimesRestrictedDigits.ExceptionalMinorArcs.ExceptionalFrequencyPartition

/-!
# Ordinary/high exceptional-minor join

This combines the generic ordinary estimate with the high-frequency theorem for an arbitrary
finite source set and a general region width.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Before specializing the region width, the ordinary/high partition already
gives the explicit coefficient-three logarithmic estimate. -/
theorem exists_norm_splitPrimeExceptionalLogSaving
    (A : Nat) (eta : Real) (heta : 0 < eta) :
    ∃ D length0 : Nat, 0 < D ∧
      ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (k : Nat) (a : Fin k → Real)
        (delta mu : Real) (I : Finset (Fin k))
        (E : Finset (Fin (10 ^ length))),
        let X : Real := ((10 ^ length : Nat) : Real)
        (E.card : Real) ≤ X ^ (23 / 40 : Real) →
        ((k + 1 : Nat) : Real) ≤ 2 / eta →
        0 ≤ delta →
        ((k + 1 : Nat) : Real) * delta +
            1 / (length : Real) ≤ mu →
        ((∑ i ∈ I, a i) ∈
            Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
          (∑ i ∈ I, a i) ∈
            Set.Icc (23 / 40 + mu) (16 / 25 - mu)) →
        ‖∑ h ∈ exceptionalMinorArcFrequencies length D E,
            paddedDigitFourierSum digit length h.val *
              majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                (fun r => (majorArcRegionWeightAtProduct
                  (10 ^ length) a delta eta r : Complex))
                (-((h.val : Real) / X))‖ / X ≤
          3 * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X ^ A := by
  obtain ⟨D, highLength, hD, hhigh⟩ :=
    exists_norm_splitPrimeExceptionalHighLogSaving A eta heta
  obtain ⟨genericLength, hgeneric⟩ :=
    exists_genericMinorArcThreshold eta heta
  obtain ⟨absorbLength, habsorb⟩ :=
    exists_genericPowerSaving_logThreshold A
  refine ⟨D, max highLength (max genericLength absorbLength), hD, ?_⟩
  intro length hlength digit k a delta mu I E
  dsimp only
  intro _hcard hell hdelta hmargin hconvenient
  have hhighLength : highLength ≤ length :=
    (le_max_left highLength (max genericLength absorbLength)).trans hlength
  have hgenericLength : genericLength ≤ length :=
    (le_max_left genericLength absorbLength).trans
      ((le_max_right highLength (max genericLength absorbLength)).trans hlength)
  have habsorbLength : absorbLength ≤ length :=
    (le_max_right genericLength absorbLength).trans
      ((le_max_right highLength (max genericLength absorbLength)).trans hlength)
  let X : Real := ((10 ^ length : Nat) : Real)
  let high := exceptionalMinorArcHighFrequencies digit length D E
  let ordinary := exceptionalMinorArcOrdinaryFrequencies digit length D E
  let term : Fin (10 ^ length) → Complex := fun h =>
    paddedDigitFourierSum digit length h.val *
      majorArcWeightedPhaseSum (Finset.range (10 ^ length))
        (fun r => (majorArcRegionWeightAtProduct
          (10 ^ length) a delta eta r : Complex))
        (-((h.val : Real) / X))
  have hXPos : 0 < X := by dsimp only [X]; positivity
  have hminor : ∀ h ∈ high,
      h.val ∉ majorArcRawFrequencies (10 ^ length)
        (Real.log X ^ D) := by
    intro h hh
    simpa only [X, high] using
      mem_exceptionalMinorArcHighFrequencies_not_major hh
  have hhighSubset : high ⊆ genericExceptionalFrequencies digit length := by
    simpa only [high] using
      exceptionalMinorArcHighFrequencies_subset_genericExceptional
        digit length D E
  have hhighBound :
      ‖∑ h ∈ high, term h‖ / X ≤
        2 * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X ^ A := by
    have hbound := hhigh length hhighLength digit k a delta mu I high hell
      hminor hdelta hmargin hconvenient hhighSubset
    simpa only [X, term, card_paddedRestrictedNumbers, Nat.cast_pow,
      Nat.cast_ofNat] using hbound
  have hgenericAt := hgeneric length hgenericLength digit (k + 1)
    (by omega) hell (majorArcLogRegion a delta eta)
  have hordinaryFull :
      (∑ h ∈ genericOrdinaryFrequencies digit length, ‖term h‖) / X ≤
        ((paddedRestrictedNumbers digit length).card : Real) /
          (((10 ^ length : Nat) : Real) ^
            (127 / 21338240 : Real)) := by
    simpa only [X, term, normalizedLogRegionWeight_majorArcLogRegion] using
      hgenericAt.2
  have hpowerAbsorb := habsorb length habsorbLength
  have hordinaryBound :
      ‖∑ h ∈ ordinary, term h‖ / X ≤
        ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X ^ A := by
    calc
      ‖∑ h ∈ ordinary, term h‖ / X ≤
          (∑ h ∈ genericOrdinaryFrequencies digit length, ‖term h‖) / X :=
        div_le_div_of_nonneg_right
          (by simpa only [ordinary] using
            norm_sum_exceptionalMinorArcOrdinary_le digit length D E term)
          hXPos.le
      _ ≤ ((paddedRestrictedNumbers digit length).card : Real) /
          (((10 ^ length : Nat) : Real) ^
            (127 / 21338240 : Real)) := hordinaryFull
      _ ≤ ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X ^ A := by
        calc
          ((paddedRestrictedNumbers digit length).card : Real) /
              (((10 ^ length : Nat) : Real) ^
                (127 / 21338240 : Real)) =
              ((paddedRestrictedNumbers digit length).card : Real) *
                (1 / (((10 ^ length : Nat) : Real) ^
                  (127 / 21338240 : Real))) := by ring
          _ ≤ ((paddedRestrictedNumbers digit length).card : Real) *
                (1 / Real.log (((10 ^ length : Nat) : Real)) ^ A) :=
            mul_le_mul_of_nonneg_left hpowerAbsorb (by positivity)
          _ = ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log X ^ A := by
            dsimp only [X]
            ring
  have hsplit :
      (∑ h ∈ high, term h) + (∑ h ∈ ordinary, term h) =
        ∑ h ∈ exceptionalMinorArcFrequencies length D E, term h := by
    simpa only [high, ordinary] using
      sum_exceptionalMinorArcHigh_add_ordinary digit length D E term
  change ‖∑ h ∈ exceptionalMinorArcFrequencies length D E, term h‖ / X ≤ _
  rw [← hsplit]
  calc
    ‖(∑ h ∈ high, term h) + ∑ h ∈ ordinary, term h‖ / X ≤
        (‖∑ h ∈ high, term h‖ + ‖∑ h ∈ ordinary, term h‖) / X :=
      div_le_div_of_nonneg_right (norm_add_le _ _) hXPos.le
    _ = ‖∑ h ∈ high, term h‖ / X +
        ‖∑ h ∈ ordinary, term h‖ / X := by ring
    _ ≤ 2 * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X ^ A +
        ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X ^ A :=
      add_le_add hhighBound hordinaryBound
    _ = 3 * ((paddedRestrictedNumbers digit length).card : Real) /
        Real.log X ^ A := by ring

end

end PrimesRestrictedDigits
