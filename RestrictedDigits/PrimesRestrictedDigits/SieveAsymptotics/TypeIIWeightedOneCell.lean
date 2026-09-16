import PrimesRestrictedDigits.SieveAsymptotics.TypeIIFrequencyPartition
import PrimesRestrictedDigits.ExceptionalMinorArcs.PropositionNineThree

/-!
# Weighted one-cell Type II error

This combines the exact decimal-grid priority partition with the three terminal arc estimates.
It is the fixed one-logarithm consequence of the one-cube assembly on p. 168 of
`MAYNARD-PRD-PUBLISHED`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 1200000 in
theorem exists_typeIIWeightedOneCellLogError
    (eta : Real) (heta : 0 < eta) :
    ∀ mu : Real, 0 < mu ->
      ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
      ∀ (digit : Fin 10) (k : Nat) (a : Fin k -> Real)
        (I : Finset (Fin k)),
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let delta : Real := majorArcM2LogLogDelta XNat
        (∀ i, eta / 2 <= a i) ->
        (∑ i, a i) < 1 - eta / 2 ->
        (((k + 1 : Nat) : Real) <= 2 / eta) ->
        ((∑ i ∈ I, a i) ∈
              Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
          (∑ i ∈ I, a i) ∈
              Set.Icc (23 / 40 + mu) (16 / 25 - mu)) ->
        ‖(∑ m ∈ paddedRestrictedNumbers digit length,
              (majorArcRegionWeightAtProduct
                XNat a delta eta m : Complex)) -
            (restrictedDigitDensity digit : Complex) *
              ((paddedRestrictedNumbers digit length).card : Complex) *
              majorArcRegionTotalWeight XNat a delta eta /
                (XNat : Complex)‖ <=
          229 *
            ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X := by
  obtain ⟨D, hD, hExceptional⟩ :=
    exists_exceptionalMinorArcPropositionNatThreshold 1 eta heta
  obtain ⟨majorLength, hMajor⟩ :=
    exists_majorArcRawRegionContributionLogScaleThreshold
      (eta := eta) D hD heta
  obtain ⟨genericLength, hGeneric⟩ :=
    exists_genericMinorArcThreshold eta heta
  obtain ⟨powerLength, hPower⟩ :=
    exists_genericPowerSaving_logThreshold 1
  intro mu hmu
  obtain ⟨exceptionalLength, hExceptionalAt⟩ := hExceptional mu hmu
  let length0 := max 1
    (max majorLength (max genericLength (max powerLength exceptionalLength)))
  refine ⟨length0, by simp [length0], ?_⟩
  intro length hlength digit k a I
  have hlengths :
      1 <= length ∧ majorLength <= length ∧ genericLength <= length ∧
        powerLength <= length ∧ exceptionalLength <= length := by
    simpa only [length0, max_le_iff] using hlength
  rcases hlengths with
    ⟨hlengthOne, hmajorLength, hgenericLength, hpowerLength,
      hexceptionalLength⟩
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let delta : Real := majorArcM2LogLogDelta XNat
  dsimp only
  intro hanchors hsum hell hconvenient
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let E : Finset (Fin XNat) := genericExceptionalFrequencies digit length
  let w : Nat -> Complex := fun n =>
    (majorArcRegionWeightAtProduct XNat a delta eta n : Complex)
  let term : Fin XNat -> Complex := fun h =>
    typeIIFrequencyFourierTerm digit length w h
  let major : Complex := majorArcRawContribution XNat
    (Real.log X ^ D) A (Finset.range XNat) w
  let high : Complex :=
    (∑ h ∈ typeIIFrequencyHighFrequencies digit length D, term h) /
      (XNat : Complex)
  let ordinary : Complex :=
    (∑ h ∈ typeIIFrequencyOrdinaryFrequencies digit length D, term h) /
      (XNat : Complex)
  let mainTerm : Complex :=
    (restrictedDigitDensity digit : Complex) * (A.card : Complex) *
      majorArcRegionTotalWeight XNat a delta eta / (XNat : Complex)
  let weightedCount : Complex := ∑ m ∈ A, w m
  let card : Real := (A.card : Real)
  let logX : Real := Real.log X
  have hXNatPos : 0 < XNat := by
    dsimp only [XNat]
    positivity
  have hXPos : 0 < X := by
    dsimp only [X]
    exact_mod_cast hXNatPos
  have hlogOne : 1 <= logX := by
    dsimp only [logX, X, XNat]
    exact one_le_log_powTen_of_pos (Nat.zero_lt_of_lt hlengthOne)
  have hlogPos : 0 < logX := zero_lt_one.trans_le hlogOne
  have hgenericAt := hGeneric length hgenericLength digit (k + 1)
    (by omega) hell (majorArcLogRegion a delta eta)
  have hcardE : (E.card : Real) <= X ^ (23 / 40 : Real) := by
    simpa only [E, X, XNat] using hgenericAt.1
  have hmajorRaw :
      ‖major - mainTerm‖ <= 225 * card / logX ^ D := by
    simpa only [major, mainTerm, card, logX, A, w, X, XNat, delta] using
      hMajor length hmajorLength k digit a hanchors hsum hell
  have hDOne : 1 <= D := hD
  have hlogPower : logX <= logX ^ D := by
    calc
      logX = logX ^ 1 := by ring
      _ <= logX ^ D := pow_le_pow_right₀ hlogOne hDOne
  have hmajorBound :
      ‖major - mainTerm‖ <= 225 * card / logX :=
    hmajorRaw.trans <| div_le_div_of_nonneg_left
      (by positivity) hlogPos hlogPower
  have hhighRaw := hExceptionalAt length hexceptionalLength digit k a I E
    hanchors hsum hell hconvenient hcardE
  have hhighNorm :
      ‖∑ h ∈ typeIIFrequencyHighFrequencies digit length D, term h‖ / X <=
        3 * card / logX := by
    rw [typeIIFrequencyHighFrequencies_eq_exceptionalMinorArcFrequencies]
    simpa only [term, typeIIFrequencyFourierTerm, w, E, card, logX,
      X, XNat, delta, pow_one] using hhighRaw
  have hhighBound : ‖high‖ <= 3 * card / logX := by
    dsimp only [high]
    rw [norm_div, norm_natCast]
    simpa only [X] using hhighNorm
  have hgenericNorm :
      (∑ h ∈ genericOrdinaryFrequencies digit length, ‖term h‖) / X <=
        card / X ^ (127 / 21338240 : Real) := by
    simpa only [term, typeIIFrequencyFourierTerm, w, card, X, XNat,
      delta, normalizedLogRegionWeight_majorArcLogRegion] using hgenericAt.2
  have hordinaryNormSum :
      ‖∑ h ∈ typeIIFrequencyOrdinaryFrequencies digit length D, term h‖ <=
        ∑ h ∈ genericOrdinaryFrequencies digit length, ‖term h‖ := by
    calc
      ‖∑ h ∈ typeIIFrequencyOrdinaryFrequencies digit length D, term h‖ <=
          ∑ h ∈ typeIIFrequencyOrdinaryFrequencies digit length D,
            ‖term h‖ := norm_sum_le _ _
      _ <= ∑ h ∈ genericOrdinaryFrequencies digit length, ‖term h‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (typeIIFrequencyOrdinaryFrequencies_subset_genericOrdinary
            digit length D)
          (fun h _ _ => norm_nonneg (term h))
  have hordinaryPower :
      ‖∑ h ∈ typeIIFrequencyOrdinaryFrequencies digit length D, term h‖ / X <=
        card / X ^ (127 / 21338240 : Real) := by
    exact (div_le_div_of_nonneg_right hordinaryNormSum hXPos.le).trans
      hgenericNorm
  have hpowerAt :
      1 / X ^ (127 / 21338240 : Real) <= 1 / logX := by
    simpa only [X, XNat, logX, pow_one] using
      hPower length hpowerLength
  have hordinaryNorm :
      ‖∑ h ∈ typeIIFrequencyOrdinaryFrequencies digit length D, term h‖ / X <=
        card / logX := by
    apply hordinaryPower.trans
    calc
      card / X ^ (127 / 21338240 : Real) =
          card * (1 / X ^ (127 / 21338240 : Real)) := by ring
      _ <= card * (1 / logX) :=
        mul_le_mul_of_nonneg_left hpowerAt (by positivity)
      _ = card / logX := by ring
  have hordinaryBound : ‖ordinary‖ <= card / logX := by
    dsimp only [ordinary]
    rw [norm_div, norm_natCast]
    simpa only [X] using hordinaryNorm
  have hpartition :=
    sum_typeIIFrequencyMajor_add_high_add_ordinary digit length D term
  have hmajorIdentity :=
    typeIIFrequencyMajorContribution_eq_majorArcRawContribution
      digit length D w
  have hdecomp : weightedCount = major + high + ordinary := by
    calc
      weightedCount =
          (∑ h : Fin XNat, term h) / (XNat : Complex) := by
        simpa only [weightedCount, A, w, term, typeIIFrequencyFourierTerm,
          XNat] using
          sum_paddedRestrictedNumbers_weight_eq_decimalGrid digit length w
      _ = ((∑ h ∈ typeIIFrequencyMajorFrequencies length D, term h) +
            ((∑ h ∈ typeIIFrequencyHighFrequencies digit length D,
                term h) +
              ∑ h ∈ typeIIFrequencyOrdinaryFrequencies digit length D,
                term h)) / (XNat : Complex) := by
        rw [hpartition]
      _ = typeIIFrequencyMajorContribution digit length D w +
            high + ordinary := by
        dsimp only [typeIIFrequencyMajorContribution, high, ordinary, term]
        ring
      _ = major + high + ordinary := by
        rw [hmajorIdentity]
  have herror : weightedCount - mainTerm =
      (major - mainTerm) + high + ordinary := by
    rw [hdecomp]
    ring
  change ‖weightedCount - mainTerm‖ <= 229 * card / logX
  rw [herror]
  calc
    ‖(major - mainTerm) + high + ordinary‖ <=
        ‖(major - mainTerm) + high‖ + ‖ordinary‖ := norm_add_le _ _
    _ <= (‖major - mainTerm‖ + ‖high‖) + ‖ordinary‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ <= (225 * card / logX + 3 * card / logX) + card / logX :=
      add_le_add (add_le_add hmajorBound hhighBound) hordinaryBound
    _ = 229 * card / logX := by ring

end

end PrimesRestrictedDigits
