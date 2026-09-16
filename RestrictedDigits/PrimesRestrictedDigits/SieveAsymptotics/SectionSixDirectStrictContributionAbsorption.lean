import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearGeometryThreshold
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearDiscrepancyAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectCandidateContribution
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixStrictOutsideNearAbsorption

/-!
# Direct strict contribution absorption

The two direct near discrepancies and their already-controlled outside-near tails are
reassembled into the exact once-dilated strict contribution.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 300000 in
/-- The algebraic sum of the two direct strict range contributions is
eventually absorbed into any positive logarithmic budget. -/
theorem exists_sectionSixDirectTwoBandRangeStrictContribution_budget_upper
    (delta budget : Real) (hdelta : 0 < delta) (hbudget : 0 < budget)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (ell : Nat) (region : Set (Fin ell -> Real))
    (presentation : TypeIIAffineMixedPresentation region) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let strictContribution : SectionSixDirectBand -> Real := fun band =>
          sectionSixDirectRangeStrictContribution digit epsilon delta ell
            length region band
        abs (strictContribution .first + strictContribution .second) <=
          budget * (A.card : Real) / Real.log X := by
  obtain ⟨geometryLength, hgeometryLength, hgeometryAt⟩ :=
    exists_sectionSixDirectNearGeometryThreshold delta epsilon hdelta hepsilon
      ell
  obtain ⟨nearLength, hnearLength, hnearAt⟩ :=
    exists_sectionSixDirectTwoBandNearDiscrepancy_budget_upper
      delta (budget / 2) hdelta (by positivity) epsilon hepsilon ell region
        presentation
  obtain ⟨outsideLength, houtsideLength, houtsideAt⟩ :=
    exists_sectionSixDirectStrictOutsideNearAbsorptionThreshold epsilon ell
      (budget / 4) (by positivity) delta hdelta hdeltaGapStrict
  let length0 : Nat := max geometryLength (max nearLength outsideLength)
  have hlength0 : 1 <= length0 :=
    hgeometryLength.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  have hgeometryLengthAt : geometryLength <= length := by
    have : geometryLength <= length0 := by dsimp only [length0]; omega
    exact this.trans hlength
  have hnearLengthAt : nearLength <= length := by
    have : nearLength <= length0 := by dsimp only [length0]; omega
    exact this.trans hlength
  have houtsideLengthAt : outsideLength <= length := by
    have : outsideLength <= length0 := by dsimp only [length0]; omega
    exact this.trans hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let nearCarrier : Finset Nat := typeIINearXCarrier XNat rho
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let mass : Real := (A.card : Real) / Real.log X
  let nearDiscrepancy : SectionSixDirectBand -> Real := fun band =>
    ((sectionSixDirectNearCandidates epsilon delta rho ell region length band
      A).card : Real) -
      lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell region
        length band B).card : Real)
  let outsideCount : SectionSixDirectBand -> Finset Nat -> Real :=
    fun band C =>
      ((sectionSixDirectOutsideNearCandidates epsilon delta rho ell region
        length band C).card : Real)
  let outsideDiscrepancy : SectionSixDirectBand -> Real := fun band =>
    outsideCount band A - lambda * outsideCount band B
  let representedTail : SectionSixDirectBand -> Finset Nat -> Real :=
    fun band C =>
      ∑ index ∈ sectionSixDirectRepeatedIndices epsilon delta ell region length
          band,
        ((sectionSixDirectStrictRepresentedCarrier C index \
          nearCarrier).card : Real)
  let strictContribution : SectionSixDirectBand -> Real := fun band =>
    sectionSixDirectRangeStrictContribution digit epsilon delta ell length
      region band
  have hgeometry := hgeometryAt length hgeometryLengthAt
  dsimp only at hgeometry
  have hnearRaw := hnearAt length hnearLengthAt digit hepsilonSmall
    hdeltaGapStrict hgeometry.1 hgeometry.2.1 hgeometry.2.2
  have hnear :
      abs (nearDiscrepancy .first + nearDiscrepancy .second) <=
        budget / 2 * mass := by
    have hnear' :
        abs (nearDiscrepancy .first + nearDiscrepancy .second) <=
          budget / 2 * (A.card : Real) / Real.log X := by
      simpa only [nearDiscrepancy, XNat, X, rho, A, B, lambda] using hnearRaw
    calc
      abs (nearDiscrepancy .first + nearDiscrepancy .second) <=
          budget / 2 * (A.card : Real) / Real.log X := hnear'
      _ = budget / 2 * mass := by
        dsimp only [mass]
        ring
  have houtsideCharge (band : SectionSixDirectBand) :
      representedTail band A + lambda * representedTail band B <=
        budget / 4 * mass := by
    have hraw := houtsideAt length houtsideLengthAt digit region band
    have hraw' :
        representedTail band A + lambda * representedTail band B <=
          budget / 4 * (A.card : Real) / Real.log X := by
      simpa only [representedTail, XNat, X, rho, A, B, nearCarrier, lambda]
        using hraw
    calc
      representedTail band A + lambda * representedTail band B <=
          budget / 4 * (A.card : Real) / Real.log X := hraw'
      _ = budget / 4 * mass := by
        dsimp only [mass]
        ring
  have houtsideCount (band : SectionSixDirectBand) (C : Finset Nat) :
      outsideCount band C = representedTail band C := by
    dsimp only [outsideCount, representedTail, nearCarrier, XNat, rho]
    rw [card_sectionSixDirectOutsideNearCandidates_eq_sum_represented_sdiff]
    simp only [Nat.cast_sum]
  have hXPos : 0 < X := by
    dsimp only [X, XNat]
    positivity
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact div_nonneg
      (mul_nonneg (restrictedDigitDensity_nonneg digit)
        (Nat.cast_nonneg A.card)) hXPos.le
  have hrepresentedTail (band : SectionSixDirectBand) (C : Finset Nat) :
      0 <= representedTail band C := by
    dsimp only [representedTail]
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have houtside (band : SectionSixDirectBand) :
      abs (outsideDiscrepancy band) <= budget / 4 * mass := by
    dsimp only [outsideDiscrepancy]
    rw [houtsideCount band A, houtsideCount band B]
    calc
      abs (representedTail band A - lambda * representedTail band B) <=
          abs (representedTail band A) +
            abs (lambda * representedTail band B) := abs_sub _ _
      _ = representedTail band A + lambda * representedTail band B := by
        rw [abs_of_nonneg (hrepresentedTail band A),
          abs_of_nonneg (mul_nonneg hlambda (hrepresentedTail band B))]
      _ <= budget / 4 * mass := houtsideCharge band
  have houtsideBoth :
      abs (outsideDiscrepancy .first + outsideDiscrepancy .second) <=
        budget / 2 * mass := by
    calc
      abs (outsideDiscrepancy .first + outsideDiscrepancy .second) <=
          abs (outsideDiscrepancy .first) +
            abs (outsideDiscrepancy .second) := abs_add_le _ _
      _ <= budget / 4 * mass + budget / 4 * mass :=
        add_le_add (houtside .first) (houtside .second)
      _ = budget / 2 * mass := by ring
  have hsplit (band : SectionSixDirectBand) :
      strictContribution band =
        nearDiscrepancy band + outsideDiscrepancy band := by
    have h :=
      sectionSixDirectRangeStrictContribution_eq_near_add_outsideDiscrepancy
        digit epsilon delta rho ell length region band
    simpa only [strictContribution, nearDiscrepancy, outsideDiscrepancy,
      outsideCount, XNat, X, rho, A, B, lambda, div_eq_mul_inv, mul_assoc]
      using h
  calc
    abs (strictContribution .first + strictContribution .second) =
        abs ((nearDiscrepancy .first + nearDiscrepancy .second) +
          (outsideDiscrepancy .first + outsideDiscrepancy .second)) := by
      rw [hsplit .first, hsplit .second]
      congr 1
      ring
    _ <= abs (nearDiscrepancy .first + nearDiscrepancy .second) +
        abs (outsideDiscrepancy .first + outsideDiscrepancy .second) :=
      abs_add_le _ _
    _ <= budget / 2 * mass + budget / 2 * mass :=
      add_le_add hnear houtsideBoth
    _ = budget * (A.card : Real) / Real.log X := by
      dsimp only [mass]
      ring

end

end PrimesRestrictedDigits
