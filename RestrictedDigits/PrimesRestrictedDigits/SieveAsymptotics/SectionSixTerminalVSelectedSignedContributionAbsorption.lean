import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearGeometryThreshold
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVTwoBandNearSignedCandidateSumAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVOutsideSignedContribution

/-!
# Terminal-V selected signed-contribution absorption

The two-band near and outside candidate estimates are reassembled into the exact selected
terminal-V recurrence contribution. See `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 136--145, and
Lemma 7.3, pp. 149--157.
-/

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 400000 in
/-- The low-plus-high selected terminal-V recurrence contribution is
eventually absorbed into any positive multiple of the restricted logarithmic
scale. -/
theorem
    exists_sectionSixTerminalVTwoBandSelectedSignedContribution_budget_upper
    (delta budget : Real) (hdelta : 0 < delta) (hbudget : 0 < budget)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (ell : Nat) (region : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation region) :
    ∃ (length0 : Nat) (hlength0 : 1 <= length0),
      ∀ (length : Nat) (hlength : length0 <= length),
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let hlengthOne : 1 <= length := hlength0.trans hlength
        let selected : SectionSixStateBand -> Real := fun band =>
          sectionSixSourceBandSelectedSignedContribution digit region hepsilon
            hepsilonSmall hlengthOne hdeltaGapStrict.le band
              sectionSixTerminalVPredicate
        abs (selected .low + selected .high) <=
          budget * (A.card : Real) / Real.log X := by
  obtain ⟨geometryLength, hgeometryLength, hgeometryAt⟩ :=
    exists_sectionSixDirectNearGeometryThreshold delta epsilon hdelta hepsilon
      ell
  obtain ⟨nearLength, hnearLength, hnearAt⟩ :=
    exists_sectionSixTerminalVTwoBandNearSignedCandidateSum_budget_upper
      delta (budget / 2) hdelta (by positivity) epsilon hepsilon ell region
        sourcePresentation
  obtain ⟨outsideLength, houtsideLength, houtsideAt⟩ :=
    exists_sectionSixTerminalVTwoBandOutsideSignedContribution_budget_upper
      epsilon hepsilon hepsilonSmall ell (budget / 2) (by positivity) delta
        hdelta hdeltaGapStrict.le
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
  let M : Nat := Nat.ceil (2 / delta)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let near : Finset Nat := typeIINearXCarrier XNat rho
  have hlengthOne : 1 <= length := hlength0.trans hlength
  let selected : SectionSixStateBand -> Real := fun band =>
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
      hepsilonSmall hlengthOne hdeltaGapStrict.le band
        sectionSixTerminalVPredicate
  let nearSum : SectionSixStateBand -> Real := fun band =>
    sectionSixSourceBandTerminalVNearSignedCandidateSum digit region hepsilon
      hepsilonSmall hlengthOne hdeltaGapStrict.le band (X ^ delta) near
  let outsideSum : SectionSixStateBand -> Real := fun band =>
    sectionSixSourceBandTerminalVOutsideSignedCandidateSum digit region
      hepsilon hepsilonSmall hlengthOne hdeltaGapStrict.le band (X ^ delta)
        near
  let mass : Real := (A.card : Real) / Real.log X
  have hgeometry := hgeometryAt length hgeometryLengthAt
  dsimp only at hgeometry
  have hrho : 0 < rho := by
    simpa only [rho, XNat] using
      (majorArcM2LogLogDelta_powTen_pos hlengthOne)
  have hMle : (M : Real) <= (ell + M : Nat) := by
    exact_mod_cast Nat.le_add_left M ell
  have hglobal : rho ^ 2 + (M : Real) * rho <= epsilon := by
    have hlinear : (M : Real) * rho <= ((ell + M : Nat) : Real) * rho :=
      mul_le_mul_of_nonneg_right hMle hrho.le
    calc
      rho ^ 2 + (M : Real) * rho <=
          rho ^ 2 + ((ell + M : Nat) : Real) * rho :=
        add_le_add le_rfl hlinear
      _ <= epsilon := by
        simpa only [rho, XNat, M] using hgeometry.2.2
  have hnearRaw := hnearAt length hnearLengthAt digit hepsilonSmall
    hdeltaGapStrict hgeometry.2.1 hglobal
  have hnear : abs (nearSum .low + nearSum .high) <=
      budget / 2 * mass := by
    have hnear' : abs (nearSum .low + nearSum .high) <=
        budget / 2 * (A.card : Real) / Real.log X := by
      simpa only [nearSum, XNat, X, rho, A, near, M] using hnearRaw
    calc
      abs (nearSum .low + nearSum .high) <=
          budget / 2 * (A.card : Real) / Real.log X := hnear'
      _ = budget / 2 * mass := by
        dsimp only [mass]
        ring
  have houtsideRaw := houtsideAt region length houtsideLengthAt digit
  have houtside : abs (outsideSum .low + outsideSum .high) <=
      budget / 2 * mass := by
    have houtside' : abs (outsideSum .low + outsideSum .high) <=
        budget / 2 * (A.card : Real) / Real.log X := by
      simpa only [outsideSum, XNat, X, rho, A, near] using houtsideRaw
    calc
      abs (outsideSum .low + outsideSum .high) <=
          budget / 2 * (A.card : Real) / Real.log X := houtside'
      _ = budget / 2 * mass := by
        dsimp only [mass]
        ring
  have hsplit (band : SectionSixStateBand) :
      selected band = nearSum band + outsideSum band := by
    have h :=
      sectionSixSourceBandSelectedSignedContribution_V_eq_near_add_outside
        digit region hepsilon hepsilonSmall hlengthOne hdeltaGapStrict.le band
          near
    simpa only [selected, nearSum, outsideSum, XNat, X, rho, near] using h
  calc
    abs (selected .low + selected .high) =
        abs ((nearSum .low + nearSum .high) +
          (outsideSum .low + outsideSum .high)) := by
      rw [hsplit .low, hsplit .high]
      congr 1
      ring
    _ <= abs (nearSum .low + nearSum .high) +
        abs (outsideSum .low + outsideSum .high) := abs_add_le _ _
    _ <= budget / 2 * mass + budget / 2 * mass := add_le_add hnear houtside
    _ = budget * (A.card : Real) / Real.log X := by
      dsimp only [mass]
      ring

end

end PrimesRestrictedDigits
