import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVNearSignedCandidateSumAbsorption

/-!
# Two-band terminal-V near signed-candidate absorption

The low and high terminal state bands share one eventual threshold and split an arbitrary
positive budget.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Both terminal state-band near signed sums are eventually absorbed into an
arbitrary positive multiple of the restricted logarithmic scale. -/
theorem exists_sectionSixTerminalVTwoBandNearSignedCandidateSum_budget_upper
    (delta budget : Real) (hdelta : 0 < delta) (hbudget : 0 < budget)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (ell : Nat) (region : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation region) :
    ∃ (length0 : Nat) (hlength0 : 1 <= length0),
      ∀ (length : Nat) (hlength : length0 <= length),
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let rho : Real := majorArcM2LogLogDelta XNat
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let near : Finset Nat := typeIINearXCarrier XNat rho
        let hlengthOne : 1 <= length := hlength0.trans hlength
        ∀ (hepsilonSmall : epsilon <= 1 / 64)
          (hdeltaGapStrict : delta < sectionSixThetaGap epsilon),
        2 * rho <= delta / 2 ->
        rho ^ 2 + ((Nat.ceil (2 / delta) : Real) * rho) <= epsilon ->
        abs (
          sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
              hepsilon hepsilonSmall hlengthOne hdeltaGapStrict.le .low
                (X ^ delta) near +
            sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
              hepsilon hepsilonSmall hlengthOne hdeltaGapStrict.le .high
                (X ^ delta) near) <=
          budget * (A.card : Real) / Real.log X := by
  obtain ⟨lowLength, hlowLength, hlowAt⟩ :=
    exists_sectionSixTerminalVNearSignedCandidateSum_budget_upper delta
      (budget / 2) hdelta (by positivity) epsilon hepsilon ell region
        sourcePresentation .low
  obtain ⟨highLength, hhighLength, hhighAt⟩ :=
    exists_sectionSixTerminalVNearSignedCandidateSum_budget_upper delta
      (budget / 2) hdelta (by positivity) epsilon hepsilon ell region
        sourcePresentation .high
  let length0 : Nat := max lowLength highLength
  have hlength0 : 1 <= length0 :=
    hlowLength.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hmarginWidth hglobalWidth
  have hlowLengthAt : lowLength <= length :=
    (Nat.le_max_left lowLength highLength).trans hlength
  have hhighLengthAt : highLength <= length :=
    (Nat.le_max_right lowLength highLength).trans hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let near : Finset Nat := typeIINearXCarrier XNat rho
  have hlengthOne : 1 <= length := hlength0.trans hlength
  let nearSum := fun band : SectionSixStateBand =>
    sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
      hepsilon hepsilonSmall hlengthOne hdeltaGapStrict.le band
        (X ^ delta) near
  have hlow : abs (nearSum .low) <=
      budget / 2 * (A.card : Real) / Real.log X := by
    have h := hlowAt length hlowLengthAt digit hepsilonSmall hdeltaGapStrict
      hmarginWidth hglobalWidth
    simpa only [nearSum, XNat, X, rho, A, near] using h
  have hhigh : abs (nearSum .high) <=
      budget / 2 * (A.card : Real) / Real.log X := by
    have h := hhighAt length hhighLengthAt digit hepsilonSmall hdeltaGapStrict
      hmarginWidth hglobalWidth
    simpa only [nearSum, XNat, X, rho, A, near] using h
  calc
    abs (nearSum .low + nearSum .high) <=
        abs (nearSum .low) + abs (nearSum .high) := abs_add_le _ _
    _ <= budget / 2 * (A.card : Real) / Real.log X +
        budget / 2 * (A.card : Real) / Real.log X := add_le_add hlow hhigh
    _ = budget * (A.card : Real) / Real.log X := by ring

end

end PrimesRestrictedDigits
