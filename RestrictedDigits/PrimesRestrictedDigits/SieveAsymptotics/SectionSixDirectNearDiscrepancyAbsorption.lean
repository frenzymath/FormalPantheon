import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectFormalSignedTargetOccurrenceAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectTwoBandFormalTargetAbsorption
/-! # SectionSixDirectNearDiscrepancyAbsorption -/

namespace PrimesRestrictedDigits

noncomputable section

/-!
# Section Six Direct Near-Discrepancy Absorption

This file combines the two-band formal signed-target estimate with the already controlled
formal-target approximation error. It is the final target-side estimate before the direct
strict contribution is reassembled with the outside-near error.
-/

set_option maxHeartbeats 2400000 in
theorem exists_sectionSixDirectTwoBandNearDiscrepancy_budget_upper
    (delta budget : Real) (hdelta : 0 < delta) (hbudget : 0 < budget)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (ell : Nat) (region : Set (Fin ell -> Real))
    (presentation : TypeIIAffineMixedPresentation region) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let rho : Real := majorArcM2LogLogDelta XNat
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let B : Finset Nat := maynardAmbientCarrier X
        let M : Nat := Nat.ceil (2 / delta)
        let lambda : Real :=
          (restrictedDigitDensity digit : Real) * (A.card : Real) / X
        let nearDiscrepancy : SectionSixDirectBand -> Real := fun band =>
          ((sectionSixDirectNearCandidates epsilon delta rho ell region length
            band A).card : Real) -
            lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell
              region length band B).card : Real)
        epsilon <= 1 / 64 ->
        delta < sectionSixThetaGap epsilon ->
        rho ^ 2 < delta ->
        2 * rho <= delta / 2 ->
        rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon ->
        abs (nearDiscrepancy .first + nearDiscrepancy .second) <=
          budget * (A.card : Real) / Real.log X := by
  obtain ⟨lengthTarget, hlengthTarget, hTarget⟩ :=
    exists_sectionSixDirectTwoBandFormalSignedWeakPieceTargetOccurrenceDiscrepancy_budget_upper
      delta (budget / 2) hdelta (by positivity) epsilon hepsilon ell region
        presentation
  obtain ⟨lengthError, hlengthError, hError⟩ :=
    exists_sectionSixDirectTwoBandFormalSignedWeakPieceTargetError_budget_upper
      delta (budget / 2) hdelta (by positivity) epsilon hepsilon ell region
        presentation
  let length0 : Nat := max lengthTarget lengthError
  have hlength0 : 1 <= length0 :=
    hlengthTarget.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hlengthTargetAt : lengthTarget <= length := by
    have : lengthTarget <= length0 := by dsimp only [length0]; omega
    exact this.trans hlength
  have hlengthErrorAt : lengthError <= length := by
    have : lengthError <= length0 := by dsimp only [length0]; omega
    exact this.trans hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let nearDiscrepancy : SectionSixDirectBand -> Real := fun band =>
    ((sectionSixDirectNearCandidates epsilon delta rho ell region length band
      A).card : Real) -
      lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell region
        length band B).card : Real)
  let formalTargetDiscrepancy : SectionSixDirectBand -> Real := fun band =>
    sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
      presentation digit epsilon delta rho length band
  have hTargetAt := hTarget length hlengthTargetAt digit hepsilonSmall
    hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hErrorAt := hError length hlengthErrorAt digit hepsilonSmall
    hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hTargetBound :
      abs (formalTargetDiscrepancy .first +
        formalTargetDiscrepancy .second) <=
          budget / 2 * (A.card : Real) / Real.log X := by
    simpa only [formalTargetDiscrepancy, XNat, X, rho, A] using hTargetAt
  have hErrorBound :
      abs ((nearDiscrepancy .first + nearDiscrepancy .second) -
        (formalTargetDiscrepancy .first +
          formalTargetDiscrepancy .second)) <=
            budget / 2 * (A.card : Real) / Real.log X := by
    simpa only [nearDiscrepancy, formalTargetDiscrepancy, XNat, X, rho, A, B,
      lambda] using hErrorAt
  calc
    abs (nearDiscrepancy .first + nearDiscrepancy .second) =
        abs (((nearDiscrepancy .first + nearDiscrepancy .second) -
          (formalTargetDiscrepancy .first +
            formalTargetDiscrepancy .second)) +
          (formalTargetDiscrepancy .first +
            formalTargetDiscrepancy .second)) := by
      congr 1
      ring
    _ <= abs ((nearDiscrepancy .first + nearDiscrepancy .second) -
          (formalTargetDiscrepancy .first +
            formalTargetDiscrepancy .second)) +
        abs (formalTargetDiscrepancy .first +
          formalTargetDiscrepancy .second) := abs_add_le _ _
    _ <= budget / 2 * (A.card : Real) / Real.log X +
        budget / 2 * (A.card : Real) / Real.log X :=
      add_le_add hErrorBound hTargetBound
    _ = budget * (A.card : Real) / Real.log X := by ring

end

end PrimesRestrictedDigits
