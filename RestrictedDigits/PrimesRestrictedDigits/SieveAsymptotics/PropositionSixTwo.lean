import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoMixedNearAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoOutsideNearCandidateAbsorption

/-!
# Proposition 6.2

The mixed-region near estimate and the complete source-candidate outside-near estimate
reassemble the exact strict Proposition 6.2 band sums.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.2, pp. 137--138, and proof of Lemma 7.3, pp.
149--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Maynard's strict Proposition 6.2, with one threshold uniform in the
excluded digit and in both direct bands. -/
theorem propositionSixTwo
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {ell : Nat} (I : Finset (Fin ell)) (j : Fin ell)
    {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region) :
    propositionSixTwoAsymptotic epsilon I j region := by
  intro budget hbudget
  obtain ⟨firstLength, hfirstLength, hfirstAt⟩ :=
    exists_propositionSixTwoMixedNearCandidateDiscrepancy_band_budget_upper
      epsilon hepsilon hepsilonSmall (budget / 2) (by positivity) I j region
        presentation .first
  obtain ⟨secondLength, hsecondLength, hsecondAt⟩ :=
    exists_propositionSixTwoMixedNearCandidateDiscrepancy_band_budget_upper
      epsilon hepsilon hepsilonSmall (budget / 2) (by positivity) I j region
        presentation .second
  obtain ⟨outsideLength, houtsideLength, houtsideAt⟩ :=
    exists_propositionSixTwoOutsideNearCandidateDiscrepancy_budget_upper
      epsilon hepsilon hepsilonSmall (budget / 2) (by positivity) I j region
  let length0 : Nat := max outsideLength (max firstLength secondLength)
  have hlength0 : 1 <= length0 :=
    houtsideLength.trans (Nat.le_max_left _ _)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit band
  have hfirstLengthAt : firstLength <= length :=
    (Nat.le_max_left firstLength secondLength).trans
      ((Nat.le_max_right outsideLength _).trans hlength)
  have hsecondLengthAt : secondLength <= length :=
    (Nat.le_max_right firstLength secondLength).trans
      ((Nat.le_max_right outsideLength _).trans hlength)
  have houtsideLengthAt : outsideLength <= length :=
    (Nat.le_max_left outsideLength _).trans hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let nearDiscrepancy : Real :=
    ((propositionSixTwoNearCandidates epsilon ell I j region length band rho
      A).card : Real) -
      lambda * ((propositionSixTwoNearCandidates epsilon ell I j region length
        band rho B).card : Real)
  let outsideDiscrepancy : Real :=
    ((propositionSixTwoOutsideNearCandidates epsilon ell I j region length band
      rho A).card : Real) -
      lambda * ((propositionSixTwoOutsideNearCandidates epsilon ell I j region
        length band rho B).card : Real)
  let mass : Real := (A.card : Real) / Real.log X
  have hnear : abs nearDiscrepancy <= budget / 2 * mass := by
    cases band with
    | first =>
        have hraw := hfirstAt length hfirstLengthAt digit
        have hraw' : abs nearDiscrepancy <=
            budget / 2 * (A.card : Real) / Real.log X := by
          simpa only [nearDiscrepancy, lambda, XNat, X, rho, A, B] using hraw
        simpa only [mass, mul_div_assoc] using hraw'
    | second =>
        have hraw := hsecondAt length hsecondLengthAt digit
        have hraw' : abs nearDiscrepancy <=
            budget / 2 * (A.card : Real) / Real.log X := by
          simpa only [nearDiscrepancy, lambda, XNat, X, rho, A, B] using hraw
        simpa only [mass, mul_div_assoc] using hraw'
  have houtside : abs outsideDiscrepancy <= budget / 2 * mass := by
    have hraw := houtsideAt length houtsideLengthAt digit band
    have hraw' : abs outsideDiscrepancy <=
        budget / 2 * (A.card : Real) / Real.log X := by
      simpa only [outsideDiscrepancy, lambda, XNat, X, rho, A, B] using hraw
    simpa only [mass, mul_div_assoc] using hraw'
  have hsplit := propositionSixTwoBandSum_eq_near_add_outsideDiscrepancy
    epsilon rho ell I j region digit length band
  have hsplit' : propositionSixTwoBandSum epsilon ell I j region digit length
      band = nearDiscrepancy + outsideDiscrepancy := by
    simpa only [nearDiscrepancy, outsideDiscrepancy, lambda, XNat, X, rho, A,
      B, div_eq_mul_inv, mul_assoc] using hsplit
  rw [hsplit']
  calc
    abs (nearDiscrepancy + outsideDiscrepancy) <=
        abs nearDiscrepancy + abs outsideDiscrepancy := abs_add_le _ _
    _ <= budget / 2 * mass + budget / 2 * mass :=
      add_le_add hnear houtside
    _ = budget * (A.card : Real) / Real.log X := by
      dsimp only [mass]
      ring

end

end PrimesRestrictedDigits
