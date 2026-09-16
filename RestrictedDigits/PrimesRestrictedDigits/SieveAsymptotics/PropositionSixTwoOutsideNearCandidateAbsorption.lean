import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoOutsideNearCandidateTailIncidence
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternTargetTailCharge
import PrimesRestrictedDigits.SieveAsymptotics.TypeIILogLogWidthAbsorption

/-!
# Proposition 6.2 outside-near candidate absorption

The complete source-candidate tail is bounded by the full stable-pattern multiplicity, the
weak small-product tail, and decay of the log-log width.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 149--152, Eq. (9.4), p. 165, and
Proposition 7.2 proof, pp. 163--168.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The requested-minus-weighted-ambient outside-near candidate discrepancy is
eventually absorbed into an arbitrary positive logarithmic budget, uniformly
in the excluded digit and direct band. -/
theorem exists_propositionSixTwoOutsideNearCandidateDiscrepancy_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget)
    {ell : Nat} (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
      ∀ digit : Fin 10,
      ∀ band : SectionSixDirectBand,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let rho : Real := majorArcM2LogLogDelta XNat
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let B : Finset Nat := maynardAmbientCarrier X
        let lambda : Real :=
          (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
        let outsideCount : Finset Nat -> Real := fun C =>
          ((propositionSixTwoOutsideNearCandidates epsilon ell I j region
            length band rho C).card : Real)
        abs (outsideCount A - lambda * outsideCount B) <=
          budget * (A.card : Real) / Real.log X := by
  let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
  let Kreal : Real :=
    (Fintype.card (PropositionSixTwoStablePattern ell M) : Real)
  obtain ⟨Ctail, hCtail, tailLength, htailLength, htailAt⟩ :=
    exists_propositionSixTwoStablePatternTargetTailCharge_upper epsilon ell
  obtain ⟨widthLength, hwidthLength, hwidthAt⟩ :=
    exists_mul_majorArcM2LogLogDelta_powTen_le Ctail budget hCtail.le hbudget
  let length0 : Nat := max tailLength widthLength
  have hlength0 : 1 <= length0 :=
    htailLength.trans (Nat.le_max_left _ _)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit band
  have htailLengthAt : tailLength <= length :=
    (Nat.le_max_left tailLength widthLength).trans hlength
  have hwidthLengthAt : widthLength <= length :=
    (Nat.le_max_right tailLength widthLength).trans hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let near : Finset Nat := typeIINearXCarrier XNat rho
  let outsideCount : Finset Nat -> Real := fun C =>
    ((propositionSixTwoOutsideNearCandidates epsilon ell I j region length band
      rho C).card : Real)
  let tailCharge : Real :=
    ((A \ near).card : Real) + lambda * ((B \ near).card : Real)
  let mass : Real := (A.card : Real) / Real.log X
  have hlengthOne : 1 <= length := hlength0.trans hlength
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hAIncidenceNat :=
    card_propositionSixTwoOutsideNearCandidates_le_patternCard_mul_tail
      (epsilon := epsilon) (rho := rho) (I := I) (j := j)
      (region := region) band A hgap
        (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length)
  have hBIncidenceNat :=
    card_propositionSixTwoOutsideNearCandidates_le_patternCard_mul_tail
      (epsilon := epsilon) (rho := rho) (I := I) (j := j)
      (region := region) band B hgap (fun _ hn => hn)
  have hAIncidence : outsideCount A <=
      Kreal * ((A \ near).card : Real) := by
    dsimp only [outsideCount, Kreal, M, A, near, rho, XNat]
    exact_mod_cast hAIncidenceNat
  have hBIncidence : outsideCount B <=
      Kreal * ((B \ near).card : Real) := by
    dsimp only [outsideCount, Kreal, M, B, near, rho, X, XNat]
    exact_mod_cast hBIncidenceNat
  have hXOne : 1 < X := by
    dsimp only [X, XNat]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hlog : 0 < Real.log X := Real.log_pos hXOne
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact mul_nonneg (restrictedDigitDensity_nonneg digit)
      (div_nonneg (Nat.cast_nonneg A.card) (zero_lt_one.trans hXOne).le)
  have hKreal : 0 <= Kreal := by
    dsimp only [Kreal]
    exact Nat.cast_nonneg _
  have houtsideANonneg : 0 <= outsideCount A := by
    dsimp only [outsideCount]
    exact Nat.cast_nonneg _
  have houtsideBNonneg : 0 <= outsideCount B := by
    dsimp only [outsideCount]
    exact Nat.cast_nonneg _
  have hpositiveCharge :
      outsideCount A + lambda * outsideCount B <= Kreal * tailCharge := by
    calc
      outsideCount A + lambda * outsideCount B <=
          Kreal * ((A \ near).card : Real) +
            lambda * (Kreal * ((B \ near).card : Real)) :=
        add_le_add hAIncidence
          (mul_le_mul_of_nonneg_left hBIncidence hlambda)
      _ = Kreal * tailCharge := by
        dsimp only [tailCharge]
        ring
  have htailRaw := htailAt length htailLengthAt digit
  have htail : Kreal * tailCharge <= Ctail * rho * mass := by
    simpa only [M, Kreal, tailCharge, mass, lambda, near, B, A, rho, X,
      XNat, mul_div_assoc] using htailRaw
  have hwidth : Ctail * rho <= budget := by
    simpa only [rho, XNat] using hwidthAt length hwidthLengthAt
  have hmass : 0 <= mass := by
    dsimp only [mass]
    exact div_nonneg (Nat.cast_nonneg A.card) hlog.le
  have hscaled : Ctail * rho * mass <= budget * mass :=
    mul_le_mul_of_nonneg_right hwidth hmass
  have habs : abs (outsideCount A - lambda * outsideCount B) <=
      outsideCount A + lambda * outsideCount B := by
    calc
      abs (outsideCount A - lambda * outsideCount B) <=
          abs (outsideCount A) + abs (lambda * outsideCount B) := abs_sub _ _
      _ = outsideCount A + lambda * outsideCount B := by
        rw [abs_of_nonneg houtsideANonneg,
          abs_of_nonneg (mul_nonneg hlambda houtsideBNonneg)]
  change abs (outsideCount A - lambda * outsideCount B) <=
    budget * (A.card : Real) / Real.log X
  calc
    abs (outsideCount A - lambda * outsideCount B) <=
        outsideCount A + lambda * outsideCount B := habs
    _ <= Kreal * tailCharge := hpositiveCharge
    _ <= Ctail * rho * mass := htail
    _ <= budget * mass := hscaled
    _ = budget * (A.card : Real) / Real.log X := by
      dsimp only [mass]
      ring

end

end PrimesRestrictedDigits
