import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVSelectedSignedContributionAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStrictContributionAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectRepeatedAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedSignedAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectBaseFundamental
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalFundamentalAbsorption

/-!
# Proposition 6.1

The exact four-range decomposition is closed with one common auxiliary delta. Its two source
recurrences and two direct recurrences give nine separately absorbed components. See
`MAYNARD-PRD-PUBLISHED`, Proposition 6.1 and its proof, pp. 136--138 and 156--158.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem abs_nine_sum_le
    (a b c d e f g h i : Real) :
    abs (a + b + c + d + e + f + g + h + i) <=
      abs a + abs b + abs c + abs d + abs e + abs f + abs g + abs h + abs i := by
  calc
    abs (a + b + c + d + e + f + g + h + i) <=
        abs (a + b + c + d + e + f + g + h) + abs i := abs_add_le _ _
    _ <= abs (a + b + c + d + e + f + g) + abs h + abs i := by
      gcongr
      exact abs_add_le _ _
    _ <= abs (a + b + c + d + e + f) + abs g + abs h + abs i := by
      gcongr
      exact abs_add_le _ _
    _ <= abs (a + b + c + d + e) + abs f + abs g + abs h + abs i := by
      gcongr
      exact abs_add_le _ _
    _ <= abs (a + b + c + d) + abs e + abs f + abs g + abs h + abs i := by
      gcongr
      exact abs_add_le _ _
    _ <= abs (a + b + c) + abs d + abs e + abs f + abs g + abs h + abs i := by
      gcongr
      exact abs_add_le _ _
    _ <= abs (a + b) + abs c + abs d + abs e + abs f + abs g + abs h + abs i := by
      gcongr
      exact abs_add_le _ _
    _ <= abs a + abs b + abs c + abs d + abs e + abs f + abs g + abs h + abs i := by
      gcongr
      exact abs_add_le _ _

/-- Maynard's Proposition 6.1, with the little-oh claim expanded into an
eventual absolute-value estimate uniform in the excluded digit. -/
theorem propositionSixOne
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region) :
    propositionSixOneAsymptotic epsilon ell region := by
  intro rho hrho
  let budget : Real := rho / 9
  have hbudget : 0 < budget := by
    dsimp only [budget]
    positivity
  obtain ⟨delta, hdelta, _hdeltaEpsilon, hdeltaGap, fundamentalLength,
      hfundamentalLength, hfundamental⟩ :=
    exists_sectionSixTerminalTFundamentalResidualAbsorptionDeltaThreshold
      epsilon hepsilon hepsilonSmall hepsilonRosser ell epsilon hepsilon budget
        hbudget
  obtain ⟨sourceRepeatedLength, hsourceRepeatedLength, hsourceRepeated⟩ :=
    exists_sectionSixRepeatedSignedContributionAbsorptionThreshold epsilon
      hepsilon hepsilonSmall ell budget hbudget delta hdelta hdeltaGap.le
  obtain ⟨directRepeatedLength, hdirectRepeatedLength, hdirectRepeated⟩ :=
    exists_sectionSixDirectRangeRepeatedAbsorptionThreshold epsilon hepsilon
      hepsilonSmall ell budget hbudget delta hdelta hdeltaGap
  obtain ⟨directStrictLength, hdirectStrictLength, hdirectStrict⟩ :=
    exists_sectionSixDirectTwoBandRangeStrictContribution_budget_upper delta
      budget hdelta hbudget epsilon hepsilon hepsilonSmall hdeltaGap ell region
        presentation.toMixed
  obtain ⟨terminalVLength, hterminalVLength, hterminalV⟩ :=
    exists_sectionSixTerminalVTwoBandSelectedSignedContribution_budget_upper
      delta budget hdelta hbudget epsilon hepsilon hepsilonSmall hdeltaGap ell
        region presentation
  let length0 := max fundamentalLength
    (max sourceRepeatedLength (max directRepeatedLength
      (max directStrictLength terminalVLength)))
  have hlength0 : 1 <= length0 := by
    exact hfundamentalLength.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hfundamentalLengthAt : fundamentalLength <= length := by
    exact (by dsimp only [length0]; omega : fundamentalLength <= length0).trans
      hlength
  have hsourceRepeatedLengthAt : sourceRepeatedLength <= length := by
    exact (by dsimp only [length0]; omega : sourceRepeatedLength <= length0).trans
      hlength
  have hdirectRepeatedLengthAt : directRepeatedLength <= length := by
    exact (by dsimp only [length0]; omega : directRepeatedLength <= length0).trans
      hlength
  have hdirectStrictLengthAt : directStrictLength <= length := by
    exact (by dsimp only [length0]; omega : directStrictLength <= length0).trans
      hlength
  have hterminalVLengthAt : terminalVLength <= length := by
    exact (by dsimp only [length0]; omega : terminalVLength <= length0).trans
      hlength
  have hlengthOne : 1 <= length := hlength0.trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  let mass : Real := ((paddedRestrictedNumbers digit length).card : Real) /
    Real.log X
  let sourceAll : SectionSixStateBand -> Real := fun band =>
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
      hepsilonSmall hlengthOne hdeltaGap.le band (fun _ => true)
  let sourceRepeated : SectionSixStateBand -> Real := fun band =>
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
      hepsilonSmall hlengthOne hdeltaGap.le band
        sectionSixRepeatedTerminalPredicate
  let terminalT : SectionSixStateBand -> Real := fun band =>
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
      hepsilonSmall hlengthOne hdeltaGap.le band sectionSixTerminalTPredicate
  let terminalV : SectionSixStateBand -> Real := fun band =>
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
      hepsilonSmall hlengthOne hdeltaGap.le band sectionSixTerminalVPredicate
  let directSource : SectionSixDirectBand -> Real := fun band =>
    sectionSixDirectRangeSourceContribution digit epsilon delta ell length region
      band
  let directBase : SectionSixDirectBand -> Real := fun band =>
    sectionSixDirectRangeBaseContribution digit epsilon delta ell length region
      band
  let directStrict : SectionSixDirectBand -> Real := fun band =>
    sectionSixDirectRangeStrictContribution digit epsilon delta ell length region
      band
  let directRepeated : SectionSixDirectBand -> Real := fun band =>
    sectionSixDirectRangeRepeatedContribution digit epsilon delta ell length region
      band
  have hsourceAll (band : SectionSixStateBand) :
      sourceAll band = sourceRepeated band + terminalT band + terminalV band := by
    rw [show sourceAll band = sourceRepeated band +
        sectionSixSourceBandSelectedSignedContribution digit region hepsilon
          hepsilonSmall hlengthOne hdeltaGap.le band
            (fun state => !sectionSixRepeatedTerminalPredicate state) by
      simpa only [sourceAll, sourceRepeated] using
        sectionSixSourceBandSelectedSignedContribution_repeated_partition digit
          region hepsilon hepsilonSmall hlengthOne hdeltaGap.le band]
    rw [show sectionSixSourceBandSelectedSignedContribution digit region hepsilon
          hepsilonSmall hlengthOne hdeltaGap.le band
            (fun state => !sectionSixRepeatedTerminalPredicate state) =
        terminalT band + terminalV band by
      simpa only [terminalT, terminalV] using
        sectionSixSourceBandSelectedSignedContribution_nonrepeated_eq_T_add_V
          digit region hepsilon hepsilonSmall hlengthOne hdeltaGap.le band]
    ring
  have hdirectSource (band : SectionSixDirectBand) :
      directSource band =
        directBase band - directStrict band - directRepeated band := by
    exact sectionSixDirectRangeSourceContribution_eq_base_sub_strict_sub_repeated
      digit hlengthOne hdeltaGap.le region band
  have hsum : propositionSixOneSum epsilon ell region digit length =
      sourceRepeated .low + sourceRepeated .high +
      terminalT .low + terminalT .high +
      (terminalV .low + terminalV .high) +
      (directBase .first + directBase .second) +
      -(directStrict .first + directStrict .second) +
      -directRepeated .first + -directRepeated .second := by
    rw [propositionSixOneSum_eq_four_range_sums hepsilon hepsilonSmall hlengthOne
      region digit]
    rw [show (∑ p ∈ sectionSixSourceBandPrimeTuples epsilon ell region length
          .low, sectionSixSiftedSum digit length
            (primeTupleProduct p).toPNat'
              (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)) =
        sourceAll .low by
      symm
      simpa only [sourceAll] using
        sectionSixSourceBandSelectedSignedContribution_true_eq_sourceTerms digit
          region hepsilon hepsilonSmall hlengthOne hdelta hdeltaGap.le .low]
    rw [show (∑ p ∈ sectionSixSourceBandPrimeTuples epsilon ell region length
          .high, sectionSixSiftedSum digit length
            (primeTupleProduct p).toPNat'
              (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)) =
        sourceAll .high by
      symm
      simpa only [sourceAll] using
        sectionSixSourceBandSelectedSignedContribution_true_eq_sourceTerms digit
          region hepsilon hepsilonSmall hlengthOne hdelta hdeltaGap.le .high]
    change sourceAll .low + directSource .first + sourceAll .high +
      directSource .second = _
    rw [hsourceAll .low, hsourceAll .high, hdirectSource .first,
      hdirectSource .second]
    ring
  have hfundamentalAt := hfundamental length hfundamentalLengthAt digit
  have hfundamentalAt' :
      ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real) *
          sectionSixFundamentalResidual digit epsilon delta length <=
        budget * mass := by
    calc
      _ <= budget * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log (((10 ^ length : Nat) : Real)) := hfundamentalAt
      _ = budget * mass := by
        dsimp only [mass, X]
        ring
  have hsourceRepeatedLow := hsourceRepeated length hsourceRepeatedLengthAt digit
    region .low
  have hsourceRepeatedHigh := hsourceRepeated length hsourceRepeatedLengthAt digit
    region .high
  have hdirectRepeatedFirst := hdirectRepeated length hdirectRepeatedLengthAt digit
    region .first
  have hdirectRepeatedSecond := hdirectRepeated length hdirectRepeatedLengthAt digit
    region .second
  have hdirectStrictAt := hdirectStrict length hdirectStrictLengthAt digit
  have hterminalVAt := hterminalV length hterminalVLengthAt digit
  have hterminalTLow :=
    abs_sectionSixSourceBandTSignedContribution_le_fundamentalResidual digit
      region hepsilon hepsilonSmall hlengthOne hdelta hdeltaGap.le hdeltaGap .low
  have hterminalTHigh :=
    abs_sectionSixSourceBandTSignedContribution_le_fundamentalResidual digit
      region hepsilon hepsilonSmall hlengthOne hdelta hdeltaGap.le hdeltaGap .high
  have hdirectBase :=
    abs_sectionSixDirectRangeBaseContributions_le_fundamentalResidual digit region
      hepsilon hepsilonSmall hlengthOne hdeltaGap
  have hterminalTLow' : abs (terminalT .low) <= budget * mass := by
    exact hterminalTLow.trans (by
      simpa only [terminalT, sectionSixFundamentalResidual] using
        hfundamentalAt')
  have hterminalTHigh' : abs (terminalT .high) <= budget * mass := by
    exact hterminalTHigh.trans (by
      simpa only [terminalT, sectionSixFundamentalResidual] using
        hfundamentalAt')
  have hresidualNonneg : 0 <=
      sectionSixFundamentalResidual digit epsilon delta length := by
    unfold sectionSixFundamentalResidual
    dsimp only
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hceil : 0 < Nat.ceil (1 / delta) := Nat.ceil_pos.mpr (by positivity)
  have hKnat : 1 <= 5 * (Nat.ceil (1 / delta)) ^ ell := by
    have hp : 1 <= (Nat.ceil (1 / delta)) ^ ell :=
      Nat.one_le_pow ell _ hceil
    omega
  have hK : (1 : Real) <=
      ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real) := by
    exact_mod_cast hKnat
  have hdirectBase' :
      abs (directBase .first + directBase .second) <= budget * mass := by
    apply hdirectBase.trans
    calc
      sectionSixFundamentalResidual digit epsilon delta length =
          1 * sectionSixFundamentalResidual digit epsilon delta length := by ring
      _ <= ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real) *
          sectionSixFundamentalResidual digit epsilon delta length :=
        mul_le_mul_of_nonneg_right hK hresidualNonneg
      _ <= budget * mass := hfundamentalAt'
  have hsourceRepeatedLow' : abs (sourceRepeated .low) <= budget * mass := by
    calc
      _ <= budget * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log (((10 ^ length : Nat) : Real)) := by
        simpa only [sourceRepeated] using hsourceRepeatedLow
      _ = budget * mass := by dsimp only [mass, X]; ring
  have hsourceRepeatedHigh' : abs (sourceRepeated .high) <= budget * mass := by
    calc
      _ <= budget * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log (((10 ^ length : Nat) : Real)) := by
        simpa only [sourceRepeated] using hsourceRepeatedHigh
      _ = budget * mass := by dsimp only [mass, X]; ring
  have hdirectRepeatedFirst' : abs (directRepeated .first) <= budget * mass := by
    calc
      _ <= budget * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log (((10 ^ length : Nat) : Real)) := by
        simpa only [directRepeated] using hdirectRepeatedFirst
      _ = budget * mass := by dsimp only [mass, X]; ring
  have hdirectRepeatedSecond' : abs (directRepeated .second) <= budget * mass := by
    calc
      _ <= budget * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log (((10 ^ length : Nat) : Real)) := by
        simpa only [directRepeated] using hdirectRepeatedSecond
      _ = budget * mass := by dsimp only [mass, X]; ring
  have hdirectStrictAt' :
      abs (directStrict .first + directStrict .second) <= budget * mass := by
    calc
      _ <= budget * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log (((10 ^ length : Nat) : Real)) := by
        simpa only [directStrict] using hdirectStrictAt
      _ = budget * mass := by dsimp only [mass, X]; ring
  have hterminalVAt' :
      abs (terminalV .low + terminalV .high) <= budget * mass := by
    calc
      _ <= budget * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log (((10 ^ length : Nat) : Real)) := by
        simpa only [terminalV] using hterminalVAt
      _ = budget * mass := by dsimp only [mass, X]; ring
  rw [hsum]
  calc
    abs (sourceRepeated .low + sourceRepeated .high +
        terminalT .low + terminalT .high +
        (terminalV .low + terminalV .high) +
        (directBase .first + directBase .second) +
        -(directStrict .first + directStrict .second) +
        -directRepeated .first + -directRepeated .second) <=
      abs (sourceRepeated .low) + abs (sourceRepeated .high) +
        abs (terminalT .low) + abs (terminalT .high) +
        abs (terminalV .low + terminalV .high) +
        abs (directBase .first + directBase .second) +
        abs (-(directStrict .first + directStrict .second)) +
        abs (-directRepeated .first) + abs (-directRepeated .second) :=
      abs_nine_sum_le _ _ _ _ _ _ _ _ _
    _ <= budget * mass + budget * mass + budget * mass + budget * mass +
        budget * mass + budget * mass + budget * mass + budget * mass +
          budget * mass := by
      rw [abs_neg, abs_neg, abs_neg]
      gcongr
    _ = rho * ((paddedRestrictedNumbers digit length).card : Real) /
        Real.log ((10 ^ length : Nat) : Real) := by
      dsimp only [budget, mass, X]
      ring

end

end PrimesRestrictedDigits
