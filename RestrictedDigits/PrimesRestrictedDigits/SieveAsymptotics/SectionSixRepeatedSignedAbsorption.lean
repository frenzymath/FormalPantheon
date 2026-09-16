import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedSignedContribution
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedTerminalAbsorption

/-!
# Signed repeated-terminal absorption

The exact signed occurrence-to-state inequality composes directly with the unsigned
repeated-state Type I absorption at the same proof-dependent source state Finset.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- For fixed positive `delta`, the signed repeated contribution from either
one source band is eventually absorbed into an arbitrary per-band budget. -/
theorem exists_sectionSixRepeatedSignedContributionAbsorptionThreshold
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (ell : Nat) (rho : Real) (hrho : 0 < rho)
    (delta : Real) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon) :
    ∃ (length0 : Nat) (hlength0 : 1 ≤ length0),
      ∀ (length : Nat) (hlength : length0 ≤ length)
        (digit : Fin 10) (region : Set (Fin ell → Real))
        (band : SectionSixStateBand),
        abs (sectionSixSourceBandSelectedSignedContribution digit region
          hepsilon hepsilonSmall (hlength0.trans hlength) hdeltaGap band
            sectionSixRepeatedTerminalPredicate) ≤
          rho * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log (((10 ^ length : Nat) : Real)) := by
  obtain ⟨length0, hlength0, hunsigned⟩ :=
    exists_sectionSixRepeatedTerminalAbsorptionThreshold epsilon hepsilon
      hepsilonSmall ell rho hrho delta hdelta hdeltaGap
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit region band
  exact
    (abs_sectionSixSourceBandRepeatedSignedContribution_le_stateFinset
      digit region hepsilon hepsilonSmall (hlength0.trans hlength)
        hdeltaGap band).trans
      (hunsigned length hlength digit region band)

end

end PrimesRestrictedDigits
