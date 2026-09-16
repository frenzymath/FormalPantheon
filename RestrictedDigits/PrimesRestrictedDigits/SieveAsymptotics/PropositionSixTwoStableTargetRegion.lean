import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddedAffineNormal
import Mathlib.Tactic.Linarith

/-!
# Stable target regions for Proposition 6.2

One fixed stable-position pattern pulls the displayed Proposition 6.2 walls back to the
complete normalized prime-factor tuple. All walls in this module are weak. Source:
`MAYNARD-PRD-PUBLISHED`, Proposition 7.2 and proof of Lemma 7.3, pp. 147--152 and 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Lower endpoint of either selected-product band in Proposition 6.2. -/
def propositionSixTwoBandLower
    (epsilon : Real) : SectionSixDirectBand -> Real
  | .first => sectionSixThetaOne epsilon
  | .second => 1 - sectionSixThetaTwo epsilon

/-- Upper endpoint of either selected-product band in Proposition 6.2. -/
def propositionSixTwoBandUpper
    (epsilon : Real) : SectionSixDirectBand -> Real
  | .first => sectionSixThetaTwo epsilon
  | .second => 1 - sectionSixThetaOne epsilon

namespace PropositionSixTwoStablePattern

/-- Stable full-tuple positions occupied by the selected displayed labels. -/
noncomputable def selectedPositions {ell M : Nat}
    (pattern : PropositionSixTwoStablePattern ell M)
    (I : Finset (Fin ell)) : Finset (Fin (ell + pattern.1.1)) :=
  I.map pattern.2

end PropositionSixTwoStablePattern

/-- Summing over selected stable positions preserves the labelled displayed
sum, including when displayed prime values coincide. -/
theorem sum_propositionSixTwoStablePattern_selectedPositions
    {ell M : Nat} (pattern : PropositionSixTwoStablePattern ell M)
    (I : Finset (Fin ell))
    (x : Fin (ell + pattern.1.1) -> Real) :
    (∑ z ∈ pattern.selectedPositions I, x z) =
      ∑ i ∈ I, x (pattern.2 i) := by
  simp [PropositionSixTwoStablePattern.selectedPositions]

/-- The exact displayed-coordinate target before lifting to the complete
stable factor tuple. The coordinate lower walls are retained literally for
the later normalization-wall classification. -/
def propositionSixTwoDisplayedRegion
    (epsilon : Real) {ell : Nat} (I : Finset (Fin ell))
    (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixDirectBand) : Set (Fin ell -> Real) :=
  {y | y ∈ sourceRegion ∧
    (forall i, sectionSixThetaGap epsilon <= y i) ∧
    propositionSixTwoBandLower epsilon band <= ∑ i ∈ I, y i ∧
    (∑ i ∈ I, y i) <= propositionSixTwoBandUpper epsilon band}

@[simp] theorem mem_propositionSixTwoDisplayedRegion
    {epsilon : Real} {ell : Nat} {I : Finset (Fin ell)}
    {sourceRegion : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {y : Fin ell -> Real} :
    y ∈ propositionSixTwoDisplayedRegion epsilon I sourceRegion band <->
      y ∈ sourceRegion ∧
      (forall i, sectionSixThetaGap epsilon <= y i) ∧
      propositionSixTwoBandLower epsilon band <= ∑ i ∈ I, y i ∧
      (∑ i ∈ I, y i) <= propositionSixTwoBandUpper epsilon band :=
  Iff.rfl

/-- The closed target region on the complete stable prime-factor tuple. The
printed source cap is intentionally absent because it depends on the external
base `X`, rather than only on this fixed normalized target. -/
def propositionSixTwoStableTargetRegion
    {ell M : Nat} (epsilon : Real) (I : Finset (Fin ell))
    (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M) :
    Set (Fin (ell + pattern.1.1) -> Real) :=
  typeIIExponentSimplex (sectionSixThetaGap epsilon) ∩
    typeIIAffineEmbeddingPreimageRegion pattern.2
      (propositionSixTwoDisplayedRegion epsilon I sourceRegion band)

@[simp] theorem mem_propositionSixTwoStableTargetRegion
    {epsilon : Real} {ell M : Nat} {I : Finset (Fin ell)}
    {sourceRegion : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {pattern : PropositionSixTwoStablePattern ell M}
    {x : Fin (ell + pattern.1.1) -> Real} :
    x ∈ propositionSixTwoStableTargetRegion
        epsilon I sourceRegion band pattern <->
      x ∈ typeIIExponentSimplex (sectionSixThetaGap epsilon) ∧
      (fun i => x (pattern.2 i)) ∈
        propositionSixTwoDisplayedRegion epsilon I sourceRegion band :=
  Iff.rfl

/-- Every stable target is contained in the ordered theta-gap simplex. -/
theorem propositionSixTwoStableTargetRegion_isTypeIISourceRegion
    (epsilon : Real) {ell M : Nat} (I : Finset (Fin ell))
    (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M) :
    IsTypeIISourceRegion (sectionSixThetaGap epsilon)
      (propositionSixTwoStableTargetRegion
        epsilon I sourceRegion band pattern) := by
  intro x hx
  exact hx.1

/-- Both selected-product bands have the exact two-epsilon convenience
margin. The complementary band uses all positions outside the selected
displayed labels. -/
theorem propositionSixTwoStableTargetRegion_convenient_two_mul
    (epsilon : Real) {ell M : Nat} (I : Finset (Fin ell))
    (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M) :
    IsTypeIIRegionConvenient (2 * epsilon)
      (propositionSixTwoStableTargetRegion
        epsilon I sourceRegion band pattern) := by
  let selected := pattern.selectedPositions I
  cases band with
  | first =>
      refine ⟨selected, ?_⟩
      intro x hx
      have hdisplay :=
        (mem_propositionSixTwoStableTargetRegion.mp hx).2
      have hband :=
        (mem_propositionSixTwoDisplayedRegion.mp hdisplay).2.2
      simp only [propositionSixTwoBandLower,
        propositionSixTwoBandUpper] at hband
      rw [show selected = pattern.selectedPositions I by rfl,
        sum_propositionSixTwoStablePattern_selectedPositions pattern I x]
      simpa [propositionSixTwoBandLower, propositionSixTwoBandUpper,
        sectionSixThetaOne, sectionSixThetaTwo] using hband
  | second =>
      let complement : Finset (Fin (ell + pattern.1.1)) :=
        Finset.univ \ selected
      refine ⟨complement, ?_⟩
      intro x hx
      have htarget := mem_propositionSixTwoStableTargetRegion.mp hx
      have hdisplay := htarget.2
      have hband :=
        (mem_propositionSixTwoDisplayedRegion.mp hdisplay).2.2
      simp only [propositionSixTwoBandLower,
        propositionSixTwoBandUpper] at hband
      have hsumAll : (∑ z, x z) = 1 := htarget.1.2.2
      have hsumComplement :
          (∑ z ∈ complement, x z) =
            1 - ∑ i ∈ I, x (pattern.2 i) := by
        rw [show complement = Finset.univ \ selected by rfl,
          Finset.sum_sdiff_eq_sub (Finset.subset_univ selected)]
        change (∑ z, x z) - (∑ z ∈ selected, x z) = _
        rw [hsumAll, show selected = pattern.selectedPositions I by rfl,
          sum_propositionSixTwoStablePattern_selectedPositions pattern I x]
      rw [hsumComplement]
      have hconverted :
          sectionSixThetaOne epsilon <=
              1 - ∑ i ∈ I, x (pattern.2 i) ∧
            1 - ∑ i ∈ I, x (pattern.2 i) <=
              sectionSixThetaTwo epsilon := by
        exact And.intro (by linarith [hband.2]) (by linarith [hband.1])
      simpa [sectionSixThetaOne, sectionSixThetaTwo] using hconverted

/-- Discarding one epsilon of the exact margin gives the convenience premise
used by Proposition 7.2. -/
theorem propositionSixTwoStableTargetRegion_convenient
    {epsilon : Real} (hepsilon : 0 <= epsilon)
    {ell M : Nat} (I : Finset (Fin ell))
    (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M) :
    IsTypeIIRegionConvenient epsilon
      (propositionSixTwoStableTargetRegion
        epsilon I sourceRegion band pattern) := by
  obtain ⟨positions, hpositions⟩ :=
    propositionSixTwoStableTargetRegion_convenient_two_mul
      epsilon I sourceRegion band pattern
  refine ⟨positions, ?_⟩
  intro x hx
  have hbounds := hpositions x hx
  exact ⟨by linarith [hbounds.1], by linarith [hbounds.2]⟩

end

end PrimesRestrictedDigits
