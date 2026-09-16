import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetRegion
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIExponentSimplexPresentation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddedAffineNormal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Weak affine presentations of Proposition 6.2 stable targets

The displayed presentation orders its constraints as source walls, literal coordinate lower
walls, and selected-band walls. The full presentation puts the ordered-simplex walls first.
All inequalities are weak.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Concatenate two weak affine presentations of regions in the same ambient
coordinate space. -/
private noncomputable def propositionSixTwoWeakPresentationInter
    {d : Nat} {left right : Set (Fin d -> Real)}
    (leftPresentation : TypeIIAffineHalfspacePresentation left)
    (rightPresentation : TypeIIAffineHalfspacePresentation right) :
    TypeIIAffineHalfspacePresentation (left ∩ right) where
  constraintCount := leftPresentation.constraintCount +
    rightPresentation.constraintCount
  normal := Fin.append leftPresentation.normal rightPresentation.normal
  bound := Fin.append leftPresentation.bound rightPresentation.bound
  mem_iff := by
    intro x
    rw [Set.mem_inter_iff, leftPresentation.mem_iff,
      rightPresentation.mem_iff, Fin.forall_fin_add]
    constructor
    · rintro ⟨hleft, hright⟩
      exact ⟨fun i => by simpa only [Fin.append_left] using hleft i,
        fun i => by simpa only [Fin.append_right] using hright i⟩
    · rintro ⟨hleft, hright⟩
      exact ⟨fun i => by simpa only [Fin.append_left] using hleft i,
        fun i => by simpa only [Fin.append_right] using hright i⟩

private theorem propositionSixTwoAffineValue_single
    {d : Nat} (i : Fin d) (a : Real) (x : Fin d -> Real) :
    typeIIAffineValue (Pi.single i a) x = a * x i := by
  classical
  simp [typeIIAffineValue, Pi.single_apply]

/-- Constant coefficient `a` on the selected labels and zero elsewhere. -/
private noncomputable def propositionSixTwoSelectedSumNormal
    {ell : Nat} (I : Finset (Fin ell)) (a : Real) : Fin ell -> Real :=
  fun i => if i ∈ I then a else 0

private theorem propositionSixTwoAffineValue_selectedSumNormal
    {ell : Nat} (I : Finset (Fin ell)) (a : Real)
    (y : Fin ell -> Real) :
    typeIIAffineValue (propositionSixTwoSelectedSumNormal I a) y =
      a * ∑ i ∈ I, y i := by
  classical
  rw [typeIIAffineValue]
  simp only [propositionSixTwoSelectedSumNormal, ite_mul, zero_mul,
    Finset.sum_ite_mem_eq]
  rw [← Finset.mul_sum]

private def propositionSixTwoDisplayedBandNormals
    {ell : Nat} (I : Finset (Fin ell)) : Fin 2 -> Fin ell -> Real :=
  ![propositionSixTwoSelectedSumNormal I (-1 : Real),
    propositionSixTwoSelectedSumNormal I 1]

private def propositionSixTwoDisplayedBandBounds
    (epsilon : Real) (band : SectionSixDirectBand) : Fin 2 -> Real :=
  ![-propositionSixTwoBandLower epsilon band,
    propositionSixTwoBandUpper epsilon band]

/-- The displayed walls added after the supplied source presentation. -/
private def propositionSixTwoDisplayedFixedRegion
    (epsilon : Real) {ell : Nat} (I : Finset (Fin ell))
    (band : SectionSixDirectBand) : Set (Fin ell -> Real) :=
  {y | (forall i, sectionSixThetaGap epsilon <= y i) ∧
    propositionSixTwoBandLower epsilon band <= ∑ i ∈ I, y i ∧
    (∑ i ∈ I, y i) <= propositionSixTwoBandUpper epsilon band}

/-- The fixed displayed presentation has the literal coordinate lower walls
first and the two selected-band walls last. -/
private noncomputable def propositionSixTwoDisplayedFixedPresentation
    (epsilon : Real) {ell : Nat} (I : Finset (Fin ell))
    (band : SectionSixDirectBand) :
    TypeIIAffineHalfspacePresentation
      (propositionSixTwoDisplayedFixedRegion epsilon I band) where
  constraintCount := ell + 2
  normal := Fin.append (fun i => Pi.single i (-1 : Real))
    (propositionSixTwoDisplayedBandNormals I)
  bound := Fin.append (fun _ => -sectionSixThetaGap epsilon)
    (propositionSixTwoDisplayedBandBounds epsilon band)
  mem_iff := by
    intro y
    rw [Fin.forall_fin_add]
    constructor
    · rintro ⟨hlower, hbandLower, hbandUpper⟩
      refine ⟨?_, ?_⟩
      · intro i
        simp only [Fin.append_left, propositionSixTwoAffineValue_single,
          neg_one_mul]
        linarith [hlower i]
      · intro c
        fin_cases c
        · simp [Fin.append_right, propositionSixTwoDisplayedBandNormals,
            propositionSixTwoDisplayedBandBounds,
            propositionSixTwoAffineValue_selectedSumNormal, hbandLower]
        · simp [Fin.append_right, propositionSixTwoDisplayedBandNormals,
            propositionSixTwoDisplayedBandBounds,
            propositionSixTwoAffineValue_selectedSumNormal, hbandUpper]
    · rintro ⟨hlowerBounds, hbandBounds⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have hi := hlowerBounds i
        simp only [Fin.append_left, propositionSixTwoAffineValue_single,
          neg_one_mul] at hi
        linarith
      · have hlower := hbandBounds (0 : Fin 2)
        simpa [Fin.append_right, propositionSixTwoDisplayedBandNormals,
          propositionSixTwoDisplayedBandBounds,
          propositionSixTwoAffineValue_selectedSumNormal] using hlower
      · have hupper := hbandBounds (1 : Fin 2)
        simpa [Fin.append_right, propositionSixTwoDisplayedBandNormals,
          propositionSixTwoDisplayedBandBounds,
          propositionSixTwoAffineValue_selectedSumNormal] using hupper

/-- Exact weak presentation of the displayed Proposition 6.2 region. Its
constraint order is source, coordinate lower walls, then selected-band walls. -/
noncomputable def propositionSixTwoDisplayedPresentation
    {ell : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell))
    (band : SectionSixDirectBand) :
    TypeIIAffineHalfspacePresentation
      (propositionSixTwoDisplayedRegion epsilon I sourceRegion band) :=
  propositionSixTwoWeakPresentationInter sourcePresentation
    (propositionSixTwoDisplayedFixedPresentation epsilon I band)

/-- Exact weak presentation of one full stable target. The raw simplex walls
precede all lifted displayed walls. -/
noncomputable def propositionSixTwoStableTargetPresentation
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell))
    (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hd : 0 < ell + pattern.1.1) :
    TypeIIAffineHalfspacePresentation
      (propositionSixTwoStableTargetRegion
        epsilon I sourceRegion band pattern) :=
  propositionSixTwoWeakPresentationInter
    (typeIIExponentSimplexPresentationRaw
      (sectionSixThetaGap epsilon) hd)
    ((propositionSixTwoDisplayedPresentation
      sourcePresentation epsilon I band).liftAlongEmbedding pattern.2)

end

end PrimesRestrictedDigits
