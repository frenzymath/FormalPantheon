import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddedAffineNormal
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddingComplementFactorization
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIExponentSimplexPresentation

/-!
# Terminal-V stable-pattern target regions

This is the raw affine carrier for one terminal-V stable pattern in the proof of Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, pp. 149--152 and 156--157. Reverse decoding requires a separate
realized `StrictMono` pattern witness.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixTerminalVStablePattern

/-- Increasing enumeration of the coordinates outside all displayed inner and
source labels. -/
noncomputable def residualPositionEmbedding {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M) :
    Fin pattern.2.1.1 ↪o
      Fin ((pattern.1.1 + ell) + pattern.2.1.1) :=
  typeIIComplementPositionEmbedding pattern.2.2

/-- Position of the first accumulated inner label. -/
def firstInnerPosition {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) :
    Fin ((pattern.1.1 + ell) + pattern.2.1.1) :=
  pattern.innerPositionEmbedding ⟨0, hinner⟩

/-- Position of the first residual complement label. -/
noncomputable def firstResidualPosition {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hresidual : 0 < pattern.2.1.1) :
    Fin ((pattern.1.1 + ell) + pattern.2.1.1) :=
  pattern.residualPositionEmbedding ⟨0, hresidual⟩

end SectionSixTerminalVStablePattern

/-- Sum of the source-labelled coordinates in a terminal-V stable pattern. -/
def sectionSixTerminalVSourceSum {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) : Real :=
  ∑ i, x (pattern.sourcePositionEmbedding i)

/-- Sum of the accumulated-inner coordinates in a terminal-V stable pattern. -/
def sectionSixTerminalVInnerSum {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) : Real :=
  ∑ i, x (pattern.innerPositionEmbedding i)

/-- Sum of all displayed inner and source coordinates. -/
def sectionSixTerminalVDisplayedSum {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) : Real :=
  sectionSixTerminalVSourceSum pattern x +
    sectionSixTerminalVInnerSum pattern x

/-- The normalized terminal cutoff exponent in either recurrence band. -/
def sectionSixTerminalVCutoffExponent
    (epsilon : Real) (band : SectionSixStateBand) : Real :=
  match band with
  | .low => sectionSixThetaOne epsilon
  | .high => 1 - sectionSixThetaTwo epsilon

/-- The exact fixed terminal-V walls when the first inner and residual
coordinates exist. -/
def sectionSixTerminalVFixedRegion
    {ell M : Nat} (epsilon delta : Real)
    (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    Set (Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) :=
  {x | (forall i, x (pattern.innerPositionEmbedding i) <=
        sectionSixThetaGap epsilon) ∧
      (forall i, sectionSixThetaGap epsilon <=
        x (pattern.sourcePositionEmbedding i)) ∧
      sectionSixTerminalVDisplayedSum pattern x <=
        sectionSixTerminalVCutoffExponent epsilon band +
          x (pattern.firstInnerPosition hinner) ∧
      match band with
      | .low =>
          sectionSixTerminalVSourceSum pattern x <
              sectionSixThetaOne epsilon ∧
            delta < x (pattern.firstInnerPosition hinner) ∧
            sectionSixThetaOne epsilon <
              sectionSixTerminalVDisplayedSum pattern x ∧
            x (pattern.firstInnerPosition hinner) <
              x (pattern.firstResidualPosition hresidual)
      | .high =>
          sectionSixThetaTwo epsilon <
              sectionSixTerminalVSourceSum pattern x ∧
            sectionSixTerminalVSourceSum pattern x <
              1 - sectionSixThetaTwo epsilon ∧
            delta < x (pattern.firstInnerPosition hinner) ∧
            1 - sectionSixThetaTwo epsilon <
              sectionSixTerminalVDisplayedSum pattern x ∧
            x (pattern.firstInnerPosition hinner) <
              x (pattern.firstResidualPosition hresidual)}

/-- Raw terminal-V affine carrier. Invalid zero inner or residual arities give
the empty set because the strict walls refer to their first coordinates. -/
def sectionSixTerminalVStableTargetRegion
    {ell M : Nat} (epsilon delta : Real)
    (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    Set (Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) := by
  classical
  exact if hinner : 0 < pattern.1.1 then
    if hresidual : 0 < pattern.2.1.1 then
      typeIIExponentSimplex delta ∩
        (typeIIAffineEmbeddingPreimageRegion
            pattern.sourcePositionEmbedding sourceRegion ∩
          sectionSixTerminalVFixedRegion epsilon delta band pattern
            hinner hresidual)
    else ∅
  else ∅

/-- Target membership exposes the exact strict and weak terminal-V walls. -/
@[simp] theorem mem_sectionSixTerminalVStableTargetRegion
    {epsilon delta : Real} {ell M : Nat}
    {sourceRegion : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    {pattern : SectionSixTerminalVStablePattern ell M}
    {x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real} :
    x ∈ sectionSixTerminalVStableTargetRegion
        epsilon delta sourceRegion band pattern ↔
      ∃ hinner : 0 < pattern.1.1, ∃ hresidual : 0 < pattern.2.1.1,
        x ∈ typeIIExponentSimplex delta ∧
        (fun i => x (pattern.sourcePositionEmbedding i)) ∈ sourceRegion ∧
        (forall i, x (pattern.innerPositionEmbedding i) <=
          sectionSixThetaGap epsilon) ∧
        (forall i, sectionSixThetaGap epsilon <=
          x (pattern.sourcePositionEmbedding i)) ∧
        sectionSixTerminalVDisplayedSum pattern x <=
          sectionSixTerminalVCutoffExponent epsilon band +
            x (pattern.firstInnerPosition hinner) ∧
        match band with
        | .low =>
            sectionSixTerminalVSourceSum pattern x <
                sectionSixThetaOne epsilon ∧
              delta < x (pattern.firstInnerPosition hinner) ∧
              sectionSixThetaOne epsilon <
                sectionSixTerminalVDisplayedSum pattern x ∧
              x (pattern.firstInnerPosition hinner) <
                x (pattern.firstResidualPosition hresidual)
        | .high =>
            sectionSixThetaTwo epsilon <
                sectionSixTerminalVSourceSum pattern x ∧
              sectionSixTerminalVSourceSum pattern x <
                1 - sectionSixThetaTwo epsilon ∧
              delta < x (pattern.firstInnerPosition hinner) ∧
              1 - sectionSixThetaTwo epsilon <
                sectionSixTerminalVDisplayedSum pattern x ∧
              x (pattern.firstInnerPosition hinner) <
                x (pattern.firstResidualPosition hresidual) := by
  classical
  unfold sectionSixTerminalVStableTargetRegion
  split
  next hinner =>
    split
    next hresidual =>
      simp only [Set.mem_inter_iff, typeIIAffineEmbeddingPreimageRegion]
      constructor
      · rintro ⟨hsimplex, hsource, hfixed⟩
        exact ⟨hinner, hresidual, hsimplex, hsource, hfixed⟩
      · rintro ⟨_hinner, _hresidual, hsimplex, hsource, hfixed⟩
        exact ⟨hsimplex, hsource, hfixed⟩
    next hresidual =>
      simp only [Set.mem_empty_iff_false]
      constructor
      · intro hfalse
        exact hfalse.elim
      · rintro ⟨_hinner, hresidual', _⟩
        exact hresidual hresidual'
  next hinner =>
    simp only [Set.mem_empty_iff_false]
    constructor
    · intro hfalse
      exact hfalse.elim
    · rintro ⟨hinner', _⟩
      exact hinner hinner'

/-- With positive arities, the total wrapper is definitionally the exact
simplex/source/fixed-wall intersection. -/
theorem sectionSixTerminalVStableTargetRegion_eq_positiveCore
    {epsilon delta : Real} {ell M : Nat}
    {sourceRegion : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    {pattern : SectionSixTerminalVStablePattern ell M}
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    sectionSixTerminalVStableTargetRegion
        epsilon delta sourceRegion band pattern =
      typeIIExponentSimplex delta ∩
        (typeIIAffineEmbeddingPreimageRegion
            pattern.sourcePositionEmbedding sourceRegion ∩
          sectionSixTerminalVFixedRegion epsilon delta band pattern
            hinner hresidual) := by
  classical
  simp [sectionSixTerminalVStableTargetRegion, hinner, hresidual]

/-- Every terminal-V stable target is contained in its ordered delta-simplex. -/
theorem sectionSixTerminalVStableTargetRegion_isTypeIISourceRegion
    (epsilon delta : Real) {ell M : Nat}
    (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    IsTypeIISourceRegion delta
      (sectionSixTerminalVStableTargetRegion
        epsilon delta sourceRegion band pattern) := by
  intro x hx
  exact (mem_sectionSixTerminalVStableTargetRegion.mp hx).2.2.1

end

end PrimesRestrictedDigits
