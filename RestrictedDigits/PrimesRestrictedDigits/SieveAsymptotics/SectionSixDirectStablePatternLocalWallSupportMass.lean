import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternLocalWallCharges
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectDisplayedWallSupportMass

/-!
# Local support mass for one direct stable-pattern wall

This composes the realized-pattern geometry and local wall anchors with the positive
support-mass estimate for one displayed wall. See `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp.
150--152, and Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- A realized direct stable pattern has a common positive predecessor
dimension on which every literal displayed wall satisfies the one-wall
support-mass bound. -/
theorem exists_sectionSixDirectStablePatternLocalWallSupportMass_delta_upper
    (delta : Real) (hdelta : 0 < delta) :
    ∃ Cdelta : Real, 0 < Cdelta ∧
      ∀ epsilon : Real, 0 < epsilon ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
          ∀ (digit : Fin 10) (ell M : Nat)
            (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand)
            (sourcePresentation : TypeIIAffineHalfspacePresentation region)
            (pattern : SectionSixDirectStablePattern ell M),
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let rho : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let P := sectionSixDirectDisplayedBandPresentation
              sourcePresentation epsilon delta band
            let supportCount :
                (Fin (ell + pattern.1.1) -> Nat) -> Finset Nat -> Real :=
              fun anchor C => typeIICellSupportCount XNat
                (scaledNaturalCubeAnchor rho anchor) rho delta C
            epsilon <= 1 / 64 ->
            delta < sectionSixThetaGap epsilon ->
            rho ^ 2 < delta ->
            (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
              region length band B M pattern).Nonempty ->
            ∃ n : Nat, ∃ hdimension : ell + pattern.1.1 = n + 1,
              ∀ j : Fin P.constraintCount,
                let embedding : Fin (ell + 1) ↪ Fin (n + 2) :=
                  pattern.canonicalDisplayedEmbedding.trans
                    (Fin.castOrderIso
                      (congrArg (fun k : Nat => k + 1)
                        hdimension)).toEquiv.toEmbedding
                let normal : Fin (n + 1) -> Real :=
                  typeIIProjectedAffineNormal
                    (typeIIAffineLiftNormal embedding (P.normal j))
                let gamma : Real :=
                  rho ^ 2 * typeIIAffineNormalMass (P.normal j)
                (sectionSixDirectStablePatternLocalCrossedWallAnchors
                    epsilon delta rho sourcePresentation band pattern j).sum
                      (fun anchor =>
                        supportCount anchor A +
                          (restrictedDigitDensity digit : Real) *
                            (A.card : Real) / X * supportCount anchor B) <=
                  Cdelta *
                    ((rho + (2 : Real) ^ n *
                        (2 * gamma /
                            |normal (typeIIAffineMaxAbsCoordinate normal)| +
                          ((4 * (n + 1) + 2 : Nat) : Real) * rho)) *
                      (A.card : Real) / Real.log X) := by
  obtain ⟨Cdelta, hCdelta, hwall⟩ :=
    exists_sectionSixDirectDisplayedWallSupportMass_delta_upper delta hdelta
  obtain ⟨scaleLength, _hscaleLength, hscaleAt⟩ :=
    exists_typeIIWeakSmallProductScaleThreshold
  refine ⟨Cdelta, hCdelta, ?_⟩
  intro epsilon hepsilon
  obtain ⟨wallLength, hwallLength, hwallAt⟩ := hwall epsilon hepsilon
  refine ⟨max wallLength scaleLength,
    hwallLength.trans (le_max_left _ _), ?_⟩
  intro length hlength digit ell M region band sourcePresentation pattern
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hrhoSq hnonempty
  have hwallLengthAt : wallLength <= length :=
    (le_max_left wallLength scaleLength).trans hlength
  have hscaleLengthAt : scaleLength <= length :=
    (le_max_right wallLength scaleLength).trans hlength
  have hlengthOne : 1 <= length := hwallLength.trans hwallLengthAt
  obtain ⟨candidate, hcandidate⟩ := hnonempty
  have hrealized := sectionSixDirectStablePattern_realizedData_of_mem
    hepsilon hepsilonSmall hlengthOne hdelta hdeltaGapStrict hrhoSq hcandidate
  rcases pattern with ⟨⟨r, hr⟩, positions⟩
  have hresidual : 0 < r := hrealized.1
  have harity := hrealized.2.1
  obtain ⟨s, hs⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hresidual)
  subst r
  refine ⟨ell + s, rfl, ?_⟩
  intro j
  dsimp only
  let currentPattern : SectionSixDirectStablePattern ell M :=
    ⟨⟨s + 1, hr⟩, positions⟩
  let P := sectionSixDirectDisplayedBandPresentation
    sourcePresentation epsilon delta band
  let anchors := sectionSixDirectStablePatternLocalCrossedWallAnchors
    epsilon delta (majorArcM2LogLogDelta (10 ^ length)) sourcePresentation band
      currentPattern j
  let embedding : Fin (ell + 1) ↪ Fin ((ell + s) + 2) :=
    currentPattern.canonicalDisplayedEmbedding
  let normal : Fin ((ell + s) + 1) -> Real :=
    typeIIProjectedAffineNormal
      (typeIIAffineLiftNormal embedding (P.normal j))
  by_cases hnormal : normal ≠ 0
  · have hK := hwallAt length hwallLengthAt digit ell (ell + s) region band
      sourcePresentation embedding j anchors
    dsimp only at hK
    apply hK hnormal
    · simpa only [Nat.add_assoc] using harity
    · intro anchor hanchor
      exact
        (mem_sectionSixDirectStablePatternLocalCrossedWallAnchors.mp hanchor).1
    · intro anchor hanchor i
      exact
        (mem_sectionSixDirectStablePatternLocalCrossedWallAnchors.mp hanchor).2.1 i
    · intro anchor hanchor
      exact
        (mem_sectionSixDirectStablePatternLocalCrossedWallAnchors.mp hanchor).2.2.1
    · intro anchor hanchor
      exact
        (mem_sectionSixDirectStablePatternLocalCrossedWallAnchors.mp hanchor).2.2.2
  · have hnormalZero : normal = 0 := not_ne_iff.mp hnormal
    have hembedding :
        currentPattern.canonicalDisplayedEmbedding.trans
          (Fin.castOrderIso
            (congrArg (fun k : Nat => k + 1)
              (rfl : ell + currentPattern.1.1 = (ell + s) + 1))).toEquiv.toEmbedding =
        currentPattern.canonicalDisplayedEmbedding := by
      ext i
      rfl
    have htransportedNormalZero :
        typeIIProjectedAffineNormal
          (typeIIAffineLiftNormal
            (currentPattern.canonicalDisplayedEmbedding.trans
              (Fin.castOrderIso
                (congrArg (fun k : Nat => k + 1)
                  (rfl : ell + currentPattern.1.1 =
                    (ell + s) + 1))).toEquiv.toEmbedding)
            (P.normal j)) = 0 := by
      rw [hembedding]
      exact hnormalZero
    have hanchorsEmpty : anchors = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hanchorsNonempty
      obtain ⟨anchor, hanchor⟩ := hanchorsNonempty
      have hslab :=
        (mem_sectionSixDirectStablePatternLocalCrossedWallAnchors.mp hanchor).1
      have hnativeNormal :
          typeIIProjectedAffineNormal
            (typeIIAffineLiftNormal currentPattern.canonicalDisplayedEmbedding
              (P.normal j)) ≠ 0 :=
        (mem_typeIIAffineThickSlabAnchors.mp hslab).2.1
      exact hnormal hnativeNormal
    have hscale := hscaleAt length hscaleLengthAt
    dsimp only at hscale
    have hrho : 0 < majorArcM2LogLogDelta (10 ^ length) := hscale.2.1
    have hXone : (1 : Real) < ((10 ^ length : Nat) : Real) :=
      lt_of_lt_of_le (by norm_num) hscale.1
    have hlog : 0 < Real.log (((10 ^ length : Nat) : Real)) :=
      Real.log_pos hXone
    rw [show sectionSixDirectStablePatternLocalCrossedWallAnchors
      epsilon delta (majorArcM2LogLogDelta (10 ^ length)) sourcePresentation band
        currentPattern j = ∅ by exact hanchorsEmpty]
    simp only [Finset.sum_empty]
    rw [htransportedNormalZero]
    simp only [Pi.zero_apply, abs_zero, div_zero, zero_add]
    positivity

end

end PrimesRestrictedDigits
