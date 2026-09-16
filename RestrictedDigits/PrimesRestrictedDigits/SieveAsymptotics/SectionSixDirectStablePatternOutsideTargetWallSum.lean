import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternLocalWallSupportMass

/-!
# Outside-target wall sums for one direct stable pattern

This combines the restricted and density-weighted ambient forward wall charges for one fixed
stable pattern. See `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 150--152, and Proposition 7.2, pp.
163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- If the ambient fixed-pattern fiber is empty, both carrier-specific
outside-target value-image charges vanish. -/
theorem sectionSixDirectStablePatternOutsideTargetCharge_eq_zero_of_ambient_empty
    (epsilon delta rho : Real) (digit : Fin 10) (ell length M : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let ambientFiber := sectionSixDirectNearCandidatesOfStablePattern
      epsilon delta rho ell region length band B M pattern
    let targetSupport := typeIIOriginalRegionSupport XNat
      (sectionSixDirectStableTargetRegion epsilon delta region band pattern)
    let targetA := targetSupport.filter (fun m => m ∈ A)
    let targetB := targetSupport.filter (fun m => m ∈ B)
    let imageA := sectionSixDirectNearValueImageOfStablePattern epsilon delta
      rho ell region length band A M pattern
    let imageB := sectionSixDirectNearValueImageOfStablePattern epsilon delta
      rho ell region length band B M pattern
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * (A.card : Real) / X
    let outsideCharge : Real :=
      ((imageA \ targetA).card : Real) +
        lambda * ((imageB \ targetB).card : Real)
    ambientFiber = ∅ -> outsideCharge = 0 := by
  dsimp only
  intro hEmpty
  have hAfilter :=
    sectionSixDirectNearCandidatesOfStablePattern_eq_filter_of_subset
      (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length)
      epsilon delta rho ell region length band M pattern
  rw [hEmpty] at hAfilter
  simp only [Finset.filter_empty] at hAfilter
  have hAimage :
      sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
        region length band (paddedRestrictedNumbers digit length) M pattern =
          ∅ := by
    unfold sectionSixDirectNearValueImageOfStablePattern
    rw [hAfilter]
    simp only [Finset.image_empty]
  have hBimage :
      sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
        region length band
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) M pattern =
            ∅ := by
    unfold sectionSixDirectNearValueImageOfStablePattern
    rw [hEmpty]
    simp only [Finset.image_empty]
  rw [hAimage, hBimage]
  simp

set_option maxHeartbeats 2400000 in
/-- On a nonempty ambient fixed-pattern fiber, the combined restricted and
density-weighted ambient outside-target charge is bounded by the exact finite
sum of the literal-wall factors supplied by the local wall-mass theorem. -/
theorem exists_sectionSixDirectStablePatternOutsideTargetCharge_delta_upper_of_nonempty
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
            let ambientFiber := sectionSixDirectNearCandidatesOfStablePattern
              epsilon delta rho ell region length band B M pattern
            let targetSupport := typeIIOriginalRegionSupport XNat
              (sectionSixDirectStableTargetRegion epsilon delta region band pattern)
            let targetA := targetSupport.filter (fun m => m ∈ A)
            let targetB := targetSupport.filter (fun m => m ∈ B)
            let imageA := sectionSixDirectNearValueImageOfStablePattern
              epsilon delta rho ell region length band A M pattern
            let imageB := sectionSixDirectNearValueImageOfStablePattern
              epsilon delta rho ell region length band B M pattern
            let lambda : Real :=
              (restrictedDigitDensity digit : Real) * (A.card : Real) / X
            let outsideCharge : Real :=
              ((imageA \ targetA).card : Real) +
                lambda * ((imageB \ targetB).card : Real)
            epsilon <= 1 / 64 ->
            delta < sectionSixThetaGap epsilon ->
            rho ^ 2 < delta ->
            2 * rho <= delta / 2 ->
            rho ^ 2 + (((ell + pattern.1.1 : Nat) : Real) * rho) <= epsilon ->
            ambientFiber.Nonempty ->
            ∃ n : Nat, ∃ hdimension : ell + pattern.1.1 = n + 1,
              let wallFactor : Fin P.constraintCount -> Real := fun j =>
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
                rho + (2 : Real) ^ n *
                  (2 * gamma /
                      |normal (typeIIAffineMaxAbsCoordinate normal)| +
                    ((4 * (n + 1) + 2 : Nat) : Real) * rho)
              outsideCharge <=
                Cdelta *
                  ((∑ j : Fin P.constraintCount, wallFactor j) *
                    (A.card : Real) / Real.log X) := by
  obtain ⟨Cdelta, hCdelta, hmass⟩ :=
    exists_sectionSixDirectStablePatternLocalWallSupportMass_delta_upper
      delta hdelta
  obtain ⟨scaleLength, _hscaleLength, hscaleAt⟩ :=
    exists_typeIIWeakSmallProductScaleThreshold
  refine ⟨Cdelta, hCdelta, ?_⟩
  intro epsilon hepsilon
  obtain ⟨massLength, hmassLength, hmassAt⟩ := hmass epsilon hepsilon
  refine ⟨max massLength scaleLength,
    hmassLength.trans (le_max_left _ _), ?_⟩
  intro length hlength digit ell M region band sourcePresentation pattern
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth hconvenienceWidth
    hnonempty
  have hmassLengthAt : massLength <= length :=
    (le_max_left massLength scaleLength).trans hlength
  have hscaleLengthAt : scaleLength <= length :=
    (le_max_right massLength scaleLength).trans hlength
  have hlengthOne : 1 <= length := hmassLength.trans hmassLengthAt
  have hscale := hscaleAt length hscaleLengthAt
  dsimp only at hscale
  have hrho : 0 < majorArcM2LogLogDelta (10 ^ length) := hscale.2.1
  obtain ⟨n, hdimension, hwall⟩ :=
    hmassAt length hmassLengthAt digit ell M region band sourcePresentation
      pattern hepsilonSmall hdeltaGapStrict hrhoSq hnonempty
  refine ⟨n, hdimension, ?_⟩
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let P := sectionSixDirectDisplayedBandPresentation
    sourcePresentation epsilon delta band
  let targetSupport := typeIIOriginalRegionSupport XNat
    (sectionSixDirectStableTargetRegion epsilon delta region band pattern)
  let targetA := targetSupport.filter (fun m => m ∈ A)
  let targetB := targetSupport.filter (fun m => m ∈ B)
  let imageA := sectionSixDirectNearValueImageOfStablePattern epsilon delta rho
    ell region length band A M pattern
  let imageB := sectionSixDirectNearValueImageOfStablePattern epsilon delta rho
    ell region length band B M pattern
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let outsideCharge : Real :=
    ((imageA \ targetA).card : Real) +
      lambda * ((imageB \ targetB).card : Real)
  let anchors := fun j : Fin P.constraintCount =>
    sectionSixDirectStablePatternLocalCrossedWallAnchors epsilon delta rho
      sourcePresentation band pattern j
  let supportCount : (Fin (ell + pattern.1.1) -> Nat) -> Finset Nat -> Real :=
    fun anchor C => typeIICellSupportCount XNat
      (scaledNaturalCubeAnchor rho anchor) rho delta C
  let embedding : Fin (ell + 1) ↪ Fin (n + 2) :=
    pattern.canonicalDisplayedEmbedding.trans
      (Fin.castOrderIso
        (congrArg (fun k : Nat => k + 1) hdimension)).toEquiv.toEmbedding
  let normal := fun j : Fin P.constraintCount =>
    typeIIProjectedAffineNormal
      (typeIIAffineLiftNormal embedding (P.normal j))
  let gamma := fun j : Fin P.constraintCount =>
    rho ^ 2 * typeIIAffineNormalMass (P.normal j)
  let wallFactor := fun j : Fin P.constraintCount =>
    rho + (2 : Real) ^ n *
      (2 * gamma j /
          |normal j (typeIIAffineMaxAbsCoordinate (normal j))| +
        ((4 * (n + 1) + 2 : Nat) : Real) * rho)
  change outsideCharge <=
    Cdelta * ((∑ j : Fin P.constraintCount, wallFactor j) *
      (A.card : Real) / Real.log X)
  have hA := card_sectionSixDirectNearValueImage_sdiff_target_le_localWallCharges
    (sourcePresentation := sourcePresentation) (band := band) A pattern hepsilon
      hepsilonSmall hlengthOne hdeltaGapStrict hrho hmarginWidth
      hconvenienceWidth
  have hB := card_sectionSixDirectNearValueImage_sdiff_target_le_localWallCharges
    (sourcePresentation := sourcePresentation) (band := band) B pattern hepsilon
      hepsilonSmall hlengthOne hdeltaGapStrict hrho hmarginWidth
      hconvenienceWidth
  have hXpos : 0 < X := by
    dsimp only [X, XNat]
    linarith [hscale.1]
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact div_nonneg
      (mul_nonneg (restrictedDigitDensity_nonneg digit)
        (Nat.cast_nonneg A.card)) hXpos.le
  have hcombined : outsideCharge <=
      (∑ j, ∑ anchor ∈ anchors j, supportCount anchor A) +
        lambda *
          (∑ j, ∑ anchor ∈ anchors j, supportCount anchor B) := by
    dsimp only [outsideCharge]
    exact add_le_add
      (by simpa only [imageA, targetA, targetSupport, anchors, supportCount, A,
          XNat, rho] using hA)
      (mul_le_mul_of_nonneg_left
        (by simpa only [imageB, targetB, targetSupport, anchors, supportCount,
            B, XNat, X, rho] using hB)
        hlambda)
  calc
    outsideCharge <=
        (∑ j, ∑ anchor ∈ anchors j, supportCount anchor A) +
          lambda *
            (∑ j, ∑ anchor ∈ anchors j, supportCount anchor B) := hcombined
    _ = ∑ j, ∑ anchor ∈ anchors j,
          (supportCount anchor A + lambda * supportCount anchor B) := by
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ <= ∑ j, Cdelta *
          (wallFactor j * (A.card : Real) / Real.log X) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [anchors, supportCount, lambda, wallFactor, embedding,
        normal, gamma, P, A, B, XNat, X, rho] using hwall j
    _ = Cdelta *
          ((∑ j : Fin P.constraintCount, wallFactor j) *
            (A.card : Real) / Real.log X) := by
      calc
        (∑ j, Cdelta *
            (wallFactor j * (A.card : Real) / Real.log X)) =
            ∑ j, (Cdelta * (A.card : Real) / Real.log X) * wallFactor j := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (Cdelta * (A.card : Real) / Real.log X) *
            ∑ j, wallFactor j := by
          rw [Finset.mul_sum]
        _ = _ := by ring

end

end PrimesRestrictedDigits
