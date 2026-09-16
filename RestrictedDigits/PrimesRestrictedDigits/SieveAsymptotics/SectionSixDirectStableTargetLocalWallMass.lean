import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetReverseCoverCardinality
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternCanonicalWallCoefficient

/-!
# Active direct stable-target local-wall mass

The Sigma-indexed target-side wall carrier is bounded by the existing patternwise cell-support
mass, with one log-log width and the canonical finite wall coefficient sum.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- The combined restricted and density-weighted ambient active local-wall
charge has the same eventual mass bound as the underlying wall cells. -/
theorem exists_sectionSixDirectActiveStableLocalWallCharge_delta_upper
    (delta : Real) (hdelta : 0 < delta) :
    ∃ Cdelta : Real, 0 < Cdelta ∧
      ∀ epsilon : Real, 0 < epsilon ->
        ∀ (ell M : Nat) (region : Set (Fin ell -> Real))
          (band : SectionSixDirectBand)
          (sourcePresentation : TypeIIAffineHalfspacePresentation region),
          ∃ length0 : Nat, 1 <= length0 ∧
            ∀ length : Nat, length0 <= length ->
            ∀ digit : Fin 10,
              let XNat : Nat := 10 ^ length
              let X : Real := (XNat : Real)
              let rho : Real := majorArcM2LogLogDelta XNat
              let A : Finset Nat := paddedRestrictedNumbers digit length
              let B : Finset Nat := maynardAmbientCarrier X
              let lambda : Real :=
                (restrictedDigitDensity digit : Real) * (A.card : Real) / X
              let wallCount : Finset Nat -> Real := fun C =>
                ((sectionSixDirectActiveStableLocalWallValues epsilon delta rho
                  ell region length sourcePresentation band B C M).card : Real)
              epsilon <= 1 / 64 ->
              delta < sectionSixThetaGap epsilon ->
              rho ^ 2 < delta ->
              wallCount A + lambda * wallCount B <=
                Cdelta *
                  ((rho *
                      sectionSixDirectStablePatternCanonicalWallCoefficientSum
                        sourcePresentation epsilon delta band M) *
                    (A.card : Real) / Real.log X) := by
  obtain ⟨Cdelta, hCdelta, hmass⟩ :=
    exists_sectionSixDirectStablePatternLocalWallSupportMass_delta_upper
      delta hdelta
  obtain ⟨scaleLength, hscaleLength, hscaleAt⟩ :=
    exists_typeIIWeakSmallProductScaleThreshold
  refine ⟨Cdelta, hCdelta, ?_⟩
  intro epsilon hepsilon ell M region band sourcePresentation
  obtain ⟨massLength, hmassLength, hmassAt⟩ := hmass epsilon hepsilon
  refine ⟨max massLength scaleLength,
    hmassLength.trans (le_max_left _ _), ?_⟩
  intro length hlength digit
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hrhoSq
  have hmassLengthAt : massLength <= length :=
    (le_max_left massLength scaleLength).trans hlength
  have hscaleLengthAt : scaleLength <= length :=
    (le_max_right massLength scaleLength).trans hlength
  have hscale := hscaleAt length hscaleLengthAt
  dsimp only at hscale
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let active := sectionSixDirectActiveStablePatterns epsilon delta rho ell region
    length band B M
  let P := sectionSixDirectDisplayedBandPresentation
    sourcePresentation epsilon delta band
  let anchors := fun pattern : SectionSixDirectStablePattern ell M =>
    fun j : Fin P.constraintCount =>
      sectionSixDirectStablePatternLocalCrossedWallAnchors epsilon delta rho
        sourcePresentation band pattern j
  let supportCount := fun pattern : SectionSixDirectStablePattern ell M =>
    fun anchor : Fin (ell + pattern.1.1) -> Nat => fun C : Finset Nat =>
      typeIICellSupportCount XNat (scaledNaturalCubeAnchor rho anchor) rho delta C
  let wallCount : Finset Nat -> Real := fun C =>
    ((sectionSixDirectActiveStableLocalWallValues epsilon delta rho ell region
      length sourcePresentation band B C M).card : Real)
  have hrho : 0 < rho := by
    simpa only [rho, XNat] using hscale.2.1
  have hrhoOne : rho <= 1 := by
    simpa only [rho, XNat] using
      hscale.2.2.1.trans (by norm_num : (1 / 2 : Real) <= 1)
  have hXOne : 1 < X := by
    dsimp only [X, XNat]
    linarith [hscale.1]
  have hlog : 0 < Real.log X := Real.log_pos hXOne
  have hmassNonneg : 0 <= (A.card : Real) / Real.log X := by positivity
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact div_nonneg
      (mul_nonneg (restrictedDigitDensity_nonneg digit)
        (Nat.cast_nonneg A.card)) (zero_lt_one.trans hXOne).le
  have hAcard :=
    card_sectionSixDirectActiveStableLocalWallValues_le_sum_cellSupports
      epsilon delta rho ell region length sourcePresentation band B A M
  have hBcard :=
    card_sectionSixDirectActiveStableLocalWallValues_le_sum_cellSupports
      epsilon delta rho ell region length sourcePresentation band B B M
  have hA : wallCount A <=
      ∑ pattern ∈ active, ∑ j : Fin P.constraintCount,
        ∑ anchor ∈ anchors pattern j, supportCount pattern anchor A := by
    dsimp only [wallCount, active, P, anchors, supportCount,
      typeIICellSupportCount, XNat, X, rho, A, B]
    exact_mod_cast hAcard
  have hB : wallCount B <=
      ∑ pattern ∈ active, ∑ j : Fin P.constraintCount,
        ∑ anchor ∈ anchors pattern j, supportCount pattern anchor B := by
    dsimp only [wallCount, active, P, anchors, supportCount,
      typeIICellSupportCount, XNat, X, rho, A, B]
    exact_mod_cast hBcard
  have hcombined : wallCount A + lambda * wallCount B <=
      ∑ pattern ∈ active, ∑ j : Fin P.constraintCount,
        ∑ anchor ∈ anchors pattern j,
          (supportCount pattern anchor A +
            lambda * supportCount pattern anchor B) := by
    calc
      wallCount A + lambda * wallCount B <=
          (∑ pattern ∈ active, ∑ j : Fin P.constraintCount,
            ∑ anchor ∈ anchors pattern j, supportCount pattern anchor A) +
          lambda * (∑ pattern ∈ active, ∑ j : Fin P.constraintCount,
            ∑ anchor ∈ anchors pattern j, supportCount pattern anchor B) :=
        add_le_add hA (mul_le_mul_of_nonneg_left hB hlambda)
      _ = ∑ pattern ∈ active, ∑ j : Fin P.constraintCount,
          ∑ anchor ∈ anchors pattern j,
            (supportCount pattern anchor A +
              lambda * supportCount pattern anchor B) := by
        simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have hcanonicalNonneg (pattern : SectionSixDirectStablePattern ell M) :
      0 <= sectionSixDirectStablePatternCanonicalWallCoefficient
        sourcePresentation epsilon delta band pattern := by
    unfold sectionSixDirectStablePatternCanonicalWallCoefficient
    split
    · exact le_rfl
    · exact sectionSixDirectStablePatternWallCoefficient_nonneg
        sourcePresentation epsilon delta band pattern
          (ell + pattern.1.1).pred _
  have hpatternBound (pattern : SectionSixDirectStablePattern ell M)
      (hpattern : pattern ∈ active) :
      (∑ j : Fin P.constraintCount,
        ∑ anchor ∈ anchors pattern j,
          (supportCount pattern anchor A +
            lambda * supportCount pattern anchor B)) <=
        Cdelta *
          ((rho * sectionSixDirectStablePatternCanonicalWallCoefficient
              sourcePresentation epsilon delta band pattern) *
            (A.card : Real) / Real.log X) := by
    have hnonempty :
        (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band B M pattern).Nonempty := by
      simpa only [active, sectionSixDirectActiveStablePatterns,
        Finset.mem_filter, Finset.mem_univ, true_and] using hpattern
    obtain ⟨n, hdimension, hwall⟩ :=
      hmassAt length hmassLengthAt digit ell M region band sourcePresentation
        pattern hepsilonSmall hdeltaGapStrict hrhoSq hnonempty
    have hfactor :=
      sum_sectionSixDirectStablePatternWallFactor_le_rho_mul_coefficient
        sourcePresentation epsilon delta rho band pattern n hdimension
          hrho.le hrhoOne
    have hcanonical :=
      sectionSixDirectStablePatternCanonicalWallCoefficient_eq_raw
        sourcePresentation epsilon delta band pattern n hdimension
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
    have hfactor' : (∑ j : Fin P.constraintCount, wallFactor j) <=
        rho * sectionSixDirectStablePatternWallCoefficient
          sourcePresentation epsilon delta band pattern n hdimension := by
      simpa only [P, embedding, normal, gamma, wallFactor] using hfactor
    calc
      (∑ j : Fin P.constraintCount,
          ∑ anchor ∈ anchors pattern j,
            (supportCount pattern anchor A +
              lambda * supportCount pattern anchor B)) <=
          ∑ j : Fin P.constraintCount,
            Cdelta *
              (wallFactor j * (A.card : Real) / Real.log X) := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [anchors, supportCount, lambda, wallFactor, embedding,
          normal, gamma, P, A, B, XNat, X, rho] using hwall j
      _ = Cdelta *
          ((∑ j : Fin P.constraintCount, wallFactor j) *
            (A.card : Real) / Real.log X) := by
        calc
          (∑ j : Fin P.constraintCount,
              Cdelta * (wallFactor j * (A.card : Real) / Real.log X)) =
              ∑ j : Fin P.constraintCount,
                (Cdelta * (A.card : Real) / Real.log X) * wallFactor j := by
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = (Cdelta * (A.card : Real) / Real.log X) *
              ∑ j : Fin P.constraintCount, wallFactor j := by
            rw [Finset.mul_sum]
          _ = _ := by ring
      _ <= Cdelta *
          ((rho * sectionSixDirectStablePatternWallCoefficient
              sourcePresentation epsilon delta band pattern n hdimension) *
            (A.card : Real) / Real.log X) := by
        gcongr
      _ = Cdelta *
          ((rho * sectionSixDirectStablePatternCanonicalWallCoefficient
              sourcePresentation epsilon delta band pattern) *
            (A.card : Real) / Real.log X) := by
        rw [hcanonical]
  calc
    wallCount A + lambda * wallCount B <=
        ∑ pattern ∈ active, ∑ j : Fin P.constraintCount,
          ∑ anchor ∈ anchors pattern j,
            (supportCount pattern anchor A +
              lambda * supportCount pattern anchor B) := hcombined
    _ <= ∑ pattern ∈ active,
        Cdelta *
          ((rho * sectionSixDirectStablePatternCanonicalWallCoefficient
              sourcePresentation epsilon delta band pattern) *
            (A.card : Real) / Real.log X) := by
      exact Finset.sum_le_sum fun pattern hpattern =>
        hpatternBound pattern hpattern
    _ <= ∑ pattern : SectionSixDirectStablePattern ell M,
        Cdelta *
          ((rho * sectionSixDirectStablePatternCanonicalWallCoefficient
              sourcePresentation epsilon delta band pattern) *
            (A.card : Real) / Real.log X) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ active)
      intro pattern _ _
      exact mul_nonneg hCdelta.le
        (div_nonneg
          (mul_nonneg (mul_nonneg hrho.le (hcanonicalNonneg pattern))
            (Nat.cast_nonneg A.card)) hlog.le)
    _ = Cdelta *
        ((rho *
            sectionSixDirectStablePatternCanonicalWallCoefficientSum
              sourcePresentation epsilon delta band M) *
          (A.card : Real) / Real.log X) := by
      unfold sectionSixDirectStablePatternCanonicalWallCoefficientSum
      calc
        (∑ pattern : SectionSixDirectStablePattern ell M,
            Cdelta *
              ((rho * sectionSixDirectStablePatternCanonicalWallCoefficient
                  sourcePresentation epsilon delta band pattern) *
                (A.card : Real) / Real.log X)) =
            ∑ pattern : SectionSixDirectStablePattern ell M,
              (Cdelta * rho * (A.card : Real) / Real.log X) *
                sectionSixDirectStablePatternCanonicalWallCoefficient
                  sourcePresentation epsilon delta band pattern := by
          apply Finset.sum_congr rfl
          intro pattern _
          ring
        _ = (Cdelta * rho * (A.card : Real) / Real.log X) *
            ∑ pattern : SectionSixDirectStablePattern ell M,
              sectionSixDirectStablePatternCanonicalWallCoefficient
                sourcePresentation epsilon delta band pattern := by
          rw [Finset.mul_sum]
        _ = _ := by ring

end

end PrimesRestrictedDigits
