import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternCanonicalWallCoefficient

/-!
# Finite direct stable-pattern outside-target charges

This sums the positive restricted and density-weighted ambient boundary charge over all stable
patterns and extracts the common varying Type II width. See `MAYNARD-PRD-PUBLISHED`, Lemma
7.3, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The carrier-specific positive outside-target charge for one direct stable
pattern. -/
noncomputable def sectionSixDirectStablePatternOutsideTargetCharge
    (epsilon delta rho : Real) (digit : Fin 10) (ell length M : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M) : Real :=
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
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
  ((imageA \ targetA).card : Real) +
    lambda * ((imageB \ targetB).card : Real)

/-- The sum of the positive outside-target charges over the full finite stable-
pattern type. -/
noncomputable def sectionSixDirectStablePatternOutsideTargetChargeSum
    (epsilon delta rho : Real) (digit : Fin 10) (ell length M : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand) : Real :=
  ∑ pattern : SectionSixDirectStablePattern ell M,
    sectionSixDirectStablePatternOutsideTargetCharge epsilon delta rho digit
      ell length M region band pattern

set_option maxHeartbeats 2400000 in
/-- For fixed presentation data, the complete finite positive pattern charge
is bounded by one varying width times the canonical pattern coefficient sum. -/
theorem exists_sectionSixDirectStablePatternOutsideTargetChargeSum_delta_upper
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
              epsilon <= 1 / 64 ->
              delta < sectionSixThetaGap epsilon ->
              rho ^ 2 < delta ->
              2 * rho <= delta / 2 ->
              rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon ->
              sectionSixDirectStablePatternOutsideTargetChargeSum epsilon delta
                  rho digit ell length M region band <=
                Cdelta *
                  ((rho *
                      sectionSixDirectStablePatternCanonicalWallCoefficientSum
                        sourcePresentation epsilon delta band M) *
                    (A.card : Real) / Real.log X) := by
  obtain ⟨Cdelta, hCdelta, hmass⟩ :=
    exists_sectionSixDirectStablePatternOutsideTargetCharge_delta_upper_of_nonempty
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
  intro hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
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
  have hrho : 0 < rho := by
    simpa only [rho, XNat] using hscale.2.1
  have hrhoOne : rho <= 1 := by
    have : rho <= 1 / 2 := by
      simpa only [rho, XNat] using hscale.2.2.1
    linarith
  have hXOne : (1 : Real) < X := by
    dsimp only [X, XNat]
    linarith [hscale.1]
  have hlog : 0 < Real.log X := Real.log_pos hXOne
  unfold sectionSixDirectStablePatternOutsideTargetChargeSum
  change
    (∑ pattern : SectionSixDirectStablePattern ell M,
      sectionSixDirectStablePatternOutsideTargetCharge epsilon delta rho digit
        ell length M region band pattern) <=
      Cdelta *
        ((rho *
            sectionSixDirectStablePatternCanonicalWallCoefficientSum
              sourcePresentation epsilon delta band M) *
          (A.card : Real) / Real.log X)
  calc
    (∑ pattern : SectionSixDirectStablePattern ell M,
        sectionSixDirectStablePatternOutsideTargetCharge epsilon delta rho digit
          ell length M region band pattern) <=
        ∑ pattern : SectionSixDirectStablePattern ell M,
          Cdelta *
            ((rho * sectionSixDirectStablePatternCanonicalWallCoefficient
                sourcePresentation epsilon delta band pattern) *
              (A.card : Real) / Real.log X) := by
      apply Finset.sum_le_sum
      intro pattern _
      let B : Finset Nat := maynardAmbientCarrier X
      let ambientFiber := sectionSixDirectNearCandidatesOfStablePattern
        epsilon delta rho ell region length band B M pattern
      by_cases hEmpty : ambientFiber = ∅
      · have hchargeZero :=
          sectionSixDirectStablePatternOutsideTargetCharge_eq_zero_of_ambient_empty
            epsilon delta rho digit ell length M region band pattern
        have hzero :
            sectionSixDirectStablePatternOutsideTargetCharge epsilon delta rho
                digit ell length M region band pattern = 0 := by
          simpa only [sectionSixDirectStablePatternOutsideTargetCharge,
            ambientFiber, B, X, XNat, A, rho] using hchargeZero hEmpty
        rw [hzero]
        have hcoefficient :
            0 <= sectionSixDirectStablePatternCanonicalWallCoefficient
              sourcePresentation epsilon delta band pattern := by
          unfold sectionSixDirectStablePatternCanonicalWallCoefficient
          split
          · exact le_rfl
          · exact sectionSixDirectStablePatternWallCoefficient_nonneg
              sourcePresentation epsilon delta band pattern
                (ell + pattern.1.1).pred _
        exact mul_nonneg hCdelta.le
          (div_nonneg
            (mul_nonneg (mul_nonneg hrho.le hcoefficient)
              (Nat.cast_nonneg A.card)) hlog.le)
      · have hnonempty : ambientFiber.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hEmpty
        have hresidual : pattern.1.1 <= M :=
          Nat.le_of_lt_succ pattern.1.2
        have hcast :
            ((ell + pattern.1.1 : Nat) : Real) <= ((ell + M : Nat) : Real) := by
          exact_mod_cast Nat.add_le_add_left hresidual ell
        have hpatternWidth :
            rho ^ 2 + (((ell + pattern.1.1 : Nat) : Real) * rho) <= epsilon := by
          calc
            rho ^ 2 + (((ell + pattern.1.1 : Nat) : Real) * rho) <=
                rho ^ 2 + (((ell + M : Nat) : Real) * rho) := by
              gcongr
            _ <= epsilon := hglobalWidth
        obtain ⟨n, hdimension, hcharge⟩ :=
          hmassAt length hmassLengthAt digit ell M region band
            sourcePresentation pattern hepsilonSmall hdeltaGapStrict hrhoSq
              hmarginWidth hpatternWidth hnonempty
        have hwall :=
          sum_sectionSixDirectStablePatternWallFactor_le_rho_mul_coefficient
            sourcePresentation epsilon delta rho band pattern n hdimension
              hrho.le hrhoOne
        have hcanonical :=
          sectionSixDirectStablePatternCanonicalWallCoefficient_eq_raw
            sourcePresentation epsilon delta band pattern n hdimension
        have hcharge' :
            sectionSixDirectStablePatternOutsideTargetCharge epsilon delta rho
                digit ell length M region band pattern <=
              Cdelta *
                ((rho * sectionSixDirectStablePatternWallCoefficient
                    sourcePresentation epsilon delta band pattern n hdimension) *
                  (A.card : Real) / Real.log X) := by
          let P := sectionSixDirectDisplayedBandPresentation
            sourcePresentation epsilon delta band
          let embedding : Fin (ell + 1) ↪ Fin (n + 2) :=
            pattern.canonicalDisplayedEmbedding.trans
              (Fin.castOrderIso
                (congrArg (fun k : Nat => k + 1) hdimension)).toEquiv.toEmbedding
          let wallFactor : Fin P.constraintCount -> Real := fun j =>
            let normal : Fin (n + 1) -> Real :=
              typeIIProjectedAffineNormal
                (typeIIAffineLiftNormal embedding (P.normal j))
            let gamma : Real :=
              rho ^ 2 * typeIIAffineNormalMass (P.normal j)
            rho + (2 : Real) ^ n *
              (2 * gamma /
                  |normal (typeIIAffineMaxAbsCoordinate normal)| +
                ((4 * (n + 1) + 2 : Nat) : Real) * rho)
          have hchargeRaw :
              sectionSixDirectStablePatternOutsideTargetCharge epsilon delta rho
                  digit ell length M region band pattern <=
                Cdelta *
                  ((∑ j : Fin P.constraintCount, wallFactor j) *
                    (A.card : Real) / Real.log X) := by
            simpa only [sectionSixDirectStablePatternOutsideTargetCharge,
              XNat, X, rho, A, B, ambientFiber, P, embedding, wallFactor] using
                hcharge
          have hwallRaw :
              (∑ j : Fin P.constraintCount, wallFactor j) <=
                rho * sectionSixDirectStablePatternWallCoefficient
                  sourcePresentation epsilon delta band pattern n hdimension := by
            simpa only [P, embedding, wallFactor] using hwall
          calc
            sectionSixDirectStablePatternOutsideTargetCharge epsilon delta rho
                digit ell length M region band pattern <=
                Cdelta *
                  ((∑ j : Fin P.constraintCount, wallFactor j) *
                    (A.card : Real) / Real.log X) := hchargeRaw
            _ <= Cdelta *
                ((rho * sectionSixDirectStablePatternWallCoefficient
                    sourcePresentation epsilon delta band pattern n hdimension) *
                  (A.card : Real) / Real.log X) := by
              gcongr
        simpa only [hcanonical] using hcharge'
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
