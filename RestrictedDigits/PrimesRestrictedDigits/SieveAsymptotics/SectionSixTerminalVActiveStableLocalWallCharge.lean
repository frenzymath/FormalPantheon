import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternCanonicalWallCoefficient
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternLocalWallSupportMass
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetReverseCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVActiveStablePatterns

/-!
# Active terminal-V stable-pattern local-wall charge

The exact patternwise wall term in the terminal-V signed ledger is bounded by the existing
support-mass estimate, one log-log width, and a fixed finite coefficient sum. See
`MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152, and Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- The complete restricted and density-weighted ambient active local-wall
charge has one varying log-log width and a fixed finite coefficient. -/
theorem exists_sectionSixTerminalVActiveStableLocalWallCharge_delta_upper
    (delta : Real) (hdelta : 0 < delta) :
    ∃ Cdelta : Real, 0 < Cdelta ∧
      ∀ (epsilon : Real) (hepsilon : 0 < epsilon),
        ∀ (ell M : Nat) (region : Set (Fin ell -> Real))
          (band : SectionSixStateBand)
          (sourcePresentation : TypeIIAffineHalfspacePresentation region),
          ∃ (length0 : Nat) (hlength0 : 1 <= length0),
            ∀ (length : Nat) (hlength : length0 <= length),
            ∀ digit : Fin 10,
              let XNat : Nat := 10 ^ length
              let X : Real := (XNat : Real)
              let rho : Real := majorArcM2LogLogDelta XNat
              let A : Finset Nat := paddedRestrictedNumbers digit length
              let B : Finset Nat := maynardAmbientCarrier X
              let lambda : Real :=
                (restrictedDigitDensity digit : Real) * (A.card : Real) / X
              let hlengthOne : 1 <= length := hlength0.trans hlength
              ∀ (hepsilonSmall : epsilon <= 1 / 64)
                (hdeltaGapStrict : delta < sectionSixThetaGap epsilon),
                let active := sectionSixTerminalVActiveStablePatterns
                  (rho := rho) region hepsilon hepsilonSmall hlengthOne
                    hdeltaGapStrict band B M
                let wall := fun C : Finset Nat =>
                  fun pattern : SectionSixTerminalVStablePattern ell M =>
                    sectionSixTerminalVStablePatternLocalWallValues
                      (length := length) epsilon delta rho sourcePresentation
                        band C pattern
                rho ^ 2 < delta ->
                (∑ pattern ∈ active,
                    (((wall A pattern).card : Real) +
                      lambda * ((wall B pattern).card : Real))) <=
                  Cdelta *
                    ((rho *
                        sectionSixTerminalVStablePatternCanonicalWallCoefficientSum
                          sourcePresentation epsilon delta band M) *
                      (A.card : Real) / Real.log X) := by
  obtain ⟨Cdelta, hCdelta, hmass⟩ :=
    exists_sectionSixTerminalVStablePatternLocalWallSupportMass_delta_upper
      delta hdelta
  obtain ⟨scaleLength, hscaleLength, hscaleAt⟩ :=
    exists_typeIIWeakSmallProductScaleThreshold
  refine ⟨Cdelta, hCdelta, ?_⟩
  intro epsilon hepsilon ell M region band sourcePresentation
  obtain ⟨massLength, hmassLength, hmassAt⟩ := hmass epsilon hepsilon
  refine ⟨max massLength scaleLength,
    hmassLength.trans (Nat.le_max_left _ _), ?_⟩
  intro length hlength digit
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hrhoSq
  have hmassLengthAt : massLength <= length :=
    (Nat.le_max_left massLength scaleLength).trans hlength
  have hscaleLengthAt : scaleLength <= length :=
    (Nat.le_max_right massLength scaleLength).trans hlength
  have hscale := hscaleAt length hscaleLengthAt
  dsimp only at hscale
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  have hlengthOne : 1 <= length :=
    hmassLength.trans hmassLengthAt
  let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
    hepsilon hepsilonSmall hlengthOne hdeltaGapStrict band B M
  let wall := fun C : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVStablePatternLocalWallValues (length := length)
        epsilon delta rho sourcePresentation band C pattern
  have hrho : 0 < rho := by
    simpa only [rho, XNat] using hscale.2.1
  have hrhoOne : rho <= 1 := by
    simpa only [rho, XNat] using
      hscale.2.2.1.trans (by norm_num : (1 / 2 : Real) <= 1)
  have hXOne : 1 < X := by
    dsimp only [X, XNat]
    linarith [hscale.1]
  have hlog : 0 < Real.log X := Real.log_pos hXOne
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact div_nonneg
      (mul_nonneg (restrictedDigitDensity_nonneg digit)
        (Nat.cast_nonneg A.card)) (zero_lt_one.trans hXOne).le
  have hcanonicalNonneg
      (pattern : SectionSixTerminalVStablePattern ell M) :
      0 <= sectionSixTerminalVStablePatternCanonicalWallCoefficient
        sourcePresentation epsilon delta band pattern :=
    sectionSixTerminalVStablePatternCanonicalWallCoefficient_nonneg
      sourcePresentation epsilon delta band pattern
  have hpatternBound (pattern : SectionSixTerminalVStablePattern ell M)
      (hpattern : pattern ∈ active) :
      (((wall A pattern).card : Real) +
          lambda * ((wall B pattern).card : Real)) <=
        Cdelta *
          ((rho * sectionSixTerminalVStablePatternCanonicalWallCoefficient
              sourcePresentation epsilon delta band pattern) *
            (A.card : Real) / Real.log X) := by
    have hnonempty :
        (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
          hepsilon hepsilonSmall hlengthOne hdeltaGapStrict.le band B
            (X ^ delta) (typeIINearXCarrier XNat rho) M pattern).Nonempty := by
      simpa only [active, X, XNat, rho] using
        (mem_sectionSixTerminalVActiveStablePatterns.mp hpattern)
    obtain ⟨hinner, hresidual, n, hdimension, hwall⟩ :=
      hmassAt length hmassLengthAt digit ell M region band sourcePresentation
        pattern hepsilonSmall hdeltaGapStrict hrhoSq hnonempty
    let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual
    let anchors := fun j : Fin P.constraintCount =>
      sectionSixTerminalVBaseXCoreLocalWallAnchors epsilon delta rho
        sourcePresentation band pattern hinner hresidual n hdimension j
    let supportCount := fun anchor : Fin (n + 1) -> Nat =>
      fun C : Finset Nat => typeIICellSupportCount XNat
        (scaledNaturalCubeAnchor rho anchor) rho delta C
    have hAcard :=
      card_sectionSixTerminalVStablePatternLocalWallValues_le_sum_cellSupports
        (epsilon := epsilon) (delta := delta) (rho := rho)
        (length := length) sourcePresentation band A pattern hinner hresidual
          hdimension
    have hBcard :=
      card_sectionSixTerminalVStablePatternLocalWallValues_le_sum_cellSupports
        (epsilon := epsilon) (delta := delta) (rho := rho)
        (length := length) sourcePresentation band B pattern hinner hresidual
          hdimension
    have hA : ((wall A pattern).card : Real) <=
        ∑ j : Fin P.constraintCount,
          ∑ anchor ∈ anchors j, supportCount anchor A := by
      dsimp only [wall, P, anchors, supportCount, typeIICellSupportCount,
        XNat, rho, A]
      exact_mod_cast hAcard
    have hB : ((wall B pattern).card : Real) <=
        ∑ j : Fin P.constraintCount,
          ∑ anchor ∈ anchors j, supportCount anchor B := by
      dsimp only [wall, P, anchors, supportCount, typeIICellSupportCount,
        XNat, rho, B]
      exact_mod_cast hBcard
    have hcombined :
        ((wall A pattern).card : Real) +
            lambda * ((wall B pattern).card : Real) <=
          ∑ j : Fin P.constraintCount,
            ∑ anchor ∈ anchors j,
              (supportCount anchor A + lambda * supportCount anchor B) := by
      calc
        ((wall A pattern).card : Real) +
              lambda * ((wall B pattern).card : Real) <=
            (∑ j : Fin P.constraintCount,
              ∑ anchor ∈ anchors j, supportCount anchor A) +
            lambda * (∑ j : Fin P.constraintCount,
              ∑ anchor ∈ anchors j, supportCount anchor B) :=
          add_le_add hA (mul_le_mul_of_nonneg_left hB hlambda)
        _ = ∑ j : Fin P.constraintCount,
            ∑ anchor ∈ anchors j,
              (supportCount anchor A + lambda * supportCount anchor B) := by
          simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    have hfactor :=
      sum_sectionSixTerminalVStablePatternWallFactor_le_rho_mul_coefficient
        sourcePresentation epsilon delta rho band pattern hinner hresidual n
          hdimension hrho.le hrhoOne
    have hcanonical :=
      sectionSixTerminalVStablePatternCanonicalWallCoefficient_eq_raw
        sourcePresentation epsilon delta band pattern hinner hresidual n
          hdimension
    let cast := Fin.castOrderIso hdimension
    let fullNormal := fun j : Fin P.constraintCount =>
      fun i : Fin (n + 2) => P.normal j (cast.symm i)
    let normal := fun j : Fin P.constraintCount =>
      typeIIProjectedAffineNormal (fullNormal j)
    let gamma := fun j : Fin P.constraintCount =>
      rho ^ 2 * typeIIAffineNormalMass (P.normal j)
    let wallFactor := fun j : Fin P.constraintCount =>
      rho + (2 : Real) ^ n *
        (2 * gamma j /
            |normal j (typeIIAffineMaxAbsCoordinate (normal j))| +
          ((4 * (n + 1) + 2 : Nat) : Real) * rho)
    have hfactor' : (∑ j : Fin P.constraintCount, wallFactor j) <=
        rho * sectionSixTerminalVStablePatternWallCoefficient
          sourcePresentation epsilon delta band pattern hinner hresidual n
            hdimension := by
      simpa only [P, cast, fullNormal, normal, gamma, wallFactor] using hfactor
    calc
      ((wall A pattern).card : Real) +
            lambda * ((wall B pattern).card : Real) <=
          ∑ j : Fin P.constraintCount,
            ∑ anchor ∈ anchors j,
              (supportCount anchor A + lambda * supportCount anchor B) :=
        hcombined
      _ <= ∑ j : Fin P.constraintCount,
          Cdelta *
            (wallFactor j * (A.card : Real) / Real.log X) := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [anchors, supportCount, lambda, wallFactor, cast,
          fullNormal, normal, gamma, P, A, B, XNat, X, rho] using hwall j
      _ = Cdelta *
          ((∑ j : Fin P.constraintCount, wallFactor j) *
            (A.card : Real) / Real.log X) := by
        calc
          (∑ j : Fin P.constraintCount,
              Cdelta *
                (wallFactor j * (A.card : Real) / Real.log X)) =
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
          ((rho * sectionSixTerminalVStablePatternWallCoefficient
              sourcePresentation epsilon delta band pattern hinner hresidual n
                hdimension) *
            (A.card : Real) / Real.log X) := by
        gcongr
      _ = Cdelta *
          ((rho * sectionSixTerminalVStablePatternCanonicalWallCoefficient
              sourcePresentation epsilon delta band pattern) *
            (A.card : Real) / Real.log X) := by
        rw [hcanonical]
  calc
    (∑ pattern ∈ active,
        (((wall A pattern).card : Real) +
          lambda * ((wall B pattern).card : Real))) <=
        ∑ pattern ∈ active,
          Cdelta *
            ((rho * sectionSixTerminalVStablePatternCanonicalWallCoefficient
                sourcePresentation epsilon delta band pattern) *
              (A.card : Real) / Real.log X) := by
      exact Finset.sum_le_sum fun pattern hpattern =>
        hpatternBound pattern hpattern
    _ <= ∑ pattern : SectionSixTerminalVStablePattern ell M,
        Cdelta *
          ((rho * sectionSixTerminalVStablePatternCanonicalWallCoefficient
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
            sectionSixTerminalVStablePatternCanonicalWallCoefficientSum
              sourcePresentation epsilon delta band M) *
          (A.card : Real) / Real.log X) := by
      unfold sectionSixTerminalVStablePatternCanonicalWallCoefficientSum
      calc
        (∑ pattern : SectionSixTerminalVStablePattern ell M,
            Cdelta *
              ((rho * sectionSixTerminalVStablePatternCanonicalWallCoefficient
                  sourcePresentation epsilon delta band pattern) *
                (A.card : Real) / Real.log X)) =
            ∑ pattern : SectionSixTerminalVStablePattern ell M,
              (Cdelta * rho * (A.card : Real) / Real.log X) *
                sectionSixTerminalVStablePatternCanonicalWallCoefficient
                  sourcePresentation epsilon delta band pattern := by
          apply Finset.sum_congr rfl
          intro pattern _
          ring
        _ = (Cdelta * rho * (A.card : Real) / Real.log X) *
            ∑ pattern : SectionSixTerminalVStablePattern ell M,
              sectionSixTerminalVStablePatternCanonicalWallCoefficient
                sourcePresentation epsilon delta band pattern := by
          rw [Finset.mul_sum]
        _ = _ := by ring

end

end PrimesRestrictedDigits
