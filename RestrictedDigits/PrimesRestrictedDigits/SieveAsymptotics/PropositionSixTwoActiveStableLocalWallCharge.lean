import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternCanonicalWallCoefficient
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternLocalWallSupportMass
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetReverseCover
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStableCarriers

/-!
# Proposition 6.2 active stable-pattern local-wall charge

The labelled local-wall term in the Proposition 6.2 near ledger is bounded by the
fixed-pattern support-mass estimate, one log-log width, and one fixed finite coefficient sum.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152, and Proposition 7.2 statement, p.
148, and proof, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- The complete restricted and density-weighted ambient active local-wall
charge has one varying log-log width and one fixed positive coefficient. -/
theorem exists_propositionSixTwoActiveStableLocalWallCharge_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {ell : Nat} (I : Finset (Fin ell)) (j : Fin ell)
    (sourceRegion : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (band : SectionSixDirectBand) :
    let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
    ∃ Cwall : Real, 0 < Cwall ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          let XNat : Nat := 10 ^ length
          let X : Real := (XNat : Real)
          let rho : Real := majorArcM2LogLogDelta XNat
          let A : Finset Nat := paddedRestrictedNumbers digit length
          let B : Finset Nat := maynardAmbientCarrier X
          let lambda : Real :=
            (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
          let wallCount : Finset Nat -> Real := fun C =>
            ((propositionSixTwoActiveStableLocalWallValues epsilon rho ell I j
              sourceRegion length sourcePresentation band B C M).card : Real)
          wallCount A + lambda * wallCount B <=
            Cwall * rho * (A.card : Real) / Real.log X := by
  dsimp only
  let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
  obtain ⟨Ceta, hCeta, massLength, hmassLength, hmassAt⟩ :=
    exists_propositionSixTwoStablePatternLocalWallSupportMass_upper epsilon
      hepsilon hepsilonSmall
  let S : Real := propositionSixTwoStablePatternCanonicalWallCoefficientSum
    sourcePresentation epsilon I band M
  let Cwall : Real := Ceta * (S + 1)
  have hS : 0 <= S := by
    dsimp only [S]
    exact propositionSixTwoStablePatternCanonicalWallCoefficientSum_nonneg
      sourcePresentation epsilon I band M
  have hCwall : 0 < Cwall := by
    dsimp only [Cwall]
    exact mul_pos hCeta (by linarith)
  obtain ⟨scaleLength, hscaleLength, hscaleAt⟩ :=
    exists_typeIIWeakSmallProductScaleThreshold
  let length0 : Nat := max massLength scaleLength
  have hlength0 : 1 <= length0 :=
    hmassLength.trans (Nat.le_max_left _ _)
  refine ⟨Cwall, hCwall, length0, hlength0, ?_⟩
  intro length hlength digit
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
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let active := propositionSixTwoActiveStablePatterns epsilon rho ell I j
    sourceRegion length band B M
  let wall := fun C : Finset Nat =>
    fun pattern : PropositionSixTwoStablePattern ell M =>
      propositionSixTwoStablePatternLocalWallValues (length := length) epsilon
        rho I sourcePresentation band C pattern
  let wallCount : Finset Nat -> Real := fun C =>
    ((propositionSixTwoActiveStableLocalWallValues epsilon rho ell I j
      sourceRegion length sourcePresentation band B C M).card : Real)
  have hlengthOne : 1 <= length := hlength0.trans hlength
  have hell : 0 < ell := Nat.zero_lt_of_lt j.isLt
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
    exact mul_nonneg (restrictedDigitDensity_nonneg digit)
      (div_nonneg (Nat.cast_nonneg A.card) (zero_lt_one.trans hXOne).le)
  have hcanonicalNonneg (pattern : PropositionSixTwoStablePattern ell M) :
      0 <= propositionSixTwoStablePatternCanonicalWallCoefficient
        sourcePresentation epsilon I band pattern :=
    propositionSixTwoStablePatternCanonicalWallCoefficient_nonneg
      sourcePresentation epsilon I band pattern
  have hpatternBound (pattern : PropositionSixTwoStablePattern ell M)
      (hpattern : pattern ∈ active) :
      (((wall A pattern).card : Real) +
          lambda * ((wall B pattern).card : Real)) <=
        Ceta *
          ((rho * propositionSixTwoStablePatternCanonicalWallCoefficient
              sourcePresentation epsilon I band pattern) *
            (A.card : Real) / Real.log X) := by
    by_cases hresidual : 0 < pattern.1.1
    · obtain ⟨candidate, hcandidate⟩ :=
        mem_propositionSixTwoActiveStablePatterns.mp hpattern
      have hslice :=
        mem_propositionSixTwoNearCandidatesOfStablePattern.mp hcandidate
      have htag :=
        PropositionSixTwoCandidate.stablePatternTag_eq_some_data hslice.2
      have htotal := propositionSixTwoNearCandidate_totalArity_le_two_div
        hepsilon hepsilonSmall hlengthOne hslice.1
      have harity : (((ell + pattern.1.1 : Nat) : Real) <=
          2 / sectionSixThetaGap epsilon) := by
        simpa only [htag.1] using htotal
      let n := propositionSixTwoStablePatternPredecessorDimension pattern
      let hdimension : ell + pattern.1.1 = n + 2 := by
        dsimp only [n, propositionSixTwoStablePatternPredecessorDimension]
        omega
      let P := propositionSixTwoDisplayedPresentation sourcePresentation epsilon
        I band
      let cast := Fin.castOrderIso hdimension
      let embedding := pattern.2.trans cast.toEquiv.toEmbedding
      let anchors := fun c : Fin P.constraintCount =>
        propositionSixTwoStablePatternLocalWallAnchors epsilon rho I
          sourcePresentation band pattern hell hresidual c
      let supportCount := fun anchor : Fin (n + 1) -> Nat =>
        fun C : Finset Nat => typeIICellSupportCount XNat
          (scaledNaturalCubeAnchor rho anchor) rho
            (sectionSixThetaGap epsilon) C
      have hAcard :=
        card_propositionSixTwoStablePatternLocalWallValues_le_sum_cellSupports
          (epsilon := epsilon) (rho := rho) (length := length) I
            sourcePresentation band A pattern hell hresidual
      have hBcard :=
        card_propositionSixTwoStablePatternLocalWallValues_le_sum_cellSupports
          (epsilon := epsilon) (rho := rho) (length := length) I
            sourcePresentation band B pattern hell hresidual
      have hA : ((wall A pattern).card : Real) <=
          ∑ c : Fin P.constraintCount,
            ∑ anchor ∈ anchors c, supportCount anchor A := by
        dsimp only [wall, P, anchors, supportCount, typeIICellSupportCount,
          XNat, rho, A]
        exact_mod_cast hAcard
      have hB : ((wall B pattern).card : Real) <=
          ∑ c : Fin P.constraintCount,
            ∑ anchor ∈ anchors c, supportCount anchor B := by
        dsimp only [wall, P, anchors, supportCount, typeIICellSupportCount,
          XNat, rho, B]
        exact_mod_cast hBcard
      have hcombined :
          ((wall A pattern).card : Real) +
              lambda * ((wall B pattern).card : Real) <=
            ∑ c : Fin P.constraintCount,
              ∑ anchor ∈ anchors c,
                (supportCount anchor A + lambda * supportCount anchor B) := by
        calc
          ((wall A pattern).card : Real) +
                lambda * ((wall B pattern).card : Real) <=
              (∑ c : Fin P.constraintCount,
                ∑ anchor ∈ anchors c, supportCount anchor A) +
              lambda * (∑ c : Fin P.constraintCount,
                ∑ anchor ∈ anchors c, supportCount anchor B) :=
            add_le_add hA (mul_le_mul_of_nonneg_left hB hlambda)
          _ = ∑ c : Fin P.constraintCount,
              ∑ anchor ∈ anchors c,
                (supportCount anchor A + lambda * supportCount anchor B) := by
            simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      have hmass := hmassAt length hmassLengthAt digit I sourcePresentation band
        pattern hell hresidual harity
      have hfactor :=
        sum_propositionSixTwoStablePatternWallFactor_le_rho_mul_coefficient
          sourcePresentation epsilon rho I band pattern hell hresidual n
            hdimension hrho.le hrhoOne
      have hcanonical :=
        propositionSixTwoStablePatternCanonicalWallCoefficient_eq_raw
          sourcePresentation epsilon I band pattern hell hresidual n hdimension
      let fullNormal := fun c : Fin P.constraintCount =>
        typeIIAffineLiftNormal embedding (P.normal c)
      let normal := fun c : Fin P.constraintCount =>
        typeIIProjectedAffineNormal (fullNormal c)
      let gamma := fun c : Fin P.constraintCount =>
        rho ^ 2 * typeIIAffineNormalMass (P.normal c)
      let wallFactor := fun c : Fin P.constraintCount =>
        rho + (2 : Real) ^ n *
          (2 * gamma c /
              |normal c (typeIIAffineMaxAbsCoordinate (normal c))| +
            ((4 * (n + 1) + 2 : Nat) : Real) * rho)
      have hfactor' : (∑ c : Fin P.constraintCount, wallFactor c) <=
          rho * propositionSixTwoStablePatternWallCoefficient sourcePresentation
            epsilon I band pattern hell hresidual n hdimension := by
        simpa only [P, cast, embedding, fullNormal, normal, gamma, wallFactor]
          using hfactor
      calc
        ((wall A pattern).card : Real) +
              lambda * ((wall B pattern).card : Real) <=
            ∑ c : Fin P.constraintCount,
              ∑ anchor ∈ anchors c,
                (supportCount anchor A + lambda * supportCount anchor B) :=
          hcombined
        _ <= ∑ c : Fin P.constraintCount,
            Ceta * (wallFactor c * (A.card : Real) / Real.log X) := by
          apply Finset.sum_le_sum
          intro c _
          simpa only [anchors, supportCount, lambda, wallFactor, cast, embedding,
            fullNormal, normal, gamma, P, A, B, XNat, X, rho, n, hdimension]
            using hmass c
        _ = Ceta *
            ((∑ c : Fin P.constraintCount, wallFactor c) *
              (A.card : Real) / Real.log X) := by
          calc
            (∑ c : Fin P.constraintCount,
                Ceta * (wallFactor c * (A.card : Real) / Real.log X)) =
                ∑ c : Fin P.constraintCount,
                  (Ceta * (A.card : Real) / Real.log X) * wallFactor c := by
              apply Finset.sum_congr rfl
              intro c _
              ring
            _ = (Ceta * (A.card : Real) / Real.log X) *
                ∑ c : Fin P.constraintCount, wallFactor c := by
              rw [Finset.mul_sum]
            _ = _ := by ring
        _ <= Ceta *
            ((rho * propositionSixTwoStablePatternWallCoefficient
                sourcePresentation epsilon I band pattern hell hresidual n
                  hdimension) *
              (A.card : Real) / Real.log X) := by
          gcongr
        _ = Ceta *
            ((rho * propositionSixTwoStablePatternCanonicalWallCoefficient
                sourcePresentation epsilon I band pattern) *
              (A.card : Real) / Real.log X) := by
          rw [hcanonical]
    · have hwallA : wall A pattern = ∅ := by
        dsimp only [wall]
        unfold propositionSixTwoStablePatternLocalWallValues
        simp only [dif_pos hell, dif_neg hresidual]
      have hwallB : wall B pattern = ∅ := by
        dsimp only [wall]
        unfold propositionSixTwoStablePatternLocalWallValues
        simp only [dif_pos hell, dif_neg hresidual]
      have hcanonical :=
        propositionSixTwoStablePatternCanonicalWallCoefficient_eq_zero_of_not_residual
          sourcePresentation epsilon I band pattern hresidual
      rw [hwallA, hwallB, hcanonical]
      simp
  have hwallCount (C : Finset Nat) :
      wallCount C =
        ∑ pattern ∈ active, ((wall C pattern).card : Real) := by
    dsimp only [wallCount]
    rw [card_propositionSixTwoActiveStableLocalWallValues]
    simp only [Nat.cast_sum, active, wall]
  have hactiveBound :
      (∑ pattern ∈ active,
          (((wall A pattern).card : Real) +
            lambda * ((wall B pattern).card : Real))) <=
        Ceta * ((rho * S) * (A.card : Real) / Real.log X) := by
    calc
      (∑ pattern ∈ active,
          (((wall A pattern).card : Real) +
            lambda * ((wall B pattern).card : Real))) <=
          ∑ pattern ∈ active,
            Ceta *
              ((rho * propositionSixTwoStablePatternCanonicalWallCoefficient
                  sourcePresentation epsilon I band pattern) *
                (A.card : Real) / Real.log X) := by
        exact Finset.sum_le_sum fun pattern hpattern =>
          hpatternBound pattern hpattern
      _ <= ∑ pattern : PropositionSixTwoStablePattern ell M,
          Ceta *
            ((rho * propositionSixTwoStablePatternCanonicalWallCoefficient
                sourcePresentation epsilon I band pattern) *
              (A.card : Real) / Real.log X) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ active)
        intro pattern _ _
        exact mul_nonneg hCeta.le
          (div_nonneg
            (mul_nonneg (mul_nonneg hrho.le (hcanonicalNonneg pattern))
              (Nat.cast_nonneg A.card)) hlog.le)
      _ = Ceta * ((rho * S) * (A.card : Real) / Real.log X) := by
        dsimp only [S]
        unfold propositionSixTwoStablePatternCanonicalWallCoefficientSum
        calc
          (∑ pattern : PropositionSixTwoStablePattern ell M,
              Ceta *
                ((rho * propositionSixTwoStablePatternCanonicalWallCoefficient
                    sourcePresentation epsilon I band pattern) *
                  (A.card : Real) / Real.log X)) =
              ∑ pattern : PropositionSixTwoStablePattern ell M,
                (Ceta * rho * (A.card : Real) / Real.log X) *
                  propositionSixTwoStablePatternCanonicalWallCoefficient
                    sourcePresentation epsilon I band pattern := by
            apply Finset.sum_congr rfl
            intro pattern _
            ring
          _ = (Ceta * rho * (A.card : Real) / Real.log X) *
              ∑ pattern : PropositionSixTwoStablePattern ell M,
                propositionSixTwoStablePatternCanonicalWallCoefficient
                  sourcePresentation epsilon I band pattern := by
            rw [Finset.mul_sum]
          _ = _ := by ring
  have hscaleNonneg : 0 <= rho * (A.card : Real) / Real.log X := by
    positivity
  have hcoefficient : Ceta * S <= Cwall := by
    dsimp only [Cwall]
    nlinarith
  have hfinal : Ceta * ((rho * S) * (A.card : Real) / Real.log X) <=
      Cwall * rho * (A.card : Real) / Real.log X := by
    calc
      Ceta * ((rho * S) * (A.card : Real) / Real.log X) =
          (Ceta * S) * (rho * (A.card : Real) / Real.log X) := by ring
      _ <= Cwall * (rho * (A.card : Real) / Real.log X) :=
        mul_le_mul_of_nonneg_right hcoefficient hscaleNonneg
      _ = Cwall * rho * (A.card : Real) / Real.log X := by ring
  change wallCount A + lambda * wallCount B <=
    Cwall * rho * (A.card : Real) / Real.log X
  rw [hwallCount A, hwallCount B, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact hactiveBound.trans hfinal

end

end PrimesRestrictedDigits
