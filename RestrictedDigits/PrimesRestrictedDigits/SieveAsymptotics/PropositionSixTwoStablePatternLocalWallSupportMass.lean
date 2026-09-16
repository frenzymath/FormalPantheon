import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternLocalWallAnchors
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineThickSlabMass

/-!
# Proposition 6.2 fixed-pattern local-wall support mass

The canonical local anchors for one realized Proposition 6.2 stable pattern satisfy the
positive thick-slab support-mass estimate at the theta-gap simplex parameter.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 149--152, and Proposition 7.2, pp.
163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- Every literal canonical wall-anchor family of a positive-arity stable
pattern satisfies the uniform requested-plus-weighted-ambient support bound. -/
theorem exists_propositionSixTwoStablePatternLocalWallSupportMass_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    ∃ Ceta : Real, 0 < Ceta ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
        ∀ {ell M : Nat} (I : Finset (Fin ell))
          {sourceRegion : Set (Fin ell -> Real)}
          (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
          (band : SectionSixDirectBand)
          (pattern : PropositionSixTwoStablePattern ell M)
          (hell : 0 < ell) (hresidual : 0 < pattern.1.1)
          (harity : (((ell + pattern.1.1 : Nat) : Real) <=
            2 / sectionSixThetaGap epsilon)),
          let XNat : Nat := 10 ^ length
          let X : Real := (XNat : Real)
          let rho : Real := majorArcM2LogLogDelta XNat
          let A : Finset Nat := paddedRestrictedNumbers digit length
          let B : Finset Nat := maynardAmbientCarrier X
          let lambda : Real :=
            (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
          let n := propositionSixTwoStablePatternPredecessorDimension pattern
          let hdimension : ell + pattern.1.1 = n + 2 := by
            dsimp only [n, propositionSixTwoStablePatternPredecessorDimension]
            omega
          let P := propositionSixTwoDisplayedPresentation sourcePresentation
            epsilon I band
          let cast := Fin.castOrderIso hdimension
          let embedding := pattern.2.trans cast.toEquiv.toEmbedding
          ∀ c : Fin P.constraintCount,
            let fullNormal : Fin (n + 2) -> Real :=
              typeIIAffineLiftNormal embedding (P.normal c)
            let normal := typeIIProjectedAffineNormal fullNormal
            let gamma := rho ^ 2 * typeIIAffineNormalMass (P.normal c)
            let anchors := propositionSixTwoStablePatternLocalWallAnchors
              epsilon rho I sourcePresentation band pattern hell hresidual c
            let supportCount : (Fin (n + 1) -> Nat) -> Finset Nat -> Real :=
              fun anchor C => typeIICellSupportCount XNat
                (scaledNaturalCubeAnchor rho anchor) rho
                  (sectionSixThetaGap epsilon) C
            anchors.sum (fun anchor =>
                supportCount anchor A + lambda * supportCount anchor B) <=
              Ceta *
                ((rho + (2 : Real) ^ n *
                    (2 * gamma /
                        |normal (typeIIAffineMaxAbsCoordinate normal)| +
                      ((4 * (n + 1) + 2 : Nat) : Real) * rho)) *
                  (A.card : Real) / Real.log X) := by
  let eta : Real := sectionSixThetaGap epsilon
  have heta : 0 < eta := by
    simpa only [eta] using
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  obtain ⟨Ceta, hCeta, hmass⟩ :=
    exists_typeIIAffineThickSlabSupportMass_eta_upper eta heta
  obtain ⟨massLength, hmassLength, hmassAt⟩ := hmass epsilon hepsilon
  obtain ⟨scaleLength, _hscaleLength, hscaleAt⟩ :=
    exists_typeIIWeakSmallProductScaleThreshold
  refine ⟨Ceta, hCeta, max massLength scaleLength,
    hmassLength.trans (Nat.le_max_left _ _), ?_⟩
  intro length hlength digit ell M I sourceRegion sourcePresentation band pattern
    hell hresidual harity
  dsimp only
  intro c
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
  let n := propositionSixTwoStablePatternPredecessorDimension pattern
  let hdimension : ell + pattern.1.1 = n + 2 := by
    dsimp only [n, propositionSixTwoStablePatternPredecessorDimension]
    omega
  let P := propositionSixTwoDisplayedPresentation sourcePresentation epsilon I
    band
  let cast := Fin.castOrderIso hdimension
  let embedding := pattern.2.trans cast.toEquiv.toEmbedding
  let fullNormal : Fin (n + 2) -> Real :=
    typeIIAffineLiftNormal embedding (P.normal c)
  let normal := typeIIProjectedAffineNormal fullNormal
  let bound := typeIIProjectedAffineBound fullNormal (P.bound c)
  let gamma := rho ^ 2 * typeIIAffineNormalMass (P.normal c)
  let anchors := propositionSixTwoStablePatternLocalWallAnchors epsilon rho I
    sourcePresentation band pattern hell hresidual c
  let supportCount : (Fin (n + 1) -> Nat) -> Finset Nat -> Real :=
    fun anchor C => typeIICellSupportCount XNat
      (scaledNaturalCubeAnchor rho anchor) rho (sectionSixThetaGap epsilon) C
  by_cases hnormal : normal ≠ 0
  · have hgamma : 0 <= gamma := by
      apply mul_nonneg (sq_nonneg _)
      exact Finset.sum_nonneg fun i _ => abs_nonneg (P.normal c i)
    have harity' : (((n + 2 : Nat) : Real) <= 2 / eta) := by
      simpa only [eta, hdimension] using harity
    have h := hmassAt length hmassLengthAt digit n normal bound gamma anchors
      hnormal hgamma harity'
    have hsubset : anchors ⊆
        typeIIAffineThickSlabAnchors rho gamma normal bound := by
      intro anchor hanchor
      exact
        (mem_propositionSixTwoStablePatternLocalWallAnchors.mp hanchor).1
    have hmargin : ∀ anchor ∈ anchors, ∀ i,
        eta / 2 <= scaledNaturalCubeAnchor rho anchor i := by
      intro anchor hanchor i
      simpa only [eta] using
        (mem_propositionSixTwoStablePatternLocalWallAnchors.mp hanchor).2.1 i
    have hroom : ∀ anchor ∈ anchors,
        (∑ i, scaledNaturalCubeAnchor rho anchor i) < 1 - eta / 2 := by
      intro anchor hanchor
      simpa only [eta] using
        (mem_propositionSixTwoStablePatternLocalWallAnchors.mp hanchor).2.2.1
    have hconvenience : ∀ anchor ∈ anchors,
        ∃ J : Finset (Fin (n + 1)),
          (∑ i ∈ J, scaledNaturalCubeAnchor rho anchor i) ∈
              Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
            (∑ i ∈ J, scaledNaturalCubeAnchor rho anchor i) ∈
              Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon) := by
      intro anchor hanchor
      exact
        (mem_propositionSixTwoStablePatternLocalWallAnchors.mp hanchor).2.2.2
    have hresult := h hsubset hmargin hroom hconvenience
    have hlambda :
        (restrictedDigitDensity digit : Real) * (A.card : Real) / X =
          lambda := by
      simp only [lambda, mul_div_assoc]
    rw [hlambda] at hresult
    simpa only [eta] using hresult
  · have hanchorsEmpty : anchors = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨anchor, hanchor⟩
      exact hnormal
        (mem_typeIIAffineThickSlabAnchors.mp
          (mem_propositionSixTwoStablePatternLocalWallAnchors.mp hanchor).1).2.1
    have hrho : 0 < rho := by
      simpa only [rho, XNat] using hscale.2.1
    have hXOne : 1 < X := by
      dsimp only [X, XNat]
      linarith [hscale.1]
    have hlog : 0 < Real.log X := Real.log_pos hXOne
    change anchors.sum (fun anchor =>
        supportCount anchor A + lambda * supportCount anchor B) <= _
    rw [hanchorsEmpty]
    simp only [Finset.sum_empty]
    change 0 <= Ceta *
      ((rho + (2 : Real) ^ n *
          (2 * gamma /
              |normal (typeIIAffineMaxAbsCoordinate normal)| +
            ((4 * (n + 1) + 2 : Nat) : Real) * rho)) *
        (A.card : Real) / Real.log X)
    rw [not_ne_iff.mp hnormal]
    simp only [Pi.zero_apply, abs_zero, div_zero, zero_add]
    positivity

end

end PrimesRestrictedDigits
