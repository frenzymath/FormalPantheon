import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreLocalWallAnchors
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineThickSlabMass

/-!
# Support mass for one terminal-V BaseX-core wall

This applies the established thick-slab support-mass estimate to the locally admissible
anchors for one literal terminal-V wall. See `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 150--152,
and Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/--
The uniform support-mass bound for one terminal-V BaseX-core literal wall. Projected-zero
literals have an empty anchor family.
-/
theorem exists_sectionSixTerminalVBaseXCoreLocalWallSupportMass_delta_upper
    (delta : Real) (hdelta : 0 < delta) :
    ∃ Cdelta : Real, 0 < Cdelta ∧
      ∀ epsilon : Real, 0 < epsilon ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
          ∀ (digit : Fin 10) (ell M : Nat)
            (region : Set (Fin ell -> Real)) (band : SectionSixStateBand)
            (sourcePresentation : TypeIIAffineHalfspacePresentation region)
            (pattern : SectionSixTerminalVStablePattern ell M)
            (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
            (n : Nat)
            (hdimension : (pattern.1.1 + ell) + pattern.2.1.1 = n + 2)
            (j : Fin (sectionSixTerminalVBaseXCorePresentation
              sourcePresentation epsilon delta band pattern hinner
                hresidual).constraintCount),
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let rho : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
              epsilon delta band pattern hinner hresidual
            let cast := Fin.castOrderIso hdimension
            let fullNormal : Fin (n + 2) -> Real := fun i =>
              P.normal j (cast.symm i)
            let normal := typeIIProjectedAffineNormal fullNormal
            let gamma := rho ^ 2 * typeIIAffineNormalMass (P.normal j)
            let anchors := sectionSixTerminalVBaseXCoreLocalWallAnchors
              epsilon delta rho sourcePresentation band pattern hinner hresidual
                n hdimension j
            let supportCount : (Fin (n + 1) -> Nat) -> Finset Nat -> Real :=
              fun anchor C => typeIICellSupportCount XNat
                (scaledNaturalCubeAnchor rho anchor) rho delta C
            (((n + 2 : Nat) : Real) <= 2 / delta) ->
            anchors.sum (fun anchor =>
                supportCount anchor A +
                  (restrictedDigitDensity digit : Real) *
                    (A.card : Real) / X * supportCount anchor B) <=
              Cdelta *
                ((rho + (2 : Real) ^ n *
                    (2 * gamma /
                        |normal (typeIIAffineMaxAbsCoordinate normal)| +
                      ((4 * (n + 1) + 2 : Nat) : Real) * rho)) *
                  (A.card : Real) / Real.log X) := by
  obtain ⟨Cdelta, hCdelta, hmass⟩ :=
    exists_typeIIAffineThickSlabSupportMass_eta_upper delta hdelta
  obtain ⟨scaleLength, _hscaleLength, hscaleAt⟩ :=
    exists_typeIIWeakSmallProductScaleThreshold
  refine ⟨Cdelta, hCdelta, ?_⟩
  intro epsilon hepsilon
  obtain ⟨massLength, hmassLength, hmassAt⟩ := hmass epsilon hepsilon
  refine ⟨max massLength scaleLength,
    hmassLength.trans (Nat.le_max_left _ _), ?_⟩
  intro length hlength digit ell M region band sourcePresentation pattern
    hinner hresidual n hdimension j
  dsimp only
  intro harity
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
  let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
    epsilon delta band pattern hinner hresidual
  let cast := Fin.castOrderIso hdimension
  let fullNormal : Fin (n + 2) -> Real := fun i => P.normal j (cast.symm i)
  let normal := typeIIProjectedAffineNormal fullNormal
  let bound := typeIIProjectedAffineBound fullNormal (P.bound j)
  let gamma := rho ^ 2 * typeIIAffineNormalMass (P.normal j)
  let anchors := sectionSixTerminalVBaseXCoreLocalWallAnchors epsilon delta rho
    sourcePresentation band pattern hinner hresidual n hdimension j
  let supportCount : (Fin (n + 1) -> Nat) -> Finset Nat -> Real :=
    fun anchor C => typeIICellSupportCount XNat
      (scaledNaturalCubeAnchor rho anchor) rho delta C
  by_cases hnormal : normal ≠ 0
  · have hgamma : 0 <= gamma := by
      apply mul_nonneg (sq_nonneg _)
      exact Finset.sum_nonneg fun i _ => abs_nonneg (P.normal j i)
    have h := hmassAt length hmassLengthAt digit n normal bound gamma anchors
      hnormal hgamma harity
    apply h
    · intro anchor hanchor
      exact
        (mem_sectionSixTerminalVBaseXCoreLocalWallAnchors.mp hanchor).1
    · intro anchor hanchor i
      exact
        (mem_sectionSixTerminalVBaseXCoreLocalWallAnchors.mp hanchor).2.1 i
    · intro anchor hanchor
      exact
        (mem_sectionSixTerminalVBaseXCoreLocalWallAnchors.mp hanchor).2.2.1
    · intro anchor hanchor
      exact
        (mem_sectionSixTerminalVBaseXCoreLocalWallAnchors.mp hanchor).2.2.2
  · have hanchorsEmpty : anchors = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨anchor, hanchor⟩
      exact hnormal
        (mem_typeIIAffineThickSlabAnchors.mp
          (mem_sectionSixTerminalVBaseXCoreLocalWallAnchors.mp hanchor).1).2.1
    have hrho : 0 < rho := by
      simpa only [rho, XNat] using hscale.2.1
    have hXone : (1 : Real) < X := by
      dsimp only [X, XNat]
      linarith [hscale.1]
    have hlog : 0 < Real.log X := Real.log_pos hXone
    change anchors.sum (fun anchor =>
        supportCount anchor A +
          (restrictedDigitDensity digit : Real) *
            (A.card : Real) / X * supportCount anchor B) <= _
    rw [hanchorsEmpty]
    simp only [Finset.sum_empty]
    change 0 <= Cdelta *
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
