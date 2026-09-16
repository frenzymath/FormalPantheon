import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineThickSlabMass

/-!
# Positive support mass for one direct displayed wall

This specializes the positive thick-slab mass estimate to one literal constraint of the direct
Section 6 displayed-band presentation. See `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp.
150--152, and Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/--
The positive support mass specialized to one literal direct Section 6 displayed wall in an
explicit positive projected dimension.
-/
theorem exists_sectionSixDirectDisplayedWallSupportMass_delta_upper
    (delta : Real) (hdelta : 0 < delta) :
    ∃ Cdelta : Real, 0 < Cdelta ∧
      ∀ epsilon : Real, 0 < epsilon ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
          ∀ (digit : Fin 10) (ell n : Nat)
            (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand)
            (sourcePresentation : TypeIIAffineHalfspacePresentation region)
            (embedding : Fin (ell + 1) ↪ Fin (n + 2))
            (j : Fin (sectionSixDirectDisplayedBandPresentation
              sourcePresentation epsilon delta band).constraintCount)
            (anchors : Finset (Fin (n + 1) -> Nat)),
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let rho : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let P := sectionSixDirectDisplayedBandPresentation
              sourcePresentation epsilon delta band
            let normal : Fin (n + 1) -> Real :=
              typeIIProjectedAffineNormal
                (typeIIAffineLiftNormal embedding (P.normal j))
            let bound : Real := typeIIProjectedAffineBound
              (typeIIAffineLiftNormal embedding (P.normal j)) (P.bound j)
            let gamma : Real :=
              rho ^ 2 * typeIIAffineNormalMass (P.normal j)
            let supportCount :
                (Fin (n + 1) -> Nat) -> Finset Nat -> Real :=
              fun anchor C => typeIICellSupportCount XNat
                (scaledNaturalCubeAnchor rho anchor) rho delta C
            normal ≠ 0 ->
            (((n + 2 : Nat) : Real) <= 2 / delta) ->
            anchors ⊆
              typeIIAffineThickSlabAnchors rho gamma normal bound ->
            (∀ anchor ∈ anchors, ∀ i,
              delta / 2 <= scaledNaturalCubeAnchor rho anchor i) ->
            (∀ anchor ∈ anchors,
              (∑ i, scaledNaturalCubeAnchor rho anchor i) <
                1 - delta / 2) ->
            (∀ anchor ∈ anchors, ∃ I : Finset (Fin (n + 1)),
              (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
                  Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
              (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
                  Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon)) ->
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
  refine ⟨Cdelta, hCdelta, ?_⟩
  intro epsilon hepsilon
  obtain ⟨length0, hlength0, hmassAt⟩ := hmass epsilon hepsilon
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit ell n region band sourcePresentation embedding j
    anchors
  dsimp only
  intro hnormal harity hanchors hmargin hroom hconvenient
  let P := sectionSixDirectDisplayedBandPresentation
    sourcePresentation epsilon delta band
  let normal : Fin (n + 1) -> Real :=
    typeIIProjectedAffineNormal
      (typeIIAffineLiftNormal embedding (P.normal j))
  let bound : Real := typeIIProjectedAffineBound
    (typeIIAffineLiftNormal embedding (P.normal j)) (P.bound j)
  let gamma : Real := majorArcM2LogLogDelta (10 ^ length) ^ 2 *
    typeIIAffineNormalMass (P.normal j)
  have hgamma : 0 <= gamma := by
    apply mul_nonneg (sq_nonneg _)
    exact Finset.sum_nonneg fun i _ => abs_nonneg (P.normal j i)
  have h := hmassAt length hlength digit n normal bound gamma anchors
    (by simpa only [normal, P] using hnormal) hgamma harity
    (by simpa only [normal, bound, gamma, P] using hanchors)
    hmargin hroom hconvenient
  simpa only [P, normal, bound, gamma] using h

end

end PrimesRestrictedDigits
