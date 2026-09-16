import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreLocalWallSupportMass
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternRealizedData

/-!
# Local wall support mass for a realized terminal-V stable pattern

One ambient candidate supplies the common predecessor dimension needed to apply the terminal-V
BaseX-core wall estimate to every literal occurrence. See `MAYNARD-PRD-PUBLISHED`, Lemma 7.3,
pp. 149--152, and Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- A realized terminal-V stable pattern has one common predecessor dimension
on which every BaseX-core literal satisfies the per-wall support-mass bound. -/
theorem exists_sectionSixTerminalVStablePatternLocalWallSupportMass_delta_upper
    (delta : Real) (hdelta : 0 < delta) :
    ∃ Cdelta : Real, 0 < Cdelta ∧
      ∀ (epsilon : Real) (hepsilon : 0 < epsilon),
        ∃ (length0 : Nat) (hlength0 : 1 <= length0),
          ∀ (length : Nat) (hlength : length0 <= length),
          ∀ (digit : Fin 10) (ell M : Nat)
            (region : Set (Fin ell -> Real)) (band : SectionSixStateBand)
            (sourcePresentation : TypeIIAffineHalfspacePresentation region)
            (pattern : SectionSixTerminalVStablePattern ell M),
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let rho : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let hlengthOne : 1 <= length := hlength0.trans hlength
            ∀ (hepsilonSmall : epsilon <= 1 / 64)
              (hdeltaGapStrict : delta < sectionSixThetaGap epsilon),
            rho ^ 2 < delta ->
            (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
              hepsilon hepsilonSmall hlengthOne hdeltaGapStrict.le band B
                (X ^ delta) (typeIINearXCarrier XNat rho) M pattern).Nonempty ->
            ∃ hinner : 0 < pattern.1.1,
              ∃ hresidual : 0 < pattern.2.1.1,
              ∃ n : Nat,
              ∃ hdimension :
                  (pattern.1.1 + ell) + pattern.2.1.1 = n + 2,
                ∀ j : Fin (sectionSixTerminalVBaseXCorePresentation
                    sourcePresentation epsilon delta band pattern hinner
                      hresidual).constraintCount,
                  let P := sectionSixTerminalVBaseXCorePresentation
                    sourcePresentation epsilon delta band pattern hinner
                      hresidual
                  let cast := Fin.castOrderIso hdimension
                  let fullNormal : Fin (n + 2) -> Real := fun i =>
                    P.normal j (cast.symm i)
                  let normal := typeIIProjectedAffineNormal fullNormal
                  let gamma := rho ^ 2 * typeIIAffineNormalMass (P.normal j)
                  let anchors := sectionSixTerminalVBaseXCoreLocalWallAnchors
                    epsilon delta rho sourcePresentation band pattern hinner
                      hresidual n hdimension j
                  let supportCount :
                      (Fin (n + 1) -> Nat) -> Finset Nat -> Real :=
                    fun anchor C => typeIICellSupportCount XNat
                      (scaledNaturalCubeAnchor rho anchor) rho delta C
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
  obtain ⟨Cdelta, hCdelta, hwall⟩ :=
    exists_sectionSixTerminalVBaseXCoreLocalWallSupportMass_delta_upper
      delta hdelta
  refine ⟨Cdelta, hCdelta, ?_⟩
  intro epsilon hepsilon
  obtain ⟨length0, hlength0, hwallAt⟩ := hwall epsilon hepsilon
  refine ⟨length0, ?_, ?_⟩
  · exact hlength0
  · intro length hlength digit ell M region band sourcePresentation pattern
    dsimp only
    intro hepsilonSmall hdeltaGapStrict hrhoSq hnonempty
    have hlengthOne : 1 <= length := hlength0.trans hlength
    obtain ⟨candidate, hcandidate⟩ := hnonempty
    have hrealized := sectionSixTerminalVStablePattern_realizedData_of_mem
      hepsilon hepsilonSmall hlengthOne hdeltaGapStrict hrhoSq hcandidate
    obtain ⟨hinner, hresidual, harity, _hstrict⟩ := hrealized
    let n := ((pattern.1.1 + ell) + pattern.2.1.1) - 2
    have hdimension :
        (pattern.1.1 + ell) + pattern.2.1.1 = n + 2 := by
      dsimp only [n]
      omega
    refine ⟨hinner, hresidual, n, hdimension, ?_⟩
    intro j
    have hwallJ := hwallAt length hlength digit ell M region band
      sourcePresentation pattern hinner hresidual n hdimension j
    dsimp only at hwallJ ⊢
    exact hwallJ (by simpa only [hdimension] using harity)

end

end PrimesRestrictedDigits
