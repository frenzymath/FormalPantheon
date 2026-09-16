import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetBaseXCore
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineThickSlabCount
import PrimesRestrictedDigits.SieveAsymptotics.TypeIICubeFamily

/-!
# Terminal-V BaseX-core local wall anchors

This packages the finite logarithmic grid cells attached to one literal wall of the terminal-V
BaseX core. It is the terminal-V wall family used in the proof of Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Locally admissible anchors attached to one literal occurrence of a
terminal-V BaseX-core wall. -/
noncomputable def sectionSixTerminalVBaseXCoreLocalWallAnchors
    (epsilon delta rho : Real) {ell M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (n : Nat)
    (hdimension : (pattern.1.1 + ell) + pattern.2.1.1 = n + 2)
    (j : Fin (sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual).constraintCount) :
    Finset (Fin (n + 1) -> Nat) := by
  classical
  let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
    epsilon delta band pattern hinner hresidual
  let cast := Fin.castOrderIso hdimension
  let fullNormal : Fin (n + 2) -> Real := fun i => P.normal j (cast.symm i)
  let normal := typeIIProjectedAffineNormal fullNormal
  let bound := typeIIProjectedAffineBound fullNormal (P.bound j)
  let gamma := rho ^ 2 * typeIIAffineNormalMass (P.normal j)
  exact (typeIIAffineThickSlabAnchors rho gamma normal bound).filter fun anchor =>
    (forall i, delta / 2 <= scaledNaturalCubeAnchor rho anchor i) ∧
      (∑ i, scaledNaturalCubeAnchor rho anchor i) < 1 - delta / 2 ∧
      ∃ I : Finset (Fin (n + 1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon)

@[simp] theorem mem_sectionSixTerminalVBaseXCoreLocalWallAnchors
    {epsilon delta rho : Real} {ell M n : Nat}
    {region : Set (Fin ell -> Real)}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {band : SectionSixStateBand}
    {pattern : SectionSixTerminalVStablePattern ell M}
    {hinner : 0 < pattern.1.1} {hresidual : 0 < pattern.2.1.1}
    {hdimension : (pattern.1.1 + ell) + pattern.2.1.1 = n + 2}
    {j : Fin (sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual).constraintCount}
    {anchor : Fin (n + 1) -> Nat} :
    anchor ∈ sectionSixTerminalVBaseXCoreLocalWallAnchors epsilon delta rho
        sourcePresentation band pattern hinner hresidual n hdimension j ↔
      let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
        epsilon delta band pattern hinner hresidual
      let cast := Fin.castOrderIso hdimension
      let fullNormal : Fin (n + 2) -> Real := fun i =>
        P.normal j (cast.symm i)
      anchor ∈ typeIIAffineThickSlabAnchors rho
          (rho ^ 2 * typeIIAffineNormalMass (P.normal j))
          (typeIIProjectedAffineNormal fullNormal)
          (typeIIProjectedAffineBound fullNormal (P.bound j)) ∧
        (forall i, delta / 2 <= scaledNaturalCubeAnchor rho anchor i) ∧
        (∑ i, scaledNaturalCubeAnchor rho anchor i) < 1 - delta / 2 ∧
        ∃ I : Finset (Fin (n + 1)),
          (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
              Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
          (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
              Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon) := by
  classical
  simp [sectionSixTerminalVBaseXCoreLocalWallAnchors]

end

end PrimesRestrictedDigits
