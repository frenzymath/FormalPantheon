import PrimesRestrictedDigits.SieveAsymptotics.SectionSixProjectedFactorsLocalWallAnchor
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreWallProjection
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetConvenience

/-!
# Locally admissible anchors for terminal-V BaseX walls

This module reindexes one literal terminal-V BaseX-core wall and its exact prime tuple to the
positive projected dimension, then applies the common locally admissible wall-cell kernel.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/--
A terminal-V target tuple on one selected BaseX-core wall lies in an exact locally admissible
cell after canonical dimension transport.
-/
theorem
    sectionSixTerminalVStableTargetFactors_exists_locallyAdmissibleWallAnchor
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} (band : SectionSixStateBand)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    {C : Finset Nat}
    {factors : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Nat}
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 +
          ((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho <=
        epsilon)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (hprime : ∀ i, (factors i).Prime)
    (hproduct : primeTupleProduct factors = N)
    (htarget :
      (fun i => normalizedPrimeLog N (factors i)) ∈
        sectionSixTerminalVStableTargetRegion
          epsilon delta region band pattern)
    (hNC : N ∈ C)
    (j : Fin (sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual).constraintCount)
    (hnormal : (sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual).normal j ≠ 0)
    (hwall :
      |typeIIAffineValue
          ((sectionSixTerminalVBaseXCorePresentation sourcePresentation
            epsilon delta band pattern hinner hresidual).normal j)
          (fun i => normalizedPrimeLog N (factors i)) -
        (sectionSixTerminalVBaseXCorePresentation sourcePresentation
          epsilon delta band pattern hinner hresidual).bound j| <=
      rho ^ 2 * typeIIAffineNormalMass
        ((sectionSixTerminalVBaseXCorePresentation sourcePresentation
          epsilon delta band pattern hinner hresidual).normal j)) :
    ∃ n : Nat,
      ∃ hdimension :
          (pattern.1.1 + ell) + pattern.2.1.1 = n + 2,
        let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
          epsilon delta band pattern hinner hresidual
        let cast := Fin.castOrderIso hdimension
        let transportedFactors : Fin (n + 2) -> Nat := fun i =>
          factors (cast.symm i)
        let fullNormal : Fin (n + 2) -> Real := fun i =>
          P.normal j (cast.symm i)
        typeIIProjectedAffineNormal fullNormal ≠ 0 ∧
        (∀ i, (transportedFactors i).Prime) ∧
        primeTupleProduct transportedFactors = N ∧
        ∃ anchor,
          anchor ∈ typeIIAffineThickSlabAnchors rho
              (rho ^ 2 * typeIIAffineNormalMass (P.normal j))
              (typeIIProjectedAffineNormal fullNormal)
              (typeIIProjectedAffineBound fullNormal (P.bound j)) ∧
          (∀ i, delta / 2 <= scaledNaturalCubeAnchor rho anchor i) ∧
          (∑ i, scaledNaturalCubeAnchor rho anchor i) < 1 - delta / 2 ∧
          (∃ I : Finset (Fin (n + 1)),
            (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
                Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
            (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
                Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon)) ∧
          transportedFactors ∈ majorArcPrimeTuples (10 ^ length)
            (scaledNaturalCubeAnchor rho anchor) rho delta ∧
          N ∈
            (primeTupleProductSupport
              (majorArcPrimeTuples (10 ^ length)
                (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
              (fun m => m ∈ C) := by
  have hsimplexOriginal :=
    (mem_sectionSixTerminalVStableTargetRegion.mp htarget).2.2.1
  obtain ⟨n, hdimension, hprojected, hprojectedWall⟩ :=
    sectionSixTerminalVBaseXCoreWall_exists_projected band sourcePresentation
      pattern hinner hresidual
        (fun i => normalizedPrimeLog N (factors i)) hsimplexOriginal.2.2
          j hnormal hwall
  refine ⟨n, hdimension, ?_⟩
  let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
    epsilon delta band pattern hinner hresidual
  let cast :
      Fin ((pattern.1.1 + ell) + pattern.2.1.1) ≃o Fin (n + 2) :=
    Fin.castOrderIso hdimension
  let transportedFactors : Fin (n + 2) -> Nat := fun i =>
    factors (cast.symm i)
  let fullNormal : Fin (n + 2) -> Real := fun i =>
    P.normal j (cast.symm i)
  have hprimeTransported : ∀ i, (transportedFactors i).Prime := fun i =>
    hprime (cast.symm i)
  have hproductTransported : primeTupleProduct transportedFactors = N := by
    unfold primeTupleProduct transportedFactors
    exact (Equiv.prod_comp cast.symm.toEquiv factors).trans hproduct
  have hsimplexTransported :
      (fun i => normalizedPrimeLog N (transportedFactors i)) ∈
        typeIIExponentSimplex delta := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact hsimplexOriginal.1 (cast.symm i)
    · intro i i' hii'
      exact hsimplexOriginal.2.1 (cast.symm.monotone hii')
    · exact (Equiv.sum_comp cast.symm.toEquiv
        (fun i => normalizedPrimeLog N (factors i))).trans
          hsimplexOriginal.2.2
  obtain ⟨positions, hpositions⟩ :=
    sectionSixTerminalVStableTargetRegion_convenient_two_mul
      (epsilon := epsilon) (delta := delta) region band pattern
  have hpositionsAt := hpositions
    (fun i => normalizedPrimeLog N (factors i)) htarget
  let transportedPositions : Finset (Fin (n + 2)) :=
    positions.map cast.toEmbedding
  have hconvenientPoint :
      ∃ positions : Finset (Fin (n + 2)),
        (∑ q ∈ positions, normalizedPrimeLog N (transportedFactors q)) ∈
          Set.Icc (9 / 25 + 2 * epsilon) (17 / 40 - 2 * epsilon) := by
    refine ⟨transportedPositions, ?_⟩
    simpa [transportedPositions, transportedFactors] using hpositionsAt
  have hconvenienceWidth' :
      rho ^ 2 + (((n + 1 : Nat) : Real) * rho) <= epsilon := by
    have hcount :
        ((pattern.1.1 + ell) + pattern.2.1.1) - 1 = n + 1 := by omega
    rw [← hcount]
    exact hconvenienceWidth
  have hprojected' : typeIIProjectedAffineNormal fullNormal ≠ 0 := by
    simpa only [P, cast, fullNormal] using hprojected
  have hprojectedWall' :
      |typeIIAffineValue (typeIIProjectedAffineNormal fullNormal)
            (Fin.init (fun i => normalizedPrimeLog N (transportedFactors i))) -
          typeIIProjectedAffineBound fullNormal (P.bound j)| <=
        rho ^ 2 * typeIIAffineNormalMass (P.normal j) := by
    simpa only [P, cast, fullNormal, transportedFactors] using hprojectedWall
  refine ⟨hprojected', hprimeTransported, hproductTransported, ?_⟩
  exact projectedFactors_exists_locallyAdmissibleWallAnchor
    hlength hdelta hrho hrhoHalf hmarginWidth hconvenienceWidth' hnear
      hprimeTransported hproductTransported hsimplexTransported
        hconvenientPoint hNC hprojected' hprojectedWall'

end


end PrimesRestrictedDigits
