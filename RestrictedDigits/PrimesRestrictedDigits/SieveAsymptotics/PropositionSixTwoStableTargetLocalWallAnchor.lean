import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetPresentation
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixProjectedFactorsLocalWallAnchor
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddingComplementFactorization

/-!
# Proposition 6.2 reverse target-wall local anchor

One literal displayed wall for a complete tuple already in a fixed Proposition 6.2 target is
transported to the exact projected cell geometry used by Proposition 7.2. This is the reverse
boundary-cell step in the proof of Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/--
A complete Proposition 6.2 target tuple on one selected reverse displayed wall belongs to an
exact locally admissible cell after canonical dimension transport.
-/
theorem
    propositionSixTwoStableTargetFactors_exists_locallyAdmissibleWallAnchor
    {epsilon rho : Real} {ell length M N : Nat}
    {I : Finset (Fin ell)} {sourceRegion : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    {C : Finset Nat} {pattern : PropositionSixTwoStablePattern ell M}
    (hell : 0 < ell) (hresidual : 0 < pattern.1.1)
    {factors : Fin (ell + pattern.1.1) -> Nat}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hrho : 0 < rho)
    (hmarginWidth :
      2 * rho <= sectionSixThetaGap epsilon / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <=
        epsilon)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (hprime : ∀ z, (factors z).Prime)
    (hproduct : primeTupleProduct factors = N)
    (htarget :
      (fun z => normalizedPrimeLog N (factors z)) ∈
        propositionSixTwoStableTargetRegion
          epsilon I sourceRegion band pattern)
    (hNC : N ∈ C)
    (c : Fin (propositionSixTwoDisplayedPresentation sourcePresentation
      epsilon I band).constraintCount)
    (hnormal : (propositionSixTwoDisplayedPresentation sourcePresentation
      epsilon I band).normal c ≠ 0)
    (hwall :
      |typeIIAffineValue
          ((propositionSixTwoDisplayedPresentation sourcePresentation
            epsilon I band).normal c)
          (fun i => normalizedPrimeLog N (factors (pattern.2 i))) -
        (propositionSixTwoDisplayedPresentation sourcePresentation
          epsilon I band).bound c| <=
      rho ^ 2 * typeIIAffineNormalMass
        ((propositionSixTwoDisplayedPresentation sourcePresentation
          epsilon I band).normal c)) :
    ∃ n : Nat,
      ∃ hdimension : ell + pattern.1.1 = n + 2,
        let P := propositionSixTwoDisplayedPresentation sourcePresentation
          epsilon I band
        let cast := Fin.castOrderIso hdimension
        let transportedEmbedding :=
          pattern.2.trans cast.toEquiv.toEmbedding
        let transportedFactors : Fin (n + 2) -> Nat := fun z =>
          factors (cast.symm z)
        let fullNormal : Fin (n + 2) -> Real :=
          typeIIAffineLiftNormal transportedEmbedding (P.normal c)
        typeIIProjectedAffineNormal fullNormal ≠ 0 ∧
        (∀ z, (transportedFactors z).Prime) ∧
        primeTupleProduct transportedFactors = N ∧
        ∃ anchor,
          anchor ∈ typeIIAffineThickSlabAnchors rho
              (rho ^ 2 * typeIIAffineNormalMass (P.normal c))
              (typeIIProjectedAffineNormal fullNormal)
              (typeIIProjectedAffineBound fullNormal (P.bound c)) ∧
          (∀ z, sectionSixThetaGap epsilon / 2 <=
            scaledNaturalCubeAnchor rho anchor z) ∧
          (∑ z, scaledNaturalCubeAnchor rho anchor z) <
            1 - sectionSixThetaGap epsilon / 2 ∧
          (∃ J : Finset (Fin (n + 1)),
            (∑ z ∈ J, scaledNaturalCubeAnchor rho anchor z) ∈
                Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
            (∑ z ∈ J, scaledNaturalCubeAnchor rho anchor z) ∈
                Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon)) ∧
          transportedFactors ∈ majorArcPrimeTuples (10 ^ length)
            (scaledNaturalCubeAnchor rho anchor) rho
              (sectionSixThetaGap epsilon) ∧
          N ∈
            (primeTupleProductSupport
              (majorArcPrimeTuples (10 ^ length)
                (scaledNaturalCubeAnchor rho anchor) rho
                  (sectionSixThetaGap epsilon))).filter (fun m => m ∈ C) := by
  let n := ell + pattern.1.1 - 2
  have hdimension : ell + pattern.1.1 = n + 2 := by
    dsimp only [n]
    omega
  refine ⟨n, hdimension, ?_⟩
  let P := propositionSixTwoDisplayedPresentation sourcePresentation
    epsilon I band
  let cast : Fin (ell + pattern.1.1) ≃o Fin (n + 2) :=
    Fin.castOrderIso hdimension
  let transportedEmbedding : Fin ell ↪ Fin (n + 2) :=
    pattern.2.trans cast.toEquiv.toEmbedding
  let transportedFactors : Fin (n + 2) -> Nat := fun z =>
    factors (cast.symm z)
  let fullNormal : Fin (n + 2) -> Real :=
    typeIIAffineLiftNormal transportedEmbedding (P.normal c)
  let point : Fin (n + 2) -> Real := fun z =>
    normalizedPrimeLog N (transportedFactors z)
  let rawSpare : Fin (ell + pattern.1.1) :=
    typeIIComplementPositionEmbedding pattern.2 ⟨0, hresidual⟩
  let spare : Fin (n + 2) := cast rawSpare
  have hrawSpare : rawSpare ∉ Set.range pattern.2 := by
    rw [← mem_range_typeIIComplementPositionEmbedding_iff pattern.2]
    exact ⟨⟨0, hresidual⟩, rfl⟩
  have hspare : spare ∉ Set.range transportedEmbedding := by
    rintro ⟨i, hi⟩
    apply hrawSpare
    refine ⟨i, ?_⟩
    apply cast.injective
    change cast (pattern.2 i) = cast rawSpare at hi
    exact hi
  have hprojected : typeIIProjectedAffineNormal fullNormal ≠ 0 := by
    exact typeIIProjectedAffineNormal_lift_ne_zero_of_offRange
      transportedEmbedding (P.normal c) hnormal hspare
  have hprimeTransported : ∀ z, (transportedFactors z).Prime := fun z =>
    hprime (cast.symm z)
  have hproductTransported :
      primeTupleProduct transportedFactors = N := by
    unfold primeTupleProduct transportedFactors
    exact (Equiv.prod_comp cast.symm.toEquiv factors).trans hproduct
  have hsimplexOriginal :=
    (mem_propositionSixTwoStableTargetRegion.mp htarget).1
  have hsimplexTransported : point ∈
      typeIIExponentSimplex (sectionSixThetaGap epsilon) := by
    refine ⟨?_, ?_, ?_⟩
    · intro z
      exact hsimplexOriginal.1 (cast.symm z)
    · intro z z' hzz'
      exact hsimplexOriginal.2.1 (cast.symm.monotone hzz')
    · exact (Equiv.sum_comp cast.symm.toEquiv
        (fun z => normalizedPrimeLog N (factors z))).trans
          hsimplexOriginal.2.2
  have hsumPoint : (∑ z, point z) = 1 := hsimplexTransported.2.2
  have hcomplete : completeProjectedLogTuple (Fin.init point) = point :=
    completeProjectedLogTuple_init_eq_of_sum_eq_one hsumPoint
  have hfullWall :
      |typeIIAffineValue fullNormal point - P.bound c| <=
        rho ^ 2 * typeIIAffineNormalMass (P.normal c) := by
    rw [typeIIAffineValue_liftNormal]
    change
      |typeIIAffineValue (P.normal c)
          (fun i => normalizedPrimeLog N
            (factors (cast.symm (cast (pattern.2 i))))) - P.bound c| <=
        rho ^ 2 * typeIIAffineNormalMass (P.normal c)
    simpa only [cast.symm_apply_apply, P] using hwall
  have hprojectedValue :=
    typeIIAffineValue_completeProjectedLogTuple fullNormal (Fin.init point)
  rw [hcomplete] at hprojectedValue
  have hprojectedWall :
      |typeIIAffineValue (typeIIProjectedAffineNormal fullNormal)
            (Fin.init point) -
          typeIIProjectedAffineBound fullNormal (P.bound c)| <=
        rho ^ 2 * typeIIAffineNormalMass (P.normal c) := by
    have hrewrite :
        typeIIAffineValue (typeIIProjectedAffineNormal fullNormal)
              (Fin.init point) -
            typeIIProjectedAffineBound fullNormal (P.bound c) =
          typeIIAffineValue fullNormal point - P.bound c := by
      unfold typeIIProjectedAffineBound
      rw [hprojectedValue]
      ring
    rw [hrewrite]
    exact hfullWall
  obtain ⟨positions, hpositions⟩ :=
    propositionSixTwoStableTargetRegion_convenient_two_mul
      epsilon I sourceRegion band pattern
  let transportedPositions : Finset (Fin (n + 2)) :=
    positions.map cast.toEmbedding
  have hconvenientPoint :
      ∃ positions : Finset (Fin (n + 2)),
        (∑ z ∈ positions, normalizedPrimeLog N (transportedFactors z)) ∈
          Set.Icc (9 / 25 + 2 * epsilon)
            (17 / 40 - 2 * epsilon) := by
    refine ⟨transportedPositions, ?_⟩
    have hpositionsAt := hpositions
      (fun z => normalizedPrimeLog N (factors z)) htarget
    simpa [transportedPositions, transportedFactors] using hpositionsAt
  have heta : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hetaLtOne : sectionSixThetaGap epsilon < 1 := by
    rw [sectionSixThetaGap_eq]
    linarith
  have hrhoHalf : rho <= 1 / 2 := by
    linarith
  let i0 : Fin (ell + pattern.1.1) :=
    Fin.castAdd pattern.1.1 ⟨0, hell⟩
  have hi0Le : factors i0 <= primeTupleProduct factors :=
    primeTupleCoordinate_le_product (fun z => (hprime z).one_le) i0
  have hN : 1 < N := by
    rw [hproduct] at hi0Le
    exact (hprime i0).one_lt.trans_le hi0Le
  have hX : 1 < 10 ^ length :=
    hN.trans (mem_typeIINearXCarrier.mp hnear).1
  have hlength : 1 <= length := by
    by_contra hlength
    have hzero : length = 0 := by omega
    subst length
    norm_num at hX
  have hconvenienceWidth' :
      rho ^ 2 + (((n + 1 : Nat) : Real) * rho) <= epsilon := by
    have hcount : ell + pattern.1.1 - 1 = n + 1 := by omega
    rw [← hcount]
    exact hconvenienceWidth
  refine ⟨hprojected, hprimeTransported, hproductTransported, ?_⟩
  exact projectedFactors_exists_locallyAdmissibleWallAnchor
    hlength heta hrho hrhoHalf hmarginWidth hconvenienceWidth' hnear
      hprimeTransported hproductTransported hsimplexTransported
        hconvenientPoint hNC hprojected hprojectedWall

end

end PrimesRestrictedDigits
