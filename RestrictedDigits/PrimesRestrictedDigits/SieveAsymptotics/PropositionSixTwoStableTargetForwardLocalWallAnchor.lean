import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetPresentation
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixProjectedFactorsLocalWallAnchor
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddingComplementFactorization

/-!
# Proposition 6.2 forward base-X wall local anchor

This is the forward counterpart of the reverse target-wall adapter. The selected wall is
measured at the base-N point, while convenience is recovered from the displayed base-X region.
See the proof of Lemma 7.3 in `MAYNARD-PRD-PUBLISHED`, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem propositionSixTwoForward_sumPrefixIndexSet_eq
    {k : Nat} (positions : Finset (Fin (k + 1)))
    (x : Fin (k + 1) -> Real) (hlast : Fin.last k ∉ positions) :
    (∑ i ∈ typeIIPrefixIndexSet positions, x i.castSucc) =
      ∑ j ∈ positions, x j := by
  rw [typeIIPrefixIndexSet, Finset.sum_filter]
  have hall := Fin.sum_univ_castSucc
    (fun j => if j ∈ positions then x j else 0)
  simp only [hlast, if_false, add_zero] at hall
  rw [← hall]
  have hfilter :=
    (Finset.sum_filter (s := Finset.univ) (fun j => j ∈ positions) x).symm
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hfilter
  exact hfilter

private theorem propositionSixTwoForward_oneWidthSubsetSum_bounds
    {k : Nat} {rho : Real} {anchor : Fin k -> Nat}
    {z : Fin k -> Real} (hrho : 0 <= rho)
    (hz : z ∈ projectedLogBox (scaledNaturalCubeAnchor rho anchor) rho)
    (I : Finset (Fin k)) :
    (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) <= ∑ i ∈ I, z i ∧
      (∑ i ∈ I, z i) <=
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (k : Real) * rho := by
  constructor
  · exact Finset.sum_le_sum fun i _ => (hz i).1.le
  · calc
      (∑ i ∈ I, z i) <=
          ∑ i ∈ I, (scaledNaturalCubeAnchor rho anchor i + rho) :=
        Finset.sum_le_sum fun i _ => (hz i).2
      _ = (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (I.card : Real) * rho := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
      _ <= (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (k : Real) * rho := by
        gcongr
        simpa using Finset.card_le_univ I

/-- A complete forward tuple on one selected displayed wall belongs to an
exact projected cell whose convenience interval is obtained from the
base-X displayed band. -/
theorem
    propositionSixTwoStableTargetFactors_exists_forwardLocalWallAnchor
    {epsilon rho : Real} {ell length M N : Nat}
    {I : Finset (Fin ell)} {sourceRegion : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    {C : Finset Nat} {pattern : PropositionSixTwoStablePattern ell M}
    (hell : 0 < ell) (hresidual : 0 < pattern.1.1)
    (hlength : 1 <= length)
    (hdelta : 0 < sectionSixThetaGap epsilon)
    (hrho : 0 < rho) (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <= epsilon)
    {factors : Fin (ell + pattern.1.1) -> Nat}
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (hprime : ∀ z, (factors z).Prime)
    (hproduct : primeTupleProduct factors = N)
    (hsimplex : (fun z => normalizedPrimeLog N (factors z)) ∈
      typeIIExponentSimplex (sectionSixThetaGap epsilon))
    (hdisplayX : (fun i => normalizedPrimeLog (10 ^ length)
      (factors (pattern.2 i))) ∈
      propositionSixTwoDisplayedRegion epsilon I sourceRegion band)
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
        let transportedEmbedding := pattern.2.trans cast.toEquiv.toEmbedding
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
          N ∈ (primeTupleProductSupport
            (majorArcPrimeTuples (10 ^ length)
              (scaledNaturalCubeAnchor rho anchor) rho
                (sectionSixThetaGap epsilon))).filter (fun m => m ∈ C) := by
  let d := ell + pattern.1.1
  let n := d - 2
  have hdimension : d = n + 2 := by
    dsimp only [n]
    omega
  refine ⟨n, hdimension, ?_⟩
  let P := propositionSixTwoDisplayedPresentation sourcePresentation
    epsilon I band
  let cast : Fin d ≃o Fin (n + 2) := Fin.castOrderIso hdimension
  let transportedEmbedding : Fin ell ↪ Fin (n + 2) :=
    pattern.2.trans cast.toEquiv.toEmbedding
  let transportedFactors : Fin (n + 2) -> Nat := fun z =>
    factors (cast.symm z)
  let fullNormal : Fin (n + 2) -> Real :=
    typeIIAffineLiftNormal transportedEmbedding (P.normal c)
  let eN : Fin (n + 2) -> Real := fun z =>
    normalizedPrimeLog N (transportedFactors z)
  let eX : Fin (n + 2) -> Real := fun z =>
    normalizedPrimeLog (10 ^ length) (transportedFactors z)
  let rawSpare : Fin d :=
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
  have hsimplexTransported : eN ∈
      typeIIExponentSimplex (sectionSixThetaGap epsilon) := by
    refine ⟨?_, ?_, ?_⟩
    · intro z
      exact hsimplex.1 (cast.symm z)
    · intro z z' hzz'
      exact hsimplex.2.1 (cast.symm.monotone hzz')
    · exact (Equiv.sum_comp cast.symm.toEquiv
        (fun z => normalizedPrimeLog N (factors z))).trans
          hsimplex.2.2
  have hprojectedValue :=
    typeIIAffineValue_completeProjectedLogTuple fullNormal (Fin.init eN)
  have hsumN : (∑ z, eN z) = 1 := hsimplexTransported.2.2
  have hcomplete : completeProjectedLogTuple (Fin.init eN) = eN :=
    completeProjectedLogTuple_init_eq_of_sum_eq_one hsumN
  rw [hcomplete] at hprojectedValue
  have hfullWall :
      |typeIIAffineValue fullNormal eN - P.bound c| <=
        rho ^ 2 * typeIIAffineNormalMass (P.normal c) := by
    rw [typeIIAffineValue_liftNormal]
    change
      |typeIIAffineValue (P.normal c)
          (fun i => normalizedPrimeLog N
            (factors (cast.symm (cast (pattern.2 i))))) - P.bound c| <=
        rho ^ 2 * typeIIAffineNormalMass (P.normal c)
    simpa only [cast.symm_apply_apply, P] using hwall
  have hprojectedWall :
      |typeIIAffineValue (typeIIProjectedAffineNormal fullNormal)
            (Fin.init eN) - typeIIProjectedAffineBound fullNormal (P.bound c)| <=
        rho ^ 2 * typeIIAffineNormalMass (P.normal c) := by
    have hrewrite :
        typeIIAffineValue (typeIIProjectedAffineNormal fullNormal)
              (Fin.init eN) - typeIIProjectedAffineBound fullNormal (P.bound c) =
          typeIIAffineValue fullNormal eN - P.bound c := by
      unfold typeIIProjectedAffineBound
      rw [hprojectedValue]
      ring
    rw [hrewrite]
    exact hfullWall
  obtain ⟨anchor, hslab, hcell⟩ :=
    projectedFactors_exists_crossedWallAnchor hlength hdelta hrho hrhoHalf
      hnear hprimeTransported hproductTransported
        (hsimplexTransported.1 (Fin.last (n + 1))) hprojected hprojectedWall
  have hX : 1 < 10 ^ length := by
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hN : 1 < N :=
    one_lt_of_mem_typeIINearXCarrier hX hrho hrhoHalf hnear
  have hNX : N < 10 ^ length := (mem_typeIINearXCarrier.mp hnear).1
  have hpLe (z : Fin (n + 2)) : transportedFactors z <= N := by
    rw [← hproductTransported]
    exact primeTupleCoordinate_le_product
      (fun q => (hprimeTransported q).one_le) z
  have hcellData := mem_majorArcPrimeTuples_iff.mp hcell
  have hzCell : (fun z : Fin (n + 1) => eX z.castSucc) ∈
      projectedLogBox (scaledNaturalCubeAnchor rho anchor) rho := by
    simpa only [eX, Fin.init_def] using hcellData.2.1
  have heCell : ∀ z : Fin (n + 1),
      eN z.castSucc ∈ Set.Ioc (scaledNaturalCubeAnchor rho anchor z)
        (scaledNaturalCubeAnchor rho anchor z + 2 * rho) := by
    intro z
    exact normalizedPrimeLog_mem_doubled_Ioc_of_near hX hrho hrhoHalf hnear
      (hprimeTransported z.castSucc) (hpLe z.castSucc)
      (by simpa only [eX] using hzCell z)
  have hmargin : ∀ z : Fin (n + 1),
      sectionSixThetaGap epsilon / 2 <= scaledNaturalCubeAnchor rho anchor z := by
    intro z
    linarith [hsimplexTransported.1 z.castSucc, (heCell z).2]
  have hsumPrefix :
      (∑ z, scaledNaturalCubeAnchor rho anchor z) <=
        ∑ z : Fin (n + 1), eN z.castSucc :=
    Finset.sum_le_sum fun z _ => (heCell z).1.le
  have hsumDecomposition :
      (∑ z : Fin (n + 1), eN z.castSucc) + eN (Fin.last (n + 1)) = 1 := by
    exact (Fin.sum_univ_castSucc eN).symm.trans hsumN
  have hroom : (∑ z, scaledNaturalCubeAnchor rho anchor z) <
      1 - sectionSixThetaGap epsilon / 2 := by
    linarith [hsimplexTransported.1 (Fin.last (n + 1))]
  have hsumX : (∑ z, eX z) = normalizedPrimeLog (10 ^ length) N := by
    calc
      (∑ z, eX z) =
          ∑ z, normalizedPrimeLog (10 ^ length) (factors z) :=
        Equiv.sum_comp cast.symm.toEquiv
          (fun z => normalizedPrimeLog (10 ^ length) (factors z))
      _ = normalizedPrimeLog (10 ^ length) N := by
        rw [sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
          (fun z => (hprime z).ne_zero), hproduct]
  have hratio := normalizedPrimeLog_near_bounds hX
    (mem_typeIINearXCarrier.mp hnear).2 hNX
  have hwidth :
      rho ^ 2 + (((n + 1 : Nat) : Real) * rho) <= epsilon := by
    have hcount : d - 1 = n + 1 := by omega
    rw [← hcount]
    exact hconvenienceWidth
  let rawPositions := pattern.selectedPositions I
  let positions : Finset (Fin (n + 2)) := rawPositions.map cast.toEmbedding
  have hdisplayedX : (∑ z ∈ positions, eX z) =
      ∑ i ∈ I, normalizedPrimeLog (10 ^ length) (factors (pattern.2 i)) := by
    simpa [positions, rawPositions, eX, transportedFactors] using
      sum_propositionSixTwoStablePattern_selectedPositions pattern I
        (fun z => normalizedPrimeLog (10 ^ length) (factors z))
  have hdisplayData := mem_propositionSixTwoDisplayedRegion.mp hdisplayX
  have hbandBounds :
      propositionSixTwoBandLower epsilon band <=
          ∑ i ∈ I, normalizedPrimeLog (10 ^ length) (factors (pattern.2 i)) ∧
        (∑ i ∈ I, normalizedPrimeLog (10 ^ length) (factors (pattern.2 i))) <=
          propositionSixTwoBandUpper epsilon band := ⟨hdisplayData.2.2.1,
        hdisplayData.2.2.2⟩
  have htransport
      (selected : Finset (Fin (n + 2)))
      (hlast : Fin.last (n + 1) ∉ selected)
      (lower upper : Real)
      (hlower : lower + 2 * epsilon - rho ^ 2 < ∑ z ∈ selected, eX z)
      (hupper : (∑ z ∈ selected, eX z) <= upper - 2 * epsilon) :
      ∃ J : Finset (Fin (n + 1)),
        (∑ z ∈ J, scaledNaturalCubeAnchor rho anchor z) ∈
          Set.Icc (lower + epsilon) (upper - epsilon) := by
    let J := typeIIPrefixIndexSet selected
    have hprefix : (∑ z ∈ J, eX z.castSucc) = ∑ z ∈ selected, eX z := by
      simpa only [J] using propositionSixTwoForward_sumPrefixIndexSet_eq
        selected eX hlast
    have hmove := propositionSixTwoForward_oneWidthSubsetSum_bounds
      hrho.le hzCell J
    rw [hprefix] at hmove
    refine ⟨J, ?_⟩
    constructor <;> linarith
  have hconvenient :
      ∃ J : Finset (Fin (n + 1)),
        (∑ z ∈ J, scaledNaturalCubeAnchor rho anchor z) ∈
            Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
        (∑ z ∈ J, scaledNaturalCubeAnchor rho anchor z) ∈
            Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon) := by
    by_cases hlast : Fin.last (n + 1) ∈ positions
    · let complement : Finset (Fin (n + 2)) := Finset.univ \ positions
      have hlastComplement : Fin.last (n + 1) ∉ complement := by
        simp [complement, hlast]
      have hsumComplement :
          (∑ z ∈ complement, eX z) =
            normalizedPrimeLog (10 ^ length) N -
              ∑ z ∈ positions, eX z := by
        rw [show complement = Finset.univ \ positions by rfl,
          Finset.sum_sdiff_eq_sub (Finset.subset_univ positions)]
        change (∑ z, eX z) - (∑ z ∈ positions, eX z) = _
        rw [hsumX]
      cases band with
      | first =>
          obtain ⟨J, hJ⟩ := htransport complement hlastComplement
            (23 / 40) (16 / 25)
              (by
                rw [hsumComplement, hdisplayedX]
                simp only [propositionSixTwoBandLower,
                  propositionSixTwoBandUpper,
                  sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
                linarith [hratio.1])
              (by
                rw [hsumComplement, hdisplayedX]
                simp only [propositionSixTwoBandLower,
                  propositionSixTwoBandUpper,
                  sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
                linarith [hratio.2])
          exact ⟨J, Or.inr hJ⟩
      | second =>
          obtain ⟨J, hJ⟩ := htransport complement hlastComplement
            (9 / 25) (17 / 40)
              (by
                rw [hsumComplement, hdisplayedX]
                simp only [propositionSixTwoBandLower,
                  propositionSixTwoBandUpper,
                  sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
                linarith [hratio.1])
              (by
                rw [hsumComplement, hdisplayedX]
                simp only [propositionSixTwoBandLower,
                  propositionSixTwoBandUpper,
                  sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
                linarith [hratio.2])
          exact ⟨J, Or.inl hJ⟩
    · cases band with
      | first =>
          obtain ⟨J, hJ⟩ := htransport positions hlast
            (9 / 25) (17 / 40)
              (by
                rw [hdisplayedX]
                simp only [propositionSixTwoBandLower,
                  propositionSixTwoBandUpper,
                  sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
                linarith [sq_pos_of_pos hrho])
              (by
                rw [hdisplayedX]
                simp only [propositionSixTwoBandLower,
                  propositionSixTwoBandUpper,
                  sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
                linarith)
          exact ⟨J, Or.inl hJ⟩
      | second =>
          obtain ⟨J, hJ⟩ := htransport positions hlast
            (23 / 40) (16 / 25)
              (by
                rw [hdisplayedX]
                simp only [propositionSixTwoBandLower,
                  propositionSixTwoBandUpper,
                  sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
                linarith [sq_pos_of_pos hrho])
              (by
                rw [hdisplayedX]
                simp only [propositionSixTwoBandLower,
                  propositionSixTwoBandUpper,
                  sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
                linarith)
          exact ⟨J, Or.inr hJ⟩
  refine ⟨hprojected, hprimeTransported, hproductTransported, ?_⟩
  exact ⟨anchor, hslab, hmargin, hroom, hconvenient, hcell,
    Finset.mem_filter.mpr
      ⟨mem_primeTupleProductSupport.mpr ⟨transportedFactors, hcell,
        hproductTransported⟩, hNC⟩⟩

end

end PrimesRestrictedDigits
