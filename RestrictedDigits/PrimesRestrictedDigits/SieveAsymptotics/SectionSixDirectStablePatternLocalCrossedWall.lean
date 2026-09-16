import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternRealizedData
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternLandingData
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternCrossedWallAnchor

/-!
# Locally admissible crossed walls for direct stable patterns

This is the pointwise finite-wall bridge in the proof of Maynard's Lemma 7.3. It retains the
literal displayed constraint and assigns the unchanged factor tuple to a slab cell satisfying
the local hypotheses used by Proposition 9.1.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def sectionSixDirectLocalSourceEmbedding
    {ell M : Nat} (pattern : SectionSixDirectStablePattern ell M) :
    Fin ell ↪ Fin ((ell + pattern.1.1) + 1) where
  toFun i := pattern.canonicalDisplayedEmbedding i.succ
  inj' := fun _ _ h =>
    Fin.succ_injective ell (pattern.canonicalDisplayedEmbedding.injective h)

private noncomputable def sectionSixDirectLocalSourcePositions
    {ell M : Nat} (pattern : SectionSixDirectStablePattern ell M) :
    Finset (Fin ((ell + pattern.1.1) + 1)) :=
  Finset.univ.map (sectionSixDirectLocalSourceEmbedding pattern)

private theorem sum_sectionSixDirectLocalSourcePositions
    {ell M : Nat} (pattern : SectionSixDirectStablePattern ell M)
    (x : Fin ((ell + pattern.1.1) + 1) → Real) :
    (∑ j ∈ sectionSixDirectLocalSourcePositions pattern, x j) =
      ∑ i : Fin ell, x (pattern.canonicalDisplayedEmbedding i.succ) := by
  simp [sectionSixDirectLocalSourcePositions,
    sectionSixDirectLocalSourceEmbedding]

private noncomputable def sectionSixDirectPrefixPositions
    {k : Nat} (positions : Finset (Fin (k + 1))) : Finset (Fin k) :=
  Finset.univ.filter fun i => i.castSucc ∈ positions

private theorem sum_sectionSixDirectPrefixPositions_eq
    {k : Nat} (positions : Finset (Fin (k + 1)))
    (x : Fin (k + 1) → Real) (hlast : Fin.last k ∉ positions) :
    (∑ i ∈ sectionSixDirectPrefixPositions positions, x i.castSucc) =
      ∑ j ∈ positions, x j := by
  rw [sectionSixDirectPrefixPositions, Finset.sum_filter]
  have hall :=
    Fin.sum_univ_castSucc (fun j => if j ∈ positions then x j else 0)
  simp only [hlast, if_false, add_zero] at hall
  rw [← hall]
  have hfilter :=
    (Finset.sum_filter (s := Finset.univ)
      (fun j => j ∈ positions) x).symm
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hfilter
  exact hfilter

private theorem sectionSixDirectPrefixSubsetSum_bounds
    {k : Nat} {rho : Real} {anchor : Fin k → Nat}
    {z : Fin k → Real} (hrho : 0 ≤ rho)
    (hz : z ∈ projectedLogBox (scaledNaturalCubeAnchor rho anchor) rho)
    (I : Finset (Fin k)) :
    (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ≤
        ∑ i ∈ I, z i ∧
      (∑ i ∈ I, z i) ≤
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (k : Real) * rho := by
  constructor
  · exact Finset.sum_le_sum fun i _ => (hz i).1.le
  · calc
      (∑ i ∈ I, z i) ≤
          ∑ i ∈ I, (scaledNaturalCubeAnchor rho anchor i + rho) :=
        Finset.sum_le_sum fun i _ => (hz i).2
      _ = (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (I.card : Real) * rho := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
      _ ≤ (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (k : Real) * rho := by
        gcongr
        have hcard : I.card ≤ k := by
          simpa using Finset.card_le_univ I
        exact_mod_cast hcard

/-- A direct stable-pattern candidate either lands in the fixed target or is
carried by one literal displayed wall cell satisfying the local Proposition
9.1 margin, room, and ordered-subsum conditions. -/
theorem sectionSixDirectStablePattern_exists_locallyAdmissibleCrossedWallAnchor
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {C : Finset Nat}
    {pattern : SectionSixDirectStablePattern ell M}
    {candidate : SectionSixDirectCandidate ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 : Nat) : Real) * rho) <= epsilon)
    (hcandidate : candidate ∈
      sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band C M pattern) :
    candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
        (sectionSixDirectStableTargetRegion epsilon delta region band pattern) ∨
      ∃ j, ∃ anchor,
        anchor ∈ typeIIAffineThickSlabAnchors rho
            (rho ^ 2 * typeIIAffineNormalMass
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).normal j))
            (typeIIProjectedAffineNormal
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).normal j)))
            (typeIIProjectedAffineBound
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).normal j))
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).bound j)) ∧
        (∀ i, delta / 2 <= scaledNaturalCubeAnchor rho anchor i) ∧
        (∑ i, scaledNaturalCubeAnchor rho anchor i < 1 - delta / 2) ∧
        (∃ I : Finset (Fin (ell + pattern.1.1)),
          (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
              Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
          (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
              Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon)) ∧
        candidate.value ∈
          (primeTupleProductSupport
            (majorArcPrimeTuples (10 ^ length)
              (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
            (fun n => n ∈ C) := by
  have hdelta : 0 < delta := by
    linarith
  have hgapUpper : sectionSixThetaGap epsilon < 1 := by
    rw [sectionSixThetaGap_eq]
    linarith
  have hrhoLtOne : rho < 1 := by
    linarith
  have hrhoHalf : rho <= 1 / 2 := by
    linarith
  have hrhoSq : rho ^ 2 < delta := by
    nlinarith [mul_pos hrho (sub_pos.mpr hrhoLtOne)]
  have hslice :=
    mem_sectionSixDirectNearCandidatesOfStablePattern.mp hcandidate
  have hnearData := mem_sectionSixDirectNearCandidates.mp hslice.1
  have hnear : candidate.value ∈
      typeIINearXCarrier (10 ^ length) rho := hnearData.2
  have hcandidateData := mem_sectionSixDirectCandidates.mp hnearData.1
  have hvalueC : candidate.value ∈ C := by
    have hsift := mem_strictSiftedCarrier.mp hcandidateData.2
    have hdilation := mem_sieveDilation.mp hsift.1
    simpa only [SectionSixDirectCandidate.value,
      sectionSixDirectStrictKey] using hdilation
  obtain ⟨hresidual, _harity, _hembedding, spare, hspare, _hoffRange⟩ :=
    sectionSixDirectStablePattern_realizedData_of_mem hepsilon hepsilonSmall
      hlength hdelta hdeltaGapStrict hrhoSq hcandidate
  obtain ⟨factors, hprime, hproduct, hvalueOne, hvalueUpper,
      hsimplex, hdisplaySource, herror, hlanding⟩ :=
    sectionSixDirectStablePattern_exists_landingData_of_mem hepsilon
      hepsilonSmall hlength hdelta hdeltaGapStrict hrhoSq hcandidate
  have hcrossing :=
    sectionSixDirectStablePattern_landing_or_crossedDisplayedConstraint
      (sourcePresentation := sourcePresentation) spare hspare
      hsimplex.2.2 hdisplaySource herror hlanding
  rcases hcrossing with htarget | ⟨j, hnormal, hwall⟩
  · exact Or.inl htarget
  · obtain ⟨anchor, hslab, hcell⟩ :=
      sectionSixDirectStablePattern_exists_crossedWallAnchor
        (sourcePresentation := sourcePresentation) hlength hdelta hrho
        hrhoHalf hnear hprime hproduct
        (hsimplex.1 (Fin.last (ell + pattern.1.1))) j hnormal hwall
    have hX : 1 < 10 ^ length :=
      Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
    have hpLe (i : Fin ((ell + pattern.1.1) + 1)) :
        factors i <= candidate.value := by
      rw [← hproduct]
      exact primeTupleCoordinate_le_product (fun q => (hprime q).one_le) i
    have hcellData := mem_majorArcPrimeTuples_iff.mp hcell
    have hzCell : ∀ i : Fin (ell + pattern.1.1),
        normalizedPrimeLog (10 ^ length) (factors i.castSucc) ∈
          Set.Ioc (scaledNaturalCubeAnchor rho anchor i)
            (scaledNaturalCubeAnchor rho anchor i + rho) := by
      intro i
      simpa [majorArcLogRegion, projectedLogBox, Fin.init_def] using
        hcellData.2.1 i
    have heCell : ∀ i : Fin (ell + pattern.1.1),
        normalizedPrimeLog candidate.value (factors i.castSucc) ∈
          Set.Ioc (scaledNaturalCubeAnchor rho anchor i)
            (scaledNaturalCubeAnchor rho anchor i + 2 * rho) := by
      intro i
      exact normalizedPrimeLog_mem_doubled_Ioc_of_near hX hrho hrhoHalf
        hnear (hprime i.castSucc) (hpLe i.castSucc) (hzCell i)
    have hmargin : ∀ i : Fin (ell + pattern.1.1),
        delta / 2 <= scaledNaturalCubeAnchor rho anchor i := by
      intro i
      have hiLower := hsimplex.1 i.castSucc
      have hiUpper := (heCell i).2
      linarith
    have hkPositive : 0 < ell + pattern.1.1 :=
      Nat.add_pos_right ell hresidual
    have hsumStrict :
        (∑ i, scaledNaturalCubeAnchor rho anchor i) <
          ∑ i : Fin (ell + pattern.1.1),
            normalizedPrimeLog candidate.value (factors i.castSucc) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact (Finset.univ_nonempty_iff.mpr
          (Fin.pos_iff_nonempty.mp hkPositive))
      · intro i _
        exact (heCell i).1
    have hsumDecomposition :
        (∑ i : Fin (ell + pattern.1.1),
            normalizedPrimeLog candidate.value (factors i.castSucc)) +
          normalizedPrimeLog candidate.value
            (factors (Fin.last (ell + pattern.1.1))) = 1 := by
      rw [← hsimplex.2.2, Fin.sum_univ_castSucc]
    have hroom : (∑ i, scaledNaturalCubeAnchor rho anchor i) <
        1 - delta / 2 := by
      have hlastLower := hsimplex.1 (Fin.last (ell + pattern.1.1))
      linarith
    refine Or.inr ⟨j, anchor, hslab, hmargin, hroom, ?_, ?_⟩
    · let sourcePositions := sectionSixDirectLocalSourcePositions pattern
      let zFull : Fin ((ell + pattern.1.1) + 1) -> Real :=
        fun q => normalizedPrimeLog (10 ^ length) (factors q)
      let z : Fin (ell + pattern.1.1) -> Real :=
        fun i => zFull i.castSucc
      have hzBox : z ∈ projectedLogBox
          (scaledNaturalCubeAnchor rho anchor) rho := by
        simpa only [z, zFull, Fin.init_def] using hcellData.2.1
      have hsourceSum : (∑ q ∈ sourcePositions, zFull q) =
          ∑ i : Fin ell, normalizedPrimeLog (10 ^ length)
            (factors (pattern.canonicalDisplayedEmbedding i.succ)) := by
        simpa only [sourcePositions, zFull] using
          sum_sectionSixDirectLocalSourcePositions pattern
            (fun q => normalizedPrimeLog (10 ^ length) (factors q))
      have hsumZEq : (∑ q, zFull q) =
          normalizedPrimeLog (10 ^ length) candidate.value := by
        dsimp only [zFull]
        rw [sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
          (fun q => (hprime q).ne_zero), hproduct]
      have hnearBounds := normalizedPrimeLog_near_bounds hX
        (mem_typeIINearXCarrier.mp hnear).2 hvalueUpper
      have hbandBounds :=
        (mem_sectionSixDirectDisplayedBandRegion.mp hdisplaySource).2.2.2.2
      by_cases hlastSource :
          Fin.last (ell + pattern.1.1) ∈ sourcePositions
      · let complementPositions :
            Finset (Fin ((ell + pattern.1.1) + 1)) :=
          Finset.univ \ sourcePositions
        let I := sectionSixDirectPrefixPositions complementPositions
        have hlastComplement :
            Fin.last (ell + pattern.1.1) ∉ complementPositions := by
          intro hmem
          exact (Finset.mem_sdiff.mp hmem).2 hlastSource
        have hprefixSum : (∑ i ∈ I, z i) =
            ∑ q ∈ complementPositions, zFull q := by
          simpa only [I, z] using
            sum_sectionSixDirectPrefixPositions_eq complementPositions zFull
              hlastComplement
        have hcomplementSum : (∑ q ∈ complementPositions, zFull q) =
            normalizedPrimeLog (10 ^ length) candidate.value -
              ∑ q ∈ sourcePositions, zFull q := by
          rw [show complementPositions = Finset.univ \ sourcePositions by rfl,
            Finset.sum_sdiff_eq_sub (Finset.subset_univ sourcePositions)]
          change (∑ q, zFull q) - (∑ q ∈ sourcePositions, zFull q) = _
          rw [hsumZEq]
        have hmove := sectionSixDirectPrefixSubsetSum_bounds hrho.le hzBox I
        rw [hprefixSum, hcomplementSum, hsourceSum] at hmove
        refine ⟨I, ?_⟩
        cases band with
        | first =>
            simp only [sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
            right
            constructor <;> nlinarith [sq_nonneg rho]
        | second =>
            simp only [sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
            left
            constructor <;> nlinarith [sq_nonneg rho]
      · let I := sectionSixDirectPrefixPositions sourcePositions
        have hprefixSum : (∑ i ∈ I, z i) =
            ∑ q ∈ sourcePositions, zFull q := by
          simpa only [I, z] using
            sum_sectionSixDirectPrefixPositions_eq sourcePositions zFull
              hlastSource
        have hmove := sectionSixDirectPrefixSubsetSum_bounds hrho.le hzBox I
        rw [hprefixSum, hsourceSum] at hmove
        refine ⟨I, ?_⟩
        cases band with
        | first =>
            simp only [sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
            left
            constructor <;> nlinarith [sq_nonneg rho]
        | second =>
            simp only [sectionSixThetaOne, sectionSixThetaTwo] at hbandBounds
            right
            constructor <;> nlinarith [sq_nonneg rho]
    · rw [Finset.mem_filter]
      exact ⟨mem_primeTupleProductSupport.mpr ⟨factors, hcell, hproduct⟩,
        hvalueC⟩

end

end PrimesRestrictedDigits
