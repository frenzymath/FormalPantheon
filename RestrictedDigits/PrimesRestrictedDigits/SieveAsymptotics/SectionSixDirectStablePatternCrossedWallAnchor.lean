import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternCrossedWall
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineThickSlabCover
/-! # SectionSixDirectStablePatternCrossedWallAnchor -/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixDirectStableTargetFactors_exists_crossedWallAnchor
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {pattern : SectionSixDirectStablePattern ell M}
    {factors : Fin ((ell + pattern.1.1) + 1) -> Nat}
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= 1 / 2)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (hprime : ∀ i, (factors i).Prime)
    (hproduct : primeTupleProduct factors = N)
    (hlastLower : delta <= normalizedPrimeLog N
      (factors (Fin.last (ell + pattern.1.1))))
    (j : Fin (sectionSixDirectDisplayedBandPresentation
      sourcePresentation epsilon delta band).constraintCount)
    (hnormal :
      typeIIProjectedAffineNormal
          (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
            ((sectionSixDirectDisplayedBandPresentation
              sourcePresentation epsilon delta band).normal j)) ≠ 0)
    (hwall :
      |typeIIAffineValue
            (typeIIProjectedAffineNormal
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).normal j)))
            (Fin.init
              (fun i => normalizedPrimeLog N (factors i))) -
          typeIIProjectedAffineBound
            (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).normal j))
            ((sectionSixDirectDisplayedBandPresentation
              sourcePresentation epsilon delta band).bound j)| <=
        rho ^ 2 * typeIIAffineNormalMass
          ((sectionSixDirectDisplayedBandPresentation
            sourcePresentation epsilon delta band).normal j)) :
    ∃ anchor,
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
      factors ∈ majorArcPrimeTuples (10 ^ length)
        (scaledNaturalCubeAnchor rho anchor) rho delta := by
    let X : Nat := 10 ^ length
    let e : Fin ((ell + pattern.1.1) + 1) -> Real :=
      fun i => normalizedPrimeLog N (factors i)
    let z : Fin (ell + pattern.1.1) -> Real :=
      fun i => normalizedPrimeLog X (factors i.castSucc)
    have hX : 1 < X := by
      dsimp only [X]
      exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
    have hN : 1 < N :=
      one_lt_of_mem_typeIINearXCarrier hX hrho hrhoHalf (by
        simpa only [X] using hnear)
    have hNX : N < X := by
      simpa only [X] using (mem_typeIINearXCarrier.mp hnear).1
    have hpLe (i : Fin ((ell + pattern.1.1) + 1)) : factors i <= N := by
      rw [← hproduct]
      exact primeTupleCoordinate_le_product (fun q => (hprime q).one_le) i
    have hzPositive : ∀ i, 0 < z i := by
      intro i
      unfold z normalizedPrimeLog
      exact div_pos (Real.log_pos (by exact_mod_cast (hprime i.castSucc).one_lt))
        (Real.log_pos (by exact_mod_cast hX))
    have hsumZ : (∑ i, normalizedPrimeLog X (factors i)) < 1 :=
      sum_normalizedPrimeLog_lt_one_of_product_lt hX hprime (by
        rw [hproduct]
        exact hNX)
    have hzOne : ∀ i, z i <= 1 := by
      intro i
      have hnonneg : ∀ q, 0 <= normalizedPrimeLog X (factors q) := fun q => by
        unfold normalizedPrimeLog
        exact div_nonneg (Real.log_natCast_nonneg _)
          (Real.log_nonneg (by exact_mod_cast hX.le))
      have hsingle : normalizedPrimeLog X (factors i.castSucc) <=
          ∑ q, normalizedPrimeLog X (factors q) :=
        Finset.single_le_sum (fun q _ => hnonneg q) (Finset.mem_univ i.castSucc)
      exact hsingle.trans hsumZ.le
    obtain ⟨anchor, ⟨hgrid, hzCell⟩, _⟩ :=
      existsUnique_typeIINaturalCubeGrid_anchor hrho hzPositive hzOne
    have hePrefixCube : Fin.init e ∈ typeIIDoubledProjectedCube rho anchor := by
      intro i
      have hcell : normalizedPrimeLog X (factors i.castSucc) ∈
          Set.Ioc (scaledNaturalCubeAnchor rho anchor i)
            (scaledNaturalCubeAnchor rho anchor i + rho) := by
        simpa only [z] using hzCell i
      simpa only [e, Fin.init_def, X] using
        normalizedPrimeLog_mem_doubled_Ioc_of_near hX hrho hrhoHalf
          (by simpa only [X] using hnear) (hprime i.castSucc)
          (hpLe i.castSucc) hcell
    have hslab : anchor ∈ typeIIAffineThickSlabAnchors rho
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
            sourcePresentation epsilon delta band).bound j)) := by
      rw [mem_typeIIAffineThickSlabAnchors]
      refine ⟨hgrid, hnormal, ?_⟩
      have hdistance :=
        abs_typeIIAffineValue_scaled_sub_le_of_mem_doubledProjectedCube
          hrho.le
          (normal := typeIIProjectedAffineNormal
            (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).normal j)))
          hePrefixCube
      calc
        |typeIIAffineValue
              (typeIIProjectedAffineNormal
                (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                  ((sectionSixDirectDisplayedBandPresentation
                    sourcePresentation epsilon delta band).normal j)))
              (scaledNaturalCubeAnchor rho anchor) -
            typeIIProjectedAffineBound
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).normal j))
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).bound j)| <=
            |typeIIAffineValue
                (typeIIProjectedAffineNormal
                  (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                    ((sectionSixDirectDisplayedBandPresentation
                      sourcePresentation epsilon delta band).normal j)))
                (scaledNaturalCubeAnchor rho anchor) -
              typeIIAffineValue
                (typeIIProjectedAffineNormal
                  (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                    ((sectionSixDirectDisplayedBandPresentation
                      sourcePresentation epsilon delta band).normal j)))
                (Fin.init e)| +
            |typeIIAffineValue
                (typeIIProjectedAffineNormal
                  (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                    ((sectionSixDirectDisplayedBandPresentation
                      sourcePresentation epsilon delta band).normal j)))
                (Fin.init e) -
              typeIIProjectedAffineBound
                (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                  ((sectionSixDirectDisplayedBandPresentation
                    sourcePresentation epsilon delta band).normal j))
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).bound j)| :=
          abs_sub_le _ _ _
        _ <= 2 * rho * typeIIAffineNormalMass
              (typeIIProjectedAffineNormal
                (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                  ((sectionSixDirectDisplayedBandPresentation
                    sourcePresentation epsilon delta band).normal j))) +
            rho ^ 2 * typeIIAffineNormalMass
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).normal j) := by
          apply add_le_add hdistance
          simpa only [e] using hwall
        _ = rho ^ 2 * typeIIAffineNormalMass
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).normal j) +
            2 * rho * typeIIAffineNormalMass
              (typeIIProjectedAffineNormal
                (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                  ((sectionSixDirectDisplayedBandPresentation
                    sourcePresentation epsilon delta band).normal j))) := by
          ring
    have hratio := normalizedPrimeLog_near_bounds hX
      (by simpa only [X] using (mem_typeIINearXCarrier.mp hnear).2) hNX
    have hsumPrefixUpper : (∑ i, z i) <=
        (∑ i, scaledNaturalCubeAnchor rho anchor i) +
          ((ell + pattern.1.1 : Nat) : Real) * rho := by
      calc
        (∑ i, z i) <=
            ∑ i, (scaledNaturalCubeAnchor rho anchor i + rho) := by
          apply Finset.sum_le_sum
          intro i _
          exact (hzCell i).2
        _ = (∑ i, scaledNaturalCubeAnchor rho anchor i) +
            ((ell + pattern.1.1 : Nat) : Real) * rho := by
          simp [Finset.sum_add_distrib, nsmul_eq_mul]
    have hsumZEq : (∑ i, normalizedPrimeLog X (factors i)) =
        normalizedPrimeLog X N := by
      rw [sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
        (fun i => (hprime i).ne_zero), hproduct]
    have hlastDecomposition :
        (∑ i, z i) + normalizedPrimeLog X
            (factors (Fin.last (ell + pattern.1.1))) =
          normalizedPrimeLog X N := by
      rw [← hsumZEq, Fin.sum_univ_castSucc]
    have hrhoSq : rho ^ 2 <= rho := by
      nlinarith [sq_nonneg rho]
    have hlastGeometric :
        1 - (∑ i, scaledNaturalCubeAnchor rho anchor i) -
            ((((ell + pattern.1.1) + 1 : Nat) : Real) * rho) <=
          normalizedPrimeLog X (factors (Fin.last (ell + pattern.1.1))) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      norm_num [Nat.cast_add] at hsumPrefixUpper
      dsimp only [z] at hsumPrefixUpper hlastDecomposition
      linarith [hratio.1]
    have hratioThreeQuarters : (3 / 4 : Real) <= normalizedPrimeLog X N := by
      have : (3 / 4 : Real) <= 1 - rho ^ 2 := by
        nlinarith [sq_nonneg rho]
      exact this.trans hratio.1.le
    have hlastEta : delta / 4 <=
        normalizedPrimeLog X (factors (Fin.last (ell + pattern.1.1))) := by
      have hbase := normalizedPrimeLog_base_change
        (p := factors (Fin.last (ell + pattern.1.1))) hX hN
      have heLast : delta <=
          normalizedPrimeLog N (factors (Fin.last (ell + pattern.1.1))) := by
        exact hlastLower
      calc
        delta / 4 <= (3 / 4 : Real) * delta := by linarith
        _ <= normalizedPrimeLog X N * delta :=
          mul_le_mul_of_nonneg_right hratioThreeQuarters hdelta.le
        _ <= normalizedPrimeLog X N *
            normalizedPrimeLog N (factors (Fin.last (ell + pattern.1.1))) :=
          mul_le_mul_of_nonneg_left heLast (by positivity)
        _ = normalizedPrimeLog X
            (factors (Fin.last (ell + pattern.1.1))) := hbase.symm
    have hpCell : factors ∈ majorArcPrimeTuples X
        (scaledNaturalCubeAnchor rho anchor) rho delta := by
      rw [mem_majorArcPrimeTuples_iff]
      refine ⟨?_, ?_⟩
      · intro i
        rw [Nat.mem_primesLE]
        exact ⟨(hpLe i).trans hNX.le, hprime i⟩
      · refine ⟨?_, hsumZ.le, max_le hlastEta hlastGeometric⟩
        simpa [projectedLogBox, Fin.init_def, z] using hzCell
    exact ⟨anchor, hslab, by simpa only [X] using hpCell⟩

theorem sectionSixDirectStablePattern_exists_crossedWallAnchor
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {pattern : SectionSixDirectStablePattern ell M}
    {candidate : SectionSixDirectCandidate ell}
    {factors : Fin ((ell + pattern.1.1) + 1) -> Nat}
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= 1 / 2)
    (hnear : candidate.value ∈ typeIINearXCarrier (10 ^ length) rho)
    (hprime : ∀ i, (factors i).Prime)
    (hproduct : primeTupleProduct factors = candidate.value)
    (hlastLower : delta <= normalizedPrimeLog candidate.value
      (factors (Fin.last (ell + pattern.1.1))))
    (j : Fin (sectionSixDirectDisplayedBandPresentation
      sourcePresentation epsilon delta band).constraintCount)
    (hnormal :
      typeIIProjectedAffineNormal
          (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
            ((sectionSixDirectDisplayedBandPresentation
              sourcePresentation epsilon delta band).normal j)) ≠ 0)
    (hwall :
      |typeIIAffineValue
            (typeIIProjectedAffineNormal
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).normal j)))
            (Fin.init
              (fun i => normalizedPrimeLog candidate.value (factors i))) -
          typeIIProjectedAffineBound
            (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).normal j))
            ((sectionSixDirectDisplayedBandPresentation
              sourcePresentation epsilon delta band).bound j)| <=
        rho ^ 2 * typeIIAffineNormalMass
          ((sectionSixDirectDisplayedBandPresentation
            sourcePresentation epsilon delta band).normal j)) :
    ∃ anchor,
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
      factors ∈ majorArcPrimeTuples (10 ^ length)
        (scaledNaturalCubeAnchor rho anchor) rho delta := by
  exact sectionSixDirectStableTargetFactors_exists_crossedWallAnchor
    hlength hdelta hrho hrhoHalf hnear hprime hproduct hlastLower j hnormal hwall

end

end PrimesRestrictedDigits
