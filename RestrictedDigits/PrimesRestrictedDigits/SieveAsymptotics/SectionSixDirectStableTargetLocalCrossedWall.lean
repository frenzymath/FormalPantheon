import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternCrossedWallAnchor

/-!
# Locally admissible crossed walls for direct stable targets

This is the target-oriented counterpart. It combines the exact two-epsilon target margin with
aggregate near-base normalization, so the normalization loss is one `rho^2` rather than one
loss per coordinate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixDirectOneWidthSubsetSum_bounds
    {k : Nat} {rho : Real} {anchor : Fin k -> Nat}
    {z : Fin k -> Real} (hrho : 0 <= rho)
    (hz : z ∈ projectedLogBox (scaledNaturalCubeAnchor rho anchor) rho)
    (I : Finset (Fin k)) :
    (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) <=
        ∑ i ∈ I, z i ∧
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
        · simpa using Finset.card_le_univ I

private theorem sum_typeIIPrefixIndexSet_eq
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

/-- An explicit near target tuple on one projected wall belongs to the same
locally admissible wall-cell family used by the forward direct cover. -/
theorem
    sectionSixDirectStableTargetFactors_exists_locallyAdmissibleCrossedWallAnchor
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {C : Finset Nat}
    {pattern : SectionSixDirectStablePattern ell M}
    {factors : Fin ((ell + pattern.1.1) + 1) -> Nat}
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 : Nat) : Real) * rho) <= epsilon)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (hprime : ∀ i, (factors i).Prime)
    (hproduct : primeTupleProduct factors = N)
    (htarget :
      (fun i => normalizedPrimeLog N (factors i)) ∈
        sectionSixDirectStableTargetRegion
          epsilon delta region band pattern)
    (hNC : N ∈ C)
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
            (Fin.init (fun i => normalizedPrimeLog N (factors i))) -
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
      (∀ i, delta / 2 <= scaledNaturalCubeAnchor rho anchor i) ∧
      (∑ i, scaledNaturalCubeAnchor rho anchor i) < 1 - delta / 2 ∧
      (∃ I : Finset (Fin (ell + pattern.1.1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon)) ∧
      N ∈
        (primeTupleProductSupport
          (majorArcPrimeTuples (10 ^ length)
            (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
          (fun n => n ∈ C) := by
  let X : Nat := 10 ^ length
  let eN : Fin ((ell + pattern.1.1) + 1) -> Real :=
    fun i => normalizedPrimeLog N (factors i)
  let eX : Fin ((ell + pattern.1.1) + 1) -> Real :=
    fun i => normalizedPrimeLog X (factors i)
  have hX : 1 < X := by
    dsimp only [X]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hN : 1 < N :=
    one_lt_of_mem_typeIINearXCarrier hX hrho hrhoHalf (by
      simpa only [X] using hnear)
  have hNX : N < X := by
    simpa only [X] using (mem_typeIINearXCarrier.mp hnear).1
  have hsimplex := (mem_sectionSixDirectStableTargetRegion.mp htarget).1
  obtain ⟨anchor, hslab, hcell⟩ :=
    sectionSixDirectStableTargetFactors_exists_crossedWallAnchor
      (sourcePresentation := sourcePresentation) hlength hdelta hrho hrhoHalf
        hnear hprime hproduct (hsimplex.1 (Fin.last (ell + pattern.1.1)))
        j hnormal hwall
  have hpLe (i : Fin ((ell + pattern.1.1) + 1)) : factors i <= N := by
    rw [← hproduct]
    exact primeTupleCoordinate_le_product (fun q => (hprime q).one_le) i
  have hcellData := mem_majorArcPrimeTuples_iff.mp hcell
  have hzCell : (fun i : Fin (ell + pattern.1.1) => eX i.castSucc) ∈
      projectedLogBox (scaledNaturalCubeAnchor rho anchor) rho := by
    simpa only [eX, X, Fin.init_def] using hcellData.2.1
  have heCell : ∀ i : Fin (ell + pattern.1.1),
      eN i.castSucc ∈ Set.Ioc (scaledNaturalCubeAnchor rho anchor i)
        (scaledNaturalCubeAnchor rho anchor i + 2 * rho) := by
    intro i
    exact normalizedPrimeLog_mem_doubled_Ioc_of_near hX hrho hrhoHalf
      (by simpa only [X] using hnear) (hprime i.castSucc) (hpLe i.castSucc)
      (by simpa only [eX, X] using hzCell i)
  have hmargin : ∀ i : Fin (ell + pattern.1.1),
      delta / 2 <= scaledNaturalCubeAnchor rho anchor i := by
    intro i
    have hiLower := hsimplex.1 i.castSucc
    have hiUpper := (heCell i).2
    dsimp only [eN] at hiUpper
    linarith
  have hanchorPrefix :
      (∑ i, scaledNaturalCubeAnchor rho anchor i) <=
        ∑ i : Fin (ell + pattern.1.1), eN i.castSucc := by
    exact Finset.sum_le_sum fun i _ => (heCell i).1.le
  have hsumDecomposition :
      (∑ i : Fin (ell + pattern.1.1), eN i.castSucc) +
          eN (Fin.last (ell + pattern.1.1)) = 1 := by
    simpa only [eN] using (Fin.sum_univ_castSucc (fun i =>
      normalizedPrimeLog N (factors i))).symm.trans hsimplex.2.2
  have hroom : (∑ i, scaledNaturalCubeAnchor rho anchor i) <
      1 - delta / 2 := by
    have hlastLower := hsimplex.1 (Fin.last (ell + pattern.1.1))
    dsimp only [eN] at hsumDecomposition
    linarith
  have htransport
      (positions : Finset (Fin ((ell + pattern.1.1) + 1)))
      (hlast : Fin.last (ell + pattern.1.1) ∉ positions)
      (lower upper : Real)
      (hlower : lower + 2 * epsilon <= ∑ q ∈ positions, eN q)
      (hupper : (∑ q ∈ positions, eN q) <= upper - 2 * epsilon) :
      ∃ I : Finset (Fin (ell + pattern.1.1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
          Set.Icc (lower + epsilon) (upper - epsilon) := by
    let I := typeIIPrefixIndexSet positions
    have hprefixN : (∑ i ∈ I, eN i.castSucc) = ∑ q ∈ positions, eN q := by
      simpa only [I] using sum_typeIIPrefixIndexSet_eq positions eN hlast
    have hprefixX : (∑ i ∈ I, eX i.castSucc) = ∑ q ∈ positions, eX q := by
      simpa only [I] using sum_typeIIPrefixIndexSet_eq positions eX hlast
    have hbase :=
      abs_sum_normalizedPrimeLog_sub_sum_normalizedPrimeLog_le_sq_of_near
        hX hN (by simpa only [X] using (mem_typeIINearXCarrier.mp hnear).2)
          hNX hprime hproduct positions
    have hbasePrefix :
        |(∑ i ∈ I, eN i.castSucc) - ∑ i ∈ I, eX i.castSucc| <=
          rho ^ 2 := by
      rw [hprefixN, hprefixX]
      simpa only [eN, eX, X] using hbase
    have hbaseBounds := abs_le.mp hbasePrefix
    have hmove := sectionSixDirectOneWidthSubsetSum_bounds hrho.le hzCell I
    have hkRhoNonnegative :
        0 <= ((ell + pattern.1.1 : Nat) : Real) * rho :=
      mul_nonneg (by positivity) hrho.le
    refine ⟨I, ?_, ?_⟩
    · linarith
    · linarith
  have hstrong := sectionSixDirectStableTargetRegion_convenient_two_mul
    (epsilon := epsilon) (delta := delta) region band pattern
  obtain ⟨positions, hpositions⟩ := hstrong
  have htargetBounds := hpositions eN (by simpa only [eN] using htarget)
  have hconvenient :
      ∃ I : Finset (Fin (ell + pattern.1.1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon) := by
    by_cases hlast : Fin.last (ell + pattern.1.1) ∈ positions
    · let complement : Finset (Fin ((ell + pattern.1.1) + 1)) :=
        Finset.univ \ positions
      have hlastComplement :
          Fin.last (ell + pattern.1.1) ∉ complement := by
        simp [complement, hlast]
      have hsumEN : (∑ q, eN q) = 1 := by
        simpa only [eN] using hsimplex.2.2
      have hsumComplement : (∑ q ∈ complement, eN q) =
          1 - ∑ q ∈ positions, eN q := by
        rw [show complement = Finset.univ \ positions by rfl,
          Finset.sum_sdiff_eq_sub (Finset.subset_univ positions)]
        change (∑ q, eN q) - (∑ q ∈ positions, eN q) = _
        rw [hsumEN]
      obtain ⟨I, hI⟩ := htransport complement hlastComplement
        (23 / 40) (16 / 25)
          (by rw [hsumComplement]; linarith [htargetBounds.2])
          (by rw [hsumComplement]; linarith [htargetBounds.1])
      exact ⟨I, Or.inr hI⟩
    · obtain ⟨I, hI⟩ := htransport positions hlast
        (9 / 25) (17 / 40) htargetBounds.1 htargetBounds.2
      exact ⟨I, Or.inl hI⟩
  refine ⟨anchor, hslab, hmargin, hroom, hconvenient, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨mem_primeTupleProductSupport.mpr ⟨factors, hcell, hproduct⟩, hNC⟩

end

end PrimesRestrictedDigits
