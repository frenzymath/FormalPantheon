import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport

/-!
# Corrected Type II source-region support sandwich

On the strict near-`X` carrier, interior cell supports lie inside the original `log n` source
support, which lies inside the relevant `log X` cell union. This is the finite replacement for
the false existential-support identity in published Eq. (9.2).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A near product in an interior cell has its product-normalized logarithms
in the original source region. -/
theorem typeIIInteriorCubeSupport_inter_near_subset_original
    {X k : Nat} {eta delta : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (hX : 1 < X) (hdelta : 0 < delta)
    (hdeltaHalf : delta <= 1 / 2) :
    typeIICubeProductSupportUnion X delta eta
          (typeIIInteriorCubeAnchors delta region) ∩
        typeIINearXCarrier X delta ⊆
      typeIIOriginalRegionSupport X region ∩
        typeIINearXCarrier X delta := by
  intro n hn
  rcases Finset.mem_inter.mp hn with ⟨hnCell, hnNear⟩
  rcases mem_typeIICubeProductSupportUnion.mp hnCell with
    ⟨anchor, hanchor, hnSupport⟩
  rcases mem_primeTupleProductSupport.mp hnSupport with
    ⟨p, hpCell, hproduct⟩
  have hmembership := mem_majorArcPrimeTuples_iff.mp hpCell
  have hprime : forall i, (p i).Prime := fun i =>
    Nat.prime_of_mem_primesLE (hmembership.1 i)
  have hpLe (i : Fin (k + 1)) : p i <= n := by
    rw [← hproduct]
    exact primeTupleCoordinate_le_product (fun j => (hprime j).one_le) i
  let e : Fin (k + 1) -> Real := fun i => normalizedPrimeLog n (p i)
  have heCoordinates := normalizedPrimeLog_product_coordinates
    (one_lt_of_mem_typeIINearXCarrier hX hdelta hdeltaHalf hnNear)
    hprime hproduct
  have hePrefixCube : Fin.init e ∈
      typeIIDoubledProjectedCube delta anchor := by
    intro i
    have hcell : normalizedPrimeLog X (p i.castSucc) ∈
        Set.Ioc (scaledNaturalCubeAnchor delta anchor i)
          (scaledNaturalCubeAnchor delta anchor i + delta) := by
      simpa [majorArcLogRegion, projectedLogBox, Fin.init_def] using
        hmembership.2.1 i
    simpa only [e, Fin.init_def] using
      normalizedPrimeLog_mem_doubled_Ioc_of_near hX hdelta hdeltaHalf
        hnNear (hprime i.castSucc) (hpLe i.castSucc) hcell
  have heProjected : Fin.init e ∈ typeIIProjectedRegion region :=
    (mem_typeIIInteriorCubeAnchors.mp hanchor).2 hePrefixCube
  have heRegion : e ∈ region := by
    have hcomplete := completeProjectedLogTuple_init_eq_of_sum_eq_one
      heCoordinates.1
    change completeProjectedLogTuple (Fin.init e) ∈ region at heProjected
    rw [hcomplete] at heProjected
    exact heProjected
  refine Finset.mem_inter.mpr ⟨mem_typeIIOriginalRegionSupport.mpr
    ⟨(mem_typeIINearXCarrier.mp hnNear).1, ?_⟩, hnNear⟩
  exact ⟨p, hprime, hproduct, heRegion⟩

/-- An original source-region near product is supported in the unique
relevant grid cell assigned to its `log X` prefix. -/
theorem typeIIOriginal_inter_near_subset_relevantCubeSupport
    {X k : Nat} {eta delta : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (hX : 1 < X) (heta : 0 < eta)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= 1 / 2)
    (hregion : IsTypeIISourceRegion eta region) :
    typeIIOriginalRegionSupport X region ∩
        typeIINearXCarrier X delta ⊆
      typeIICubeProductSupportUnion X delta eta
          (typeIIRelevantCubeAnchors delta region) ∩
        typeIINearXCarrier X delta := by
  intro n hn
  rcases Finset.mem_inter.mp hn with ⟨hnOriginal, hnNear⟩
  rcases mem_typeIIOriginalRegionSupport.mp hnOriginal with
    ⟨hnX, p, hprime, hproduct, hpRegion⟩
  let e : Fin (k + 1) -> Real := fun i => normalizedPrimeLog n (p i)
  let z : Fin k -> Real := fun i => normalizedPrimeLog X (p i.castSucc)
  have hnOne : 1 < n :=
    one_lt_of_mem_typeIINearXCarrier hX hdelta hdeltaHalf hnNear
  have heCoordinates := normalizedPrimeLog_product_coordinates
    hnOne hprime hproduct
  have heSource := hregion hpRegion
  have hpLe (i : Fin (k + 1)) : p i <= n := by
    rw [← hproduct]
    exact primeTupleCoordinate_le_product (fun j => (hprime j).one_le) i
  have hzPositive : forall i, 0 < z i := by
    intro i
    unfold z normalizedPrimeLog
    exact div_pos (Real.log_pos (by exact_mod_cast (hprime i.castSucc).one_lt))
      (Real.log_pos (by exact_mod_cast hX))
  have hsumZ : (∑ i, normalizedPrimeLog X (p i)) < 1 :=
    sum_normalizedPrimeLog_lt_one_of_product_lt hX hprime (by
      rw [hproduct]
      exact hnX)
  have hzOne : forall i, z i <= 1 := by
    intro i
    have hnonneg : forall j, 0 <= normalizedPrimeLog X (p j) := fun j => by
      unfold normalizedPrimeLog
      exact div_nonneg (Real.log_natCast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast hX.le))
    have hsingle : normalizedPrimeLog X (p i.castSucc) <=
        ∑ j, normalizedPrimeLog X (p j) :=
      Finset.single_le_sum (fun j hj => hnonneg j)
        (Finset.mem_univ i.castSucc)
    exact hsingle.trans hsumZ.le
  obtain ⟨anchor, ⟨hanchorGrid, hzCell⟩, _hanchorUnique⟩ :=
    existsUnique_typeIINaturalCubeGrid_anchor hdelta hzPositive hzOne
  have hePrefixCube : Fin.init e ∈
      typeIIDoubledProjectedCube delta anchor := by
    intro i
    have hcell : normalizedPrimeLog X (p i.castSucc) ∈
        Set.Ioc (scaledNaturalCubeAnchor delta anchor i)
          (scaledNaturalCubeAnchor delta anchor i + delta) := by
      simpa only [z] using hzCell i
    simpa only [e, Fin.init_def] using
      normalizedPrimeLog_mem_doubled_Ioc_of_near hX hdelta hdeltaHalf
        hnNear (hprime i.castSucc) (hpLe i.castSucc) hcell
  have heProjected : Fin.init e ∈ typeIIProjectedRegion region := by
    change completeProjectedLogTuple (Fin.init e) ∈ region
    have hcomplete := completeProjectedLogTuple_init_eq_of_sum_eq_one
      heCoordinates.1
    simpa only [hcomplete, e] using hpRegion
  have hanchorRelevant :
      anchor ∈ typeIIRelevantCubeAnchors delta region :=
    mem_typeIIRelevantCubeAnchors.mpr
      ⟨hanchorGrid, ⟨Fin.init e, hePrefixCube, heProjected⟩⟩
  have hratio := normalizedPrimeLog_near_bounds hX
    (mem_typeIINearXCarrier.mp hnNear).2 hnX
  have hsumPrefixUpper : (∑ i, z i) <=
      (∑ i, scaledNaturalCubeAnchor delta anchor i) + (k : Real) * delta := by
    calc
      (∑ i, z i) <=
          ∑ i, (scaledNaturalCubeAnchor delta anchor i + delta) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hzCell i).2
      _ = (∑ i, scaledNaturalCubeAnchor delta anchor i) +
          (k : Real) * delta := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have hsumZEq : (∑ i, normalizedPrimeLog X (p i)) =
      normalizedPrimeLog X n := by
    rw [sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
      (fun i => (hprime i).ne_zero), hproduct]
  have hlastDecomposition :
      (∑ i, z i) + normalizedPrimeLog X (p (Fin.last k)) =
        normalizedPrimeLog X n := by
    rw [← hsumZEq, Fin.sum_univ_castSucc]
  have hdeltaSq : delta ^ 2 <= delta := by
    nlinarith [sq_nonneg delta]
  have hlastGeometric :
      1 - (∑ i, scaledNaturalCubeAnchor delta anchor i) -
          ((k + 1 : Nat) : Real) * delta <=
        normalizedPrimeLog X (p (Fin.last k)) := by
    push_cast
    dsimp only [z] at hsumPrefixUpper hlastDecomposition
    linarith [hratio.1]
  have hratioThreeQuarters : (3 / 4 : Real) <=
      normalizedPrimeLog X n := by
    have : (3 / 4 : Real) <= 1 - delta ^ 2 := by
      nlinarith [sq_nonneg delta]
    exact this.trans hratio.1.le
  have hlastEta : eta / 4 <=
      normalizedPrimeLog X (p (Fin.last k)) := by
    have hbase := normalizedPrimeLog_base_change
      (p := p (Fin.last k)) hX hnOne
    have heLast : eta <= normalizedPrimeLog n (p (Fin.last k)) := by
      simpa only [e] using heSource.1 (Fin.last k)
    calc
      eta / 4 <= (3 / 4 : Real) * eta := by linarith
      _ <= normalizedPrimeLog X n * eta :=
        mul_le_mul_of_nonneg_right hratioThreeQuarters heta.le
      _ <= normalizedPrimeLog X n *
          normalizedPrimeLog n (p (Fin.last k)) :=
        mul_le_mul_of_nonneg_left heLast (by positivity)
      _ = normalizedPrimeLog X (p (Fin.last k)) := hbase.symm
  have hpCell : p ∈ majorArcPrimeTuples X
      (scaledNaturalCubeAnchor delta anchor) delta eta := by
    rw [mem_majorArcPrimeTuples_iff]
    refine ⟨?_, ?_⟩
    · intro i
      rw [Nat.mem_primesLE]
      exact ⟨(hpLe i).trans hnX.le, hprime i⟩
    · refine ⟨?_, hsumZ.le, max_le hlastEta hlastGeometric⟩
      simpa [projectedLogBox, Fin.init_def, z] using hzCell
  refine Finset.mem_inter.mpr ⟨mem_typeIICubeProductSupportUnion.mpr
    ⟨anchor, hanchorRelevant, ?_⟩, hnNear⟩
  exact mem_primeTupleProductSupport.mpr ⟨p, hpCell, hproduct⟩

/-- Interior existential product supports are pairwise disjoint. -/
theorem pairwiseDisjoint_typeIIInteriorCubeProductSupports
    (X k : Nat) {eta delta : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (hX : 1 < X) (hdelta : 0 < delta)
    (hregion : IsTypeIISourceRegion eta region) :
    (typeIIInteriorCubeAnchors delta region : Set (Fin k -> Nat)).PairwiseDisjoint
      (fun anchor => primeTupleProductSupport
        (majorArcPrimeTuples X
          (scaledNaturalCubeAnchor delta anchor) delta eta)) := by
  intro u hu v hv huv
  change Disjoint
    (primeTupleProductSupport
      (majorArcPrimeTuples X (scaledNaturalCubeAnchor delta u) delta eta))
    (primeTupleProductSupport
      (majorArcPrimeTuples X (scaledNaturalCubeAnchor delta v) delta eta))
  rw [Finset.disjoint_left]
  intro n hnu hnv
  rcases mem_primeTupleProductSupport.mp hnu with ⟨p, hp, hpProduct⟩
  rcases mem_primeTupleProductSupport.mp hnv with ⟨q, hq, hqProduct⟩
  have hsepU := typeIIInteriorCubeAnchor_separated hdelta hregion hu
  have hsepV := typeIIInteriorCubeAnchor_separated hdelta hregion hv
  have hpMono :=
    strictMono_of_mem_majorArcPrimeTuples_of_typeIIInteriorCellSeparated
      hX hsepU hp
  have hqMono :=
    strictMono_of_mem_majorArcPrimeTuples_of_typeIIInteriorCellSeparated
      hX hsepV hq
  have hpPrime : forall i, (p i).Prime := fun i =>
    Nat.prime_of_mem_primesLE ((mem_majorArcPrimeTuples_iff.mp hp).1 i)
  have hqPrime : forall i, (q i).Prime := fun i =>
    Nat.prime_of_mem_primesLE ((mem_majorArcPrimeTuples_iff.mp hq).1 i)
  have hpq : p = q := eq_of_strictMono_primeTupleProduct_eq
    hpPrime hqPrime hpMono hqMono (hpProduct.trans hqProduct.symm)
  subst q
  have hglobal :=
    pairwiseDisjoint_majorArcPrimeTuples_scaledNaturalCubeAnchor
      X k delta eta hdelta
  have hdisjoint := hglobal (Set.mem_univ u) (Set.mem_univ v) huv
  exact (Finset.disjoint_left.mp hdisjoint) hp hq

/-- Relevant cell support is exactly the union of interior and remainder
cell supports. -/
theorem typeIICubeProductSupportUnion_relevant_eq_interior_union_remainder
    (X : Nat) {k : Nat} (delta eta : Real)
    (region : Set (Fin (k + 1) -> Real)) :
    typeIICubeProductSupportUnion X delta eta
        (typeIIRelevantCubeAnchors delta region) =
      typeIICubeProductSupportUnion X delta eta
          (typeIIInteriorCubeAnchors delta region) ∪
        typeIICubeProductSupportUnion X delta eta
          (typeIIRemainderCubeAnchors delta region) := by
  rw [typeIIRelevantCubeAnchors_eq_interior_union_remainder]
  unfold typeIICubeProductSupportUnion
  rw [Finset.union_biUnion]

/-- The corrected near-`X` interior/original/remainder support sandwich. -/
theorem typeIIRegionSupport_near_sandwich
    {X k : Nat} {eta delta : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (hX : 1 < X) (heta : 0 < eta)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= 1 / 2)
    (hregion : IsTypeIISourceRegion eta region) :
    typeIICubeProductSupportUnion X delta eta
          (typeIIInteriorCubeAnchors delta region) ∩
        typeIINearXCarrier X delta ⊆
      typeIIOriginalRegionSupport X region ∩ typeIINearXCarrier X delta ∧
    typeIIOriginalRegionSupport X region ∩ typeIINearXCarrier X delta ⊆
      (typeIICubeProductSupportUnion X delta eta
          (typeIIInteriorCubeAnchors delta region) ∪
        typeIICubeProductSupportUnion X delta eta
          (typeIIRemainderCubeAnchors delta region)) ∩
        typeIINearXCarrier X delta := by
  refine ⟨typeIIInteriorCubeSupport_inter_near_subset_original
    hX hdelta hdeltaHalf, ?_⟩
  rw [← typeIICubeProductSupportUnion_relevant_eq_interior_union_remainder]
  exact typeIIOriginal_inter_near_subset_relevantCubeSupport
    hX heta hdelta hdeltaHalf hregion

end

end PrimesRestrictedDigits
