import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallPairBaseBridge

/-!
# High central-small triple base bridge

This file reindexes the triple base sum by the Proposition 6.1 role order `![r, q, p]`. The
inherited pair data is reconstructed through the public pair carrier equality; the triple
presentation adds only the strict lower wall for `r`.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137--138, and the `S3` decomposition,
pp. 145--146, especially Eq. (6.16).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The recurrence-native triple roles in increasing Proposition 6.1 order. -/
def sectionSixFirstHighCentralSmallTripleTupleEquiv :
    SectionSixFirstHighCentralSmallTripleIndex ≃ (Fin 3 -> Nat) where
  toFun index := ![index.2, index.1.2, index.1.1]
  invFun tuple := ⟨⟨tuple 2, tuple 1⟩, tuple 0⟩
  left_inv index := by
    rcases index with ⟨⟨p, q⟩, r⟩
    rfl
  right_inv tuple := by
    funext i
    fin_cases i <;> rfl

private abbrev sectionSixFirstHighCentralSmallTripleTuple
    (index : SectionSixFirstHighCentralSmallTripleIndex) : Fin 3 -> Nat :=
  sectionSixFirstHighCentralSmallTripleTupleEquiv index

private theorem sectionSixFirstHighCentralSmallPairTuple_product_eq
    (index : SectionSixFirstStrictIndex) :
    primeTupleProduct (sectionSixFirstHighCentralSmallPairTupleEquiv index) =
      sectionSixFirstPairProduct index := by
  simp [sectionSixFirstHighCentralSmallPairTupleEquiv,
    primeTupleProduct, Fin.prod_univ_two,
    sectionSixFirstPairProduct, Nat.mul_comm]

private theorem sectionSixFirstHighCentralSmallTripleTuple_product_eq
    (index : SectionSixFirstHighCentralSmallTripleIndex) :
    primeTupleProduct (sectionSixFirstHighCentralSmallTripleTuple index) =
      sectionSixFirstHighCentralSmallTripleProduct index := by
  simp [sectionSixFirstHighCentralSmallTripleTuple,
    sectionSixFirstHighCentralSmallTripleTupleEquiv,
    primeTupleProduct, Fin.prod_univ_succ,
    sectionSixFirstHighCentralSmallTripleProduct,
    sectionSixFirstPairProduct, Nat.mul_comm, Nat.mul_left_comm]

private theorem sectionSixFirstHighCentralSmallTriple_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstHighCentralSmallTripleIndex) :
    index ∈ sectionSixFirstHighCentralSmallTripleIndices epsilon length <->
      sectionSixFirstHighCentralSmallTripleTuple index ∈
        propositionSixOnePrimeTuples epsilon 3
          (sectionSixFirstHighCentralSmallTripleRegion epsilon) length := by
  classical
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1.1
  let q : Nat := index.1.2
  let r : Nat := index.2
  have hXNat : 1 < XNat := by
    simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  rw [mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength]
  constructor
  · intro hindex
    have htriple :=
      mem_sectionSixFirstHighCentralSmallTripleIndices.mp hindex
    have hpairMapped :
        sectionSixFirstHighCentralSmallPairTupleEquiv index.1 ∈
          (sectionSixFirstPairPieceIndices epsilon length
            .highCentralSmall).map
              sectionSixFirstHighCentralSmallPairTupleEquiv.toEmbedding :=
      Finset.mem_map.mpr ⟨index.1, htriple.1, rfl⟩
    have hpairTuple :
        sectionSixFirstHighCentralSmallPairTupleEquiv index.1 ∈
          propositionSixOnePrimeTuples epsilon 2
            (sectionSixFirstHighCentralSmallPairRegion epsilon) length := by
      rw [← sectionSixFirstHighCentralSmallPairIndices_map_eq_propositionSixOnePrimeTuples
        epsilon hepsilon hepsilonSmall hlength]
      exact hpairMapped
    have hpairSource :=
      (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).1
        hpairTuple
    dsimp [IsPropositionSixOnePrimeTuple] at hpairSource
    rcases hpairSource with
      ⟨hpairPrime, hpairMonotone, hpairLower, _hpairCap, hpairRegion⟩
    have hrData := mem_sievePrimeInterval.mp htriple.2
    have hrq : r <= q := by
      exact_mod_cast hrData.2.2
    have hqp : q <= p := by
      simpa [sectionSixFirstHighCentralSmallPairTupleEquiv, p, q] using
        hpairMonotone (show (0 : Fin 2) <= 1 by decide)
    have hrp : r <= p := hrq.trans hqp
    have hrLog :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat r := by
      change sectionSixThetaGap epsilon < Real.logb X (r : Real)
      apply (Real.lt_logb_iff_rpow_lt hX
        (by exact_mod_cast hrData.1.pos)).2
      simpa [sectionSixZOne, X, XNat, r] using hrData.2.1
    have hpairRegionData :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q ∧
          sectionSixThetaTwo epsilon < normalizedPrimeLog XNat p ∧
            normalizedPrimeLog XNat p <= (1 / 2 : Real) ∧
              normalizedPrimeLog XNat p +
                  2 * normalizedPrimeLog XNat q <
                1 - sectionSixThetaOne epsilon := by
      simpa [sectionSixFirstHighCentralSmallPairRegion,
        sectionSixFirstHighCentralSmallPairTupleEquiv, XNat, p, q] using
          hpairRegion
    have hproductCap :
        (primeTupleProduct
            (sectionSixFirstHighCentralSmallTripleTuple index) : Real) <=
          X ^ (1 - sectionSixThetaOne epsilon) := by
      rw [sectionSixFirstHighCentralSmallTripleTuple_product_eq]
      have hcap := sectionSixFirstHighCentralSmall_tripleProduct_lt_zSix
        hepsilon hepsilonSmall hlength hindex
      simpa [sectionSixZSix, X, XNat] using hcap.le
    dsimp [IsPropositionSixOnePrimeTuple]
    refine ⟨?_, ?_, ?_, hproductCap, ?_⟩
    · intro i
      fin_cases i
      · simpa [sectionSixFirstHighCentralSmallTripleTuple,
          sectionSixFirstHighCentralSmallTripleTupleEquiv, r] using hrData.1
      · simpa [sectionSixFirstHighCentralSmallTripleTuple,
          sectionSixFirstHighCentralSmallTripleTupleEquiv,
          sectionSixFirstHighCentralSmallPairTupleEquiv, q] using
            hpairPrime (0 : Fin 2)
      · simpa [sectionSixFirstHighCentralSmallTripleTuple,
          sectionSixFirstHighCentralSmallTripleTupleEquiv,
          sectionSixFirstHighCentralSmallPairTupleEquiv, p] using
            hpairPrime (1 : Fin 2)
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [sectionSixFirstHighCentralSmallTripleTuple,
          sectionSixFirstHighCentralSmallTripleTupleEquiv, p, q, r]
    · intro i
      fin_cases i
      · simpa [sectionSixFirstHighCentralSmallTripleTuple,
          sectionSixFirstHighCentralSmallTripleTupleEquiv,
          sectionSixZOne, X, XNat, r] using hrData.2.1.le
      · simpa [sectionSixFirstHighCentralSmallTripleTuple,
          sectionSixFirstHighCentralSmallTripleTupleEquiv,
          sectionSixFirstHighCentralSmallPairTupleEquiv, q] using
            hpairLower (0 : Fin 2)
      · simpa [sectionSixFirstHighCentralSmallTripleTuple,
          sectionSixFirstHighCentralSmallTripleTupleEquiv,
          sectionSixFirstHighCentralSmallPairTupleEquiv, p] using
            hpairLower (1 : Fin 2)
    · simpa [sectionSixFirstHighCentralSmallTripleRegion,
        sectionSixFirstHighCentralSmallTripleTuple,
        sectionSixFirstHighCentralSmallTripleTupleEquiv, XNat, p, q, r] using
          And.intro hrLog hpairRegionData.2
  · intro htuple
    dsimp [IsPropositionSixOnePrimeTuple] at htuple
    rcases htuple with
      ⟨hprime, hmonotone, hlower, hproductCap, hregion⟩
    have hpPrime : p.Prime := by
      simpa [sectionSixFirstHighCentralSmallTripleTuple,
        sectionSixFirstHighCentralSmallTripleTupleEquiv, p] using
          hprime (2 : Fin 3)
    have hqPrime : q.Prime := by
      simpa [sectionSixFirstHighCentralSmallTripleTuple,
        sectionSixFirstHighCentralSmallTripleTupleEquiv, q] using
          hprime (1 : Fin 3)
    have hrPrime : r.Prime := by
      simpa [sectionSixFirstHighCentralSmallTripleTuple,
        sectionSixFirstHighCentralSmallTripleTupleEquiv, r] using
          hprime (0 : Fin 3)
    have hqPos : (0 : Real) < q := by exact_mod_cast hqPrime.pos
    have hrPos : (0 : Real) < r := by exact_mod_cast hrPrime.pos
    have hrq : r <= q := by
      simpa [sectionSixFirstHighCentralSmallTripleTuple,
        sectionSixFirstHighCentralSmallTripleTupleEquiv, q, r] using
          hmonotone (show (0 : Fin 3) <= 1 by decide)
    have hqp : q <= p := by
      simpa [sectionSixFirstHighCentralSmallTripleTuple,
        sectionSixFirstHighCentralSmallTripleTupleEquiv, p, q] using
          hmonotone (show (1 : Fin 3) <= 2 by decide)
    have hregionData :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat r ∧
          sectionSixThetaTwo epsilon < normalizedPrimeLog XNat p ∧
            normalizedPrimeLog XNat p <= (1 / 2 : Real) ∧
              normalizedPrimeLog XNat p +
                  2 * normalizedPrimeLog XNat q <
                1 - sectionSixThetaOne epsilon := by
      simpa [sectionSixFirstHighCentralSmallTripleRegion,
        sectionSixFirstHighCentralSmallTripleTuple,
        sectionSixFirstHighCentralSmallTripleTupleEquiv, XNat, p, q, r] using
          hregion
    have hrLower : X ^ sectionSixThetaGap epsilon < (r : Real) := by
      have hrLog := hregionData.1
      change sectionSixThetaGap epsilon < Real.logb X (r : Real) at hrLog
      exact (Real.lt_logb_iff_rpow_lt hX hrPos).1 hrLog
    have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) :=
      hrLower.trans_le (by exact_mod_cast hrq)
    have hqLog :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q := by
      change sectionSixThetaGap epsilon < Real.logb X (q : Real)
      exact (Real.lt_logb_iff_rpow_lt hX hqPos).2 hqLower
    have hpairProductLe :
        primeTupleProduct
            (sectionSixFirstHighCentralSmallPairTupleEquiv index.1) <=
          primeTupleProduct
            (sectionSixFirstHighCentralSmallTripleTuple index) := by
      rw [sectionSixFirstHighCentralSmallPairTuple_product_eq,
        sectionSixFirstHighCentralSmallTripleTuple_product_eq]
      unfold sectionSixFirstHighCentralSmallTripleProduct
      calc
        sectionSixFirstPairProduct index.1 =
            sectionSixFirstPairProduct index.1 * 1 := by simp
        _ <= sectionSixFirstPairProduct index.1 * r :=
          Nat.mul_le_mul_left _ hrPrime.one_le
        _ = sectionSixFirstPairProduct index.1 * index.2 := by rfl
    have hpairProductCap :
        (primeTupleProduct
            (sectionSixFirstHighCentralSmallPairTupleEquiv index.1) : Real) <=
          X ^ (1 - sectionSixThetaOne epsilon) := by
      have hpairProductLeReal :
          (primeTupleProduct
              (sectionSixFirstHighCentralSmallPairTupleEquiv index.1) : Real) <=
            (primeTupleProduct
              (sectionSixFirstHighCentralSmallTripleTuple index) : Real) := by
        exact_mod_cast hpairProductLe
      exact hpairProductLeReal.trans hproductCap
    have hpairRegion :
        (fun i => normalizedPrimeLog XNat
            (sectionSixFirstHighCentralSmallPairTupleEquiv index.1 i)) ∈
          sectionSixFirstHighCentralSmallPairRegion epsilon := by
      simpa [sectionSixFirstHighCentralSmallPairRegion,
        sectionSixFirstHighCentralSmallPairTupleEquiv, XNat, p, q] using
          And.intro hqLog hregionData.2
    have hpairSource :
        IsPropositionSixOnePrimeTuple epsilon length
          (sectionSixFirstHighCentralSmallPairRegion epsilon)
          (sectionSixFirstHighCentralSmallPairTupleEquiv index.1) := by
      dsimp [IsPropositionSixOnePrimeTuple]
      refine ⟨?_, ?_, ?_, hpairProductCap, hpairRegion⟩
      · intro i
        fin_cases i
        · simpa [sectionSixFirstHighCentralSmallPairTupleEquiv, q] using hqPrime
        · simpa [sectionSixFirstHighCentralSmallPairTupleEquiv, p] using hpPrime
      · intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [sectionSixFirstHighCentralSmallPairTupleEquiv, p, q]
      · intro i
        fin_cases i
        · simpa [sectionSixFirstHighCentralSmallPairTupleEquiv,
            sectionSixFirstHighCentralSmallTripleTuple,
            sectionSixFirstHighCentralSmallTripleTupleEquiv, q] using
              hlower (1 : Fin 3)
        · simpa [sectionSixFirstHighCentralSmallPairTupleEquiv,
            sectionSixFirstHighCentralSmallTripleTuple,
            sectionSixFirstHighCentralSmallTripleTupleEquiv, p] using
              hlower (2 : Fin 3)
    have hpairTuple :
        sectionSixFirstHighCentralSmallPairTupleEquiv index.1 ∈
          propositionSixOnePrimeTuples epsilon 2
            (sectionSixFirstHighCentralSmallPairRegion epsilon) length :=
      (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).2
        hpairSource
    have hpairMapped :
        sectionSixFirstHighCentralSmallPairTupleEquiv index.1 ∈
          (sectionSixFirstPairPieceIndices epsilon length
            .highCentralSmall).map
              sectionSixFirstHighCentralSmallPairTupleEquiv.toEmbedding := by
      rw [sectionSixFirstHighCentralSmallPairIndices_map_eq_propositionSixOnePrimeTuples
        epsilon hepsilon hepsilonSmall hlength]
      exact hpairTuple
    have hpair :
        index.1 ∈ sectionSixFirstPairPieceIndices epsilon length
          .highCentralSmall := by
      simpa using hpairMapped
    apply mem_sectionSixFirstHighCentralSmallTripleIndices.mpr
    refine ⟨hpair, mem_sievePrimeInterval.mpr ⟨hrPrime, ?_, ?_⟩⟩
    · simpa [sectionSixZOne, X, XNat, r] using hrLower
    · exact_mod_cast hrq

/-- The triple source carrier is exactly the mapped Proposition 6.1 carrier. -/
theorem sectionSixFirstHighCentralSmallTripleIndices_map_eq_propositionSixOnePrimeTuples
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstHighCentralSmallTripleIndices epsilon length).map
        sectionSixFirstHighCentralSmallTripleTupleEquiv.toEmbedding =
      propositionSixOnePrimeTuples epsilon 3
        (sectionSixFirstHighCentralSmallTripleRegion epsilon) length := by
  classical
  ext tuple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstHighCentralSmallTriple_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro htuple
    let index : SectionSixFirstHighCentralSmallTripleIndex :=
      sectionSixFirstHighCentralSmallTripleTupleEquiv.symm tuple
    have hinverse : sectionSixFirstHighCentralSmallTripleTupleEquiv index =
        tuple :=
      sectionSixFirstHighCentralSmallTripleTupleEquiv.apply_symm_apply tuple
    refine ⟨index, (sectionSixFirstHighCentralSmallTriple_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    simpa only [sectionSixFirstHighCentralSmallTripleTuple, hinverse] using
      htuple

private theorem sectionSixFirstHighCentralSmallTripleModulus_eq_tupleModulus
    (index : SectionSixFirstHighCentralSmallTripleIndex)
    (hp : index.1.1.Prime) (hq : index.1.2.Prime) (hr : index.2.Prime) :
    sectionSixFirstHighCentralSmallTripleModulus index =
      (primeTupleProduct
        (sectionSixFirstHighCentralSmallTripleTuple index)).toPNat' := by
  rw [sectionSixFirstHighCentralSmallTripleTuple_product_eq]
  apply PNat.eq
  rw [sectionSixFirstHighCentralSmallTripleModulus_coe hp hq hr,
    Nat.toPNat'_coe, if_pos]
  exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos

/-- The triple base sum is exactly its fixed Proposition 6.1 sum. -/
theorem sectionSixFirstHighCentralSmallTripleBaseSum_eq_propositionSixOneSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstHighCentralSmallTripleBaseSum epsilon digit length =
      propositionSixOneSum epsilon 3
        (sectionSixFirstHighCentralSmallTripleRegion epsilon) digit length := by
  classical
  unfold sectionSixFirstHighCentralSmallTripleBaseSum propositionSixOneSum
  dsimp only
  rw [← sectionSixFirstHighCentralSmallTripleIndices_map_eq_propositionSixOnePrimeTuples
    epsilon hepsilon hepsilonSmall hlength]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro index hindex
  have htuple := (sectionSixFirstHighCentralSmallTriple_mem_iff
    hepsilon hepsilonSmall hlength index).1 hindex
  have hsource :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).1 htuple
  have hp : index.1.1.Prime := by
    simpa [sectionSixFirstHighCentralSmallTripleTuple,
      sectionSixFirstHighCentralSmallTripleTupleEquiv] using
        hsource.1 (2 : Fin 3)
  have hq : index.1.2.Prime := by
    simpa [sectionSixFirstHighCentralSmallTripleTuple,
      sectionSixFirstHighCentralSmallTripleTupleEquiv] using
        hsource.1 (1 : Fin 3)
  have hr : index.2.Prime := by
    simpa [sectionSixFirstHighCentralSmallTripleTuple,
      sectionSixFirstHighCentralSmallTripleTupleEquiv] using
        hsource.1 (0 : Fin 3)
  rw [sectionSixFirstHighCentralSmallTripleModulus_eq_tupleModulus
    index hp hq hr]
  rfl

end

end PrimesRestrictedDigits
