import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallPairBaseBridge

/-!
# Low central-small triple base bridge

This file reindexes the triple base sum by the Proposition 6.1 role order `![r, q, p]`. The
inherited pair data is reconstructed through the public pair carrier equality; the triple
presentation appends only the strict lower wall for `r`.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137--138, and Section 6, p. 143,
especially Eq. (6.12).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The recurrence-native triple roles in increasing Proposition 6.1 order. -/
def sectionSixFirstLowCentralSmallTripleTupleEquiv :
    SectionSixFirstLowCentralSmallTripleIndex ≃ (Fin 3 -> Nat) where
  toFun index := ![index.2, index.1.2, index.1.1]
  invFun tuple := ⟨⟨tuple 2, tuple 1⟩, tuple 0⟩
  left_inv index := by
    rcases index with ⟨⟨p, q⟩, r⟩
    rfl
  right_inv tuple := by
    funext i
    fin_cases i <;> rfl

private abbrev sectionSixFirstLowCentralSmallTripleTuple
    (index : SectionSixFirstLowCentralSmallTripleIndex) : Fin 3 -> Nat :=
  sectionSixFirstLowCentralSmallTripleTupleEquiv index

private theorem sectionSixFirstLowCentralSmallPairTuple_product_eq
    (index : SectionSixFirstStrictIndex) :
    primeTupleProduct (sectionSixFirstLowCentralSmallPairTupleEquiv index) =
      sectionSixFirstPairProduct index := by
  simp [sectionSixFirstLowCentralSmallPairTupleEquiv,
    primeTupleProduct, Fin.prod_univ_two,
    sectionSixFirstPairProduct, Nat.mul_comm]

private theorem sectionSixFirstLowCentralSmallTripleTuple_product_eq
    (index : SectionSixFirstLowCentralSmallTripleIndex) :
    primeTupleProduct (sectionSixFirstLowCentralSmallTripleTuple index) =
      sectionSixFirstLowCentralSmallTripleProduct index := by
  simp [sectionSixFirstLowCentralSmallTripleTuple,
    sectionSixFirstLowCentralSmallTripleTupleEquiv,
    primeTupleProduct, Fin.prod_univ_succ,
    sectionSixFirstLowCentralSmallTripleProduct,
    sectionSixFirstPairProduct, Nat.mul_comm, Nat.mul_left_comm]

private theorem sectionSixFirstLowCentralSmallTriple_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstLowCentralSmallTripleIndex) :
    index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length <->
      sectionSixFirstLowCentralSmallTripleTuple index ∈
        propositionSixOnePrimeTuples epsilon 3
          (sectionSixFirstLowCentralSmallTripleRegion epsilon) length := by
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
      mem_sectionSixFirstLowCentralSmallTripleIndices.mp hindex
    have hpairMapped :
        sectionSixFirstLowCentralSmallPairTupleEquiv index.1 ∈
          (sectionSixFirstPairPieceIndices epsilon length
            .lowCentralSmall).map
              sectionSixFirstLowCentralSmallPairTupleEquiv.toEmbedding :=
      Finset.mem_map.mpr ⟨index.1, htriple.1, rfl⟩
    have hpairTuple :
        sectionSixFirstLowCentralSmallPairTupleEquiv index.1 ∈
          propositionSixOnePrimeTuples epsilon 2
            (sectionSixFirstLowCentralSmallPairRegion epsilon) length := by
      rw [← sectionSixFirstLowCentralSmallPairIndices_map_eq_propositionSixOnePrimeTuples
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
      simpa [sectionSixFirstLowCentralSmallPairTupleEquiv, p, q] using
        hpairMonotone (show (0 : Fin 2) <= 1 by decide)
    have hrp : r <= p := hrq.trans hqp
    have hrLog :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat r := by
      change sectionSixThetaGap epsilon < Real.logb X (r : Real)
      apply (Real.lt_logb_iff_rpow_lt hX
        (by exact_mod_cast hrData.1.pos)).2
      simpa [sectionSixZOne, X, XNat, r] using hrData.2.1
    have hpairRegionData :
        normalizedPrimeLog XNat p <= sectionSixThetaOne epsilon ∧
          sectionSixThetaTwo epsilon <
              normalizedPrimeLog XNat p + normalizedPrimeLog XNat q ∧
            normalizedPrimeLog XNat p +
                2 * normalizedPrimeLog XNat q <
              1 - sectionSixThetaOne epsilon := by
      simpa [sectionSixFirstLowCentralSmallPairRegion,
        sectionSixFirstLowCentralSmallPairTupleEquiv, XNat, p, q] using
          hpairRegion
    have hpiece :
        index.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
          sectionSixZThree epsilon X <
              (sectionSixFirstPairProduct index.1 : Real) ∧
            (sectionSixFirstPairProduct index.1 : Real) <
                sectionSixZFive epsilon X ∧
              (sectionSixFirstPairSquareProduct index.1 : Real) <
                sectionSixZSix epsilon X := by
      have hmem := (Finset.mem_filter.mp htriple.1).2
      simpa [sectionSixFirstPairMem, X, XNat] using hmem
    have htripleProductLe :
        sectionSixFirstLowCentralSmallTripleProduct index <=
          sectionSixFirstPairSquareProduct index.1 := by
      simp only [sectionSixFirstLowCentralSmallTripleProduct,
        sectionSixFirstPairSquareProduct]
      exact Nat.mul_le_mul_left _ hrq
    have htripleProductLt :
        (sectionSixFirstLowCentralSmallTripleProduct index : Real) <
          sectionSixZSix epsilon X := by
      have hle :
          (sectionSixFirstLowCentralSmallTripleProduct index : Real) <=
            (sectionSixFirstPairSquareProduct index.1 : Real) := by
        exact_mod_cast htripleProductLe
      exact hle.trans_lt hpiece.2.2.2
    have hproductCap :
        (primeTupleProduct
            (sectionSixFirstLowCentralSmallTripleTuple index) : Real) <=
          X ^ (1 - sectionSixThetaOne epsilon) := by
      rw [sectionSixFirstLowCentralSmallTripleTuple_product_eq]
      simpa [sectionSixZSix, X, XNat] using htripleProductLt.le
    dsimp [IsPropositionSixOnePrimeTuple]
    refine ⟨?_, ?_, ?_, hproductCap, ?_⟩
    · intro i
      fin_cases i
      · simpa [sectionSixFirstLowCentralSmallTripleTuple,
          sectionSixFirstLowCentralSmallTripleTupleEquiv, r] using hrData.1
      · simpa [sectionSixFirstLowCentralSmallTripleTuple,
          sectionSixFirstLowCentralSmallTripleTupleEquiv,
          sectionSixFirstLowCentralSmallPairTupleEquiv, q] using
            hpairPrime (0 : Fin 2)
      · simpa [sectionSixFirstLowCentralSmallTripleTuple,
          sectionSixFirstLowCentralSmallTripleTupleEquiv,
          sectionSixFirstLowCentralSmallPairTupleEquiv, p] using
            hpairPrime (1 : Fin 2)
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [sectionSixFirstLowCentralSmallTripleTuple,
          sectionSixFirstLowCentralSmallTripleTupleEquiv, p, q, r]
    · intro i
      fin_cases i
      · simpa [sectionSixFirstLowCentralSmallTripleTuple,
          sectionSixFirstLowCentralSmallTripleTupleEquiv,
          sectionSixZOne, X, XNat, r] using hrData.2.1.le
      · simpa [sectionSixFirstLowCentralSmallTripleTuple,
          sectionSixFirstLowCentralSmallTripleTupleEquiv,
          sectionSixFirstLowCentralSmallPairTupleEquiv, q] using
            hpairLower (0 : Fin 2)
      · simpa [sectionSixFirstLowCentralSmallTripleTuple,
          sectionSixFirstLowCentralSmallTripleTupleEquiv,
          sectionSixFirstLowCentralSmallPairTupleEquiv, p] using
            hpairLower (1 : Fin 2)
    · simpa [sectionSixFirstLowCentralSmallTripleRegion,
        sectionSixFirstLowCentralSmallTripleTuple,
        sectionSixFirstLowCentralSmallTripleTupleEquiv, XNat, p, q, r] using
          And.intro hpairRegionData.1
            (And.intro hpairRegionData.2.1
              (And.intro hpairRegionData.2.2 hrLog))
  · intro htuple
    dsimp [IsPropositionSixOnePrimeTuple] at htuple
    rcases htuple with
      ⟨hprime, hmonotone, hlower, hproductCap, hregion⟩
    have hpPrime : p.Prime := by
      simpa [sectionSixFirstLowCentralSmallTripleTuple,
        sectionSixFirstLowCentralSmallTripleTupleEquiv, p] using
          hprime (2 : Fin 3)
    have hqPrime : q.Prime := by
      simpa [sectionSixFirstLowCentralSmallTripleTuple,
        sectionSixFirstLowCentralSmallTripleTupleEquiv, q] using
          hprime (1 : Fin 3)
    have hrPrime : r.Prime := by
      simpa [sectionSixFirstLowCentralSmallTripleTuple,
        sectionSixFirstLowCentralSmallTripleTupleEquiv, r] using
          hprime (0 : Fin 3)
    have hrPos : (0 : Real) < r := by exact_mod_cast hrPrime.pos
    have hrq : r <= q := by
      simpa [sectionSixFirstLowCentralSmallTripleTuple,
        sectionSixFirstLowCentralSmallTripleTupleEquiv, q, r] using
          hmonotone (show (0 : Fin 3) <= 1 by decide)
    have hqp : q <= p := by
      simpa [sectionSixFirstLowCentralSmallTripleTuple,
        sectionSixFirstLowCentralSmallTripleTupleEquiv, p, q] using
          hmonotone (show (1 : Fin 3) <= 2 by decide)
    have hregionData :
        normalizedPrimeLog XNat p <= sectionSixThetaOne epsilon ∧
          sectionSixThetaTwo epsilon <
              normalizedPrimeLog XNat p + normalizedPrimeLog XNat q ∧
            normalizedPrimeLog XNat p +
                2 * normalizedPrimeLog XNat q <
                1 - sectionSixThetaOne epsilon ∧
              sectionSixThetaGap epsilon < normalizedPrimeLog XNat r := by
      simpa [sectionSixFirstLowCentralSmallTripleRegion,
        sectionSixFirstLowCentralSmallTripleTuple,
        sectionSixFirstLowCentralSmallTripleTupleEquiv, XNat, p, q, r] using
          hregion
    have hrLower : X ^ sectionSixThetaGap epsilon < (r : Real) := by
      have hrLog := hregionData.2.2.2
      change sectionSixThetaGap epsilon < Real.logb X (r : Real) at hrLog
      exact (Real.lt_logb_iff_rpow_lt hX hrPos).1 hrLog
    have hpairProductLe :
        primeTupleProduct
            (sectionSixFirstLowCentralSmallPairTupleEquiv index.1) <=
          primeTupleProduct
            (sectionSixFirstLowCentralSmallTripleTuple index) := by
      rw [sectionSixFirstLowCentralSmallPairTuple_product_eq,
        sectionSixFirstLowCentralSmallTripleTuple_product_eq]
      unfold sectionSixFirstLowCentralSmallTripleProduct
      calc
        sectionSixFirstPairProduct index.1 =
            sectionSixFirstPairProduct index.1 * 1 := by simp
        _ <= sectionSixFirstPairProduct index.1 * r :=
          Nat.mul_le_mul_left _ hrPrime.one_le
        _ = sectionSixFirstPairProduct index.1 * index.2 := by rfl
    have hpairProductCap :
        (primeTupleProduct
            (sectionSixFirstLowCentralSmallPairTupleEquiv index.1) : Real) <=
          X ^ (1 - sectionSixThetaOne epsilon) := by
      have hpairProductLeReal :
          (primeTupleProduct
              (sectionSixFirstLowCentralSmallPairTupleEquiv index.1) : Real) <=
            (primeTupleProduct
              (sectionSixFirstLowCentralSmallTripleTuple index) : Real) := by
        exact_mod_cast hpairProductLe
      exact hpairProductLeReal.trans hproductCap
    have hpairRegion :
        (fun i => normalizedPrimeLog XNat
            (sectionSixFirstLowCentralSmallPairTupleEquiv index.1 i)) ∈
          sectionSixFirstLowCentralSmallPairRegion epsilon := by
      simpa [sectionSixFirstLowCentralSmallPairRegion,
        sectionSixFirstLowCentralSmallPairTupleEquiv, XNat, p, q] using
          And.intro hregionData.1
            (And.intro hregionData.2.1 hregionData.2.2.1)
    have hpairSource :
        IsPropositionSixOnePrimeTuple epsilon length
          (sectionSixFirstLowCentralSmallPairRegion epsilon)
          (sectionSixFirstLowCentralSmallPairTupleEquiv index.1) := by
      dsimp [IsPropositionSixOnePrimeTuple]
      refine ⟨?_, ?_, ?_, hpairProductCap, hpairRegion⟩
      · intro i
        fin_cases i
        · simpa [sectionSixFirstLowCentralSmallPairTupleEquiv, q] using hqPrime
        · simpa [sectionSixFirstLowCentralSmallPairTupleEquiv, p] using hpPrime
      · intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [sectionSixFirstLowCentralSmallPairTupleEquiv, p, q]
      · intro i
        fin_cases i
        · simpa [sectionSixFirstLowCentralSmallPairTupleEquiv,
            sectionSixFirstLowCentralSmallTripleTuple,
            sectionSixFirstLowCentralSmallTripleTupleEquiv, q] using
              hlower (1 : Fin 3)
        · simpa [sectionSixFirstLowCentralSmallPairTupleEquiv,
            sectionSixFirstLowCentralSmallTripleTuple,
            sectionSixFirstLowCentralSmallTripleTupleEquiv, p] using
              hlower (2 : Fin 3)
    have hpairTuple :
        sectionSixFirstLowCentralSmallPairTupleEquiv index.1 ∈
          propositionSixOnePrimeTuples epsilon 2
            (sectionSixFirstLowCentralSmallPairRegion epsilon) length :=
      (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).2
        hpairSource
    have hpairMapped :
        sectionSixFirstLowCentralSmallPairTupleEquiv index.1 ∈
          (sectionSixFirstPairPieceIndices epsilon length
            .lowCentralSmall).map
              sectionSixFirstLowCentralSmallPairTupleEquiv.toEmbedding := by
      rw [sectionSixFirstLowCentralSmallPairIndices_map_eq_propositionSixOnePrimeTuples
        epsilon hepsilon hepsilonSmall hlength]
      exact hpairTuple
    have hpair :
        index.1 ∈ sectionSixFirstPairPieceIndices epsilon length
          .lowCentralSmall := by
      simpa using hpairMapped
    apply mem_sectionSixFirstLowCentralSmallTripleIndices.mpr
    refine ⟨hpair, mem_sievePrimeInterval.mpr ⟨hrPrime, ?_, ?_⟩⟩
    · simpa [sectionSixZOne, X, XNat, r] using hrLower
    · exact_mod_cast hrq

/-- The triple source carrier is exactly the mapped Proposition 6.1 carrier. -/
theorem sectionSixFirstLowCentralSmallTripleIndices_map_eq_propositionSixOnePrimeTuples
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstLowCentralSmallTripleIndices epsilon length).map
        sectionSixFirstLowCentralSmallTripleTupleEquiv.toEmbedding =
      propositionSixOnePrimeTuples epsilon 3
        (sectionSixFirstLowCentralSmallTripleRegion epsilon) length := by
  classical
  ext tuple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstLowCentralSmallTriple_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro htuple
    let index : SectionSixFirstLowCentralSmallTripleIndex :=
      sectionSixFirstLowCentralSmallTripleTupleEquiv.symm tuple
    have hinverse : sectionSixFirstLowCentralSmallTripleTupleEquiv index =
        tuple :=
      sectionSixFirstLowCentralSmallTripleTupleEquiv.apply_symm_apply tuple
    refine ⟨index, (sectionSixFirstLowCentralSmallTriple_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    simpa only [sectionSixFirstLowCentralSmallTripleTuple, hinverse] using
      htuple

private theorem sectionSixFirstLowCentralSmallTripleModulus_eq_tupleModulus
    (index : SectionSixFirstLowCentralSmallTripleIndex)
    (hp : index.1.1.Prime) (hq : index.1.2.Prime) (hr : index.2.Prime) :
    sectionSixFirstLowCentralSmallTripleModulus index =
      (primeTupleProduct
        (sectionSixFirstLowCentralSmallTripleTuple index)).toPNat' := by
  rw [sectionSixFirstLowCentralSmallTripleTuple_product_eq]
  apply PNat.eq
  rw [sectionSixFirstLowCentralSmallTripleModulus_coe hp hq hr,
    Nat.toPNat'_coe, if_pos]
  exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos

/-- The triple base sum is exactly its fixed Proposition 6.1 sum. -/
theorem sectionSixFirstLowCentralSmallTripleBaseSum_eq_propositionSixOneSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowCentralSmallTripleBaseSum epsilon digit length =
      propositionSixOneSum epsilon 3
        (sectionSixFirstLowCentralSmallTripleRegion epsilon) digit length := by
  classical
  unfold sectionSixFirstLowCentralSmallTripleBaseSum propositionSixOneSum
  dsimp only
  rw [← sectionSixFirstLowCentralSmallTripleIndices_map_eq_propositionSixOnePrimeTuples
    epsilon hepsilon hepsilonSmall hlength]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro index hindex
  have htuple := (sectionSixFirstLowCentralSmallTriple_mem_iff
    hepsilon hepsilonSmall hlength index).1 hindex
  have hsource :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).1 htuple
  have hp : index.1.1.Prime := by
    simpa [sectionSixFirstLowCentralSmallTripleTuple,
      sectionSixFirstLowCentralSmallTripleTupleEquiv] using
        hsource.1 (2 : Fin 3)
  have hq : index.1.2.Prime := by
    simpa [sectionSixFirstLowCentralSmallTripleTuple,
      sectionSixFirstLowCentralSmallTripleTupleEquiv] using
        hsource.1 (1 : Fin 3)
  have hr : index.2.Prime := by
    simpa [sectionSixFirstLowCentralSmallTripleTuple,
      sectionSixFirstLowCentralSmallTripleTupleEquiv] using
        hsource.1 (0 : Fin 3)
  rw [sectionSixFirstLowCentralSmallTripleModulus_eq_tupleModulus
    index hp hq hr]
  rfl

end

end PrimesRestrictedDigits
