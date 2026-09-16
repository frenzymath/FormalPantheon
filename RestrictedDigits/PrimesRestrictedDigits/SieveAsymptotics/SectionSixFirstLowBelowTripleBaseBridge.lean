import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowPairBaseBridge

/-!
# Low-below triple base bridge

This file reindexes the triple base sum by the Proposition 6.1 role order `![r, q, p]`. The
inherited pair data is reconstructed through the public pair carrier equality; the triple
region replaces the pair's strict `q` floor by the strict `r` floor.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137--138, and Section 6, pp. 143--144,
especially Eq. (6.13).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The recurrence-native triple roles in increasing Proposition 6.1 order. -/
def sectionSixFirstLowBelowTripleTupleEquiv :
    SectionSixFirstLowBelowTripleIndex ≃ (Fin 3 -> Nat) where
  toFun index := ![index.2, index.1.2, index.1.1]
  invFun tuple := ⟨⟨tuple 2, tuple 1⟩, tuple 0⟩
  left_inv index := by rcases index with ⟨⟨p, q⟩, r⟩; rfl
  right_inv tuple := by funext i; fin_cases i <;> rfl

private abbrev sectionSixFirstLowBelowTripleTuple
    (index : SectionSixFirstLowBelowTripleIndex) : Fin 3 -> Nat :=
  sectionSixFirstLowBelowTripleTupleEquiv index

private theorem sectionSixFirstLowBelowPairTuple_product_eq
    (index : SectionSixFirstStrictIndex) :
    primeTupleProduct (sectionSixFirstLowBelowPairTupleEquiv index) =
      sectionSixFirstPairProduct index := by
  simp [sectionSixFirstLowBelowPairTupleEquiv,
    primeTupleProduct, Fin.prod_univ_two,
    sectionSixFirstPairProduct, Nat.mul_comm]

private theorem sectionSixFirstLowBelowTripleTuple_product_eq
    (index : SectionSixFirstLowBelowTripleIndex) :
    primeTupleProduct (sectionSixFirstLowBelowTripleTuple index) =
      sectionSixFirstLowBelowTripleProduct index := by
  simp [sectionSixFirstLowBelowTripleTuple,
    sectionSixFirstLowBelowTripleTupleEquiv,
    primeTupleProduct, Fin.prod_univ_succ,
    sectionSixFirstLowBelowTripleProduct,
    sectionSixFirstPairProduct, Nat.mul_comm, Nat.mul_left_comm]

private theorem sectionSixFirstLowBelow_normalizedTripleProduct_eq
    {X p q r : Nat} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    normalizedPrimeLog X p + normalizedPrimeLog X q +
        normalizedPrimeLog X r =
      Real.logb (X : Real) ((p * q * r : Nat) : Real) := by
  have hpq := sectionSixFirst_normalizedPairProduct_eq
    (X := X) (p := p) (q := q) hp hq
  calc
    normalizedPrimeLog X p + normalizedPrimeLog X q +
          normalizedPrimeLog X r =
        (normalizedPrimeLog X q + normalizedPrimeLog X p) +
          normalizedPrimeLog X r := by ring
    _ = Real.logb (X : Real) ((p * q : Nat) : Real) +
          Real.logb (X : Real) (r : Real) := by
      rw [hpq]
      rfl
    _ = Real.logb (X : Real)
          (((p * q : Nat) : Real) * (r : Real)) := by
      rw [Real.logb_mul]
      · exact_mod_cast Nat.mul_ne_zero hp hq
      · exact_mod_cast hr
    _ = Real.logb (X : Real) ((p * q * r : Nat) : Real) := by
      norm_num only [Nat.cast_mul]

private theorem sectionSixFirstLowBelowTriple_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstLowBelowTripleIndex) :
    index ∈ sectionSixFirstLowBelowTripleIndices epsilon length <->
      sectionSixFirstLowBelowTripleTuple index ∈
        propositionSixOnePrimeTuples epsilon 3
          (sectionSixFirstLowBelowTripleRegion epsilon) length := by
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
    have htriple := mem_sectionSixFirstLowBelowTripleIndices.mp hindex
    have hpairMapped :
        sectionSixFirstLowBelowPairTupleEquiv index.1 ∈
          (sectionSixFirstPairPieceIndices epsilon length .lowBelow).map
            sectionSixFirstLowBelowPairTupleEquiv.toEmbedding :=
      Finset.mem_map.mpr ⟨index.1, htriple.1, rfl⟩
    have hpairTuple :
        sectionSixFirstLowBelowPairTupleEquiv index.1 ∈
          propositionSixOnePrimeTuples epsilon 2
            (sectionSixFirstLowBelowPairRegion epsilon) length := by
      rw [← sectionSixFirstLowBelowPairIndices_map_eq_propositionSixOnePrimeTuples
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
      simpa [sectionSixFirstLowBelowPairTupleEquiv, p, q] using
        hpairMonotone (show (0 : Fin 2) <= 1 by decide)
    have hrp : r <= p := hrq.trans hqp
    have hrLog :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat r := by
      change sectionSixThetaGap epsilon < Real.logb X (r : Real)
      apply (Real.lt_logb_iff_rpow_lt hX
        (by exact_mod_cast hrData.1.pos)).2
      simpa [sectionSixZOne, X, XNat, r] using hrData.2.1
    have hpairRegionData :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q /\
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q <
            sectionSixThetaOne epsilon := by
      simpa [sectionSixFirstLowBelowPairRegion,
        sectionSixFirstLowBelowPairTupleEquiv, XNat, p, q] using hpairRegion
    have hqPos : (0 : Real) < (q : Real) := by
      exact_mod_cast (hpairPrime (0 : Fin 2)).pos
    have hrPos : (0 : Real) < (r : Real) := by
      exact_mod_cast hrData.1.pos
    have hqpLog :
        normalizedPrimeLog XNat q <= normalizedPrimeLog XNat p := by
      change Real.logb X (q : Real) <= Real.logb X (p : Real)
      exact Real.logb_le_logb_of_le hX hqPos (by exact_mod_cast hqp)
    have hrqLog :
        normalizedPrimeLog XNat r <= normalizedPrimeLog XNat q := by
      change Real.logb X (r : Real) <= Real.logb X (q : Real)
      exact Real.logb_le_logb_of_le hX hrPos (by exact_mod_cast hrq)
    have htripleLog :
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q +
            normalizedPrimeLog XNat r <
          1 - sectionSixThetaOne epsilon := by
      unfold sectionSixThetaOne
      unfold sectionSixThetaOne at hpairRegionData
      linarith
    have htripleCap :
        ((p * q * r : Nat) : Real) <=
          X ^ (1 - sectionSixThetaOne epsilon) := by
      rw [sectionSixFirstLowBelow_normalizedTripleProduct_eq
        (X := XNat) (p := p) (q := q) (r := r)
        (hpairPrime (1 : Fin 2)).ne_zero
        (hpairPrime (0 : Fin 2)).ne_zero hrData.1.ne_zero] at htripleLog
      exact ((Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos (hpairPrime (1 : Fin 2)).pos
            (hpairPrime (0 : Fin 2)).pos) hrData.1.pos)).1 htripleLog).le
    have hproductCap :
        (primeTupleProduct
            (sectionSixFirstLowBelowTripleTuple index) : Real) <=
          X ^ (1 - sectionSixThetaOne epsilon) := by
      rw [sectionSixFirstLowBelowTripleTuple_product_eq]
      simpa [sectionSixFirstLowBelowTripleProduct,
        sectionSixFirstPairProduct, p, q, r] using htripleCap
    dsimp [IsPropositionSixOnePrimeTuple]
    refine ⟨?_, ?_, ?_, hproductCap, ?_⟩
    · intro i
      fin_cases i
      · simpa [sectionSixFirstLowBelowTripleTuple,
          sectionSixFirstLowBelowTripleTupleEquiv, r] using hrData.1
      · simpa [sectionSixFirstLowBelowTripleTuple,
          sectionSixFirstLowBelowTripleTupleEquiv,
          sectionSixFirstLowBelowPairTupleEquiv, q] using
            hpairPrime (0 : Fin 2)
      · simpa [sectionSixFirstLowBelowTripleTuple,
          sectionSixFirstLowBelowTripleTupleEquiv,
          sectionSixFirstLowBelowPairTupleEquiv, p] using
            hpairPrime (1 : Fin 2)
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [sectionSixFirstLowBelowTripleTuple,
          sectionSixFirstLowBelowTripleTupleEquiv, p, q, r]
    · intro i
      fin_cases i
      · simpa [sectionSixFirstLowBelowTripleTuple,
          sectionSixFirstLowBelowTripleTupleEquiv,
          sectionSixZOne, X, XNat, r] using hrData.2.1.le
      · simpa [sectionSixFirstLowBelowTripleTuple,
          sectionSixFirstLowBelowTripleTupleEquiv,
          sectionSixFirstLowBelowPairTupleEquiv, q] using
            hpairLower (0 : Fin 2)
      · simpa [sectionSixFirstLowBelowTripleTuple,
          sectionSixFirstLowBelowTripleTupleEquiv,
          sectionSixFirstLowBelowPairTupleEquiv, p] using
            hpairLower (1 : Fin 2)
    · simpa [sectionSixFirstLowBelowTripleRegion,
        sectionSixFirstLowBelowTripleTuple,
        sectionSixFirstLowBelowTripleTupleEquiv, XNat, p, q, r] using
          And.intro hrLog hpairRegionData.2
  · intro htuple
    dsimp [IsPropositionSixOnePrimeTuple] at htuple
    rcases htuple with
      ⟨hprime, hmonotone, hlower, hproductCap, hregion⟩
    have hpPrime : p.Prime := by
      simpa [sectionSixFirstLowBelowTripleTuple,
        sectionSixFirstLowBelowTripleTupleEquiv, p] using
          hprime (2 : Fin 3)
    have hqPrime : q.Prime := by
      simpa [sectionSixFirstLowBelowTripleTuple,
        sectionSixFirstLowBelowTripleTupleEquiv, q] using
          hprime (1 : Fin 3)
    have hrPrime : r.Prime := by
      simpa [sectionSixFirstLowBelowTripleTuple,
        sectionSixFirstLowBelowTripleTupleEquiv, r] using
          hprime (0 : Fin 3)
    have hrPos : (0 : Real) < r := by exact_mod_cast hrPrime.pos
    have hrq : r <= q := by
      simpa [sectionSixFirstLowBelowTripleTuple,
        sectionSixFirstLowBelowTripleTupleEquiv, q, r] using
          hmonotone (show (0 : Fin 3) <= 1 by decide)
    have hqp : q <= p := by
      simpa [sectionSixFirstLowBelowTripleTuple,
        sectionSixFirstLowBelowTripleTupleEquiv, p, q] using
          hmonotone (show (1 : Fin 3) <= 2 by decide)
    have hregionData :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat r /\
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q <
            sectionSixThetaOne epsilon := by
      simpa [sectionSixFirstLowBelowTripleRegion,
        sectionSixFirstLowBelowTripleTuple,
        sectionSixFirstLowBelowTripleTupleEquiv, XNat, p, q, r] using hregion
    have hrLower : X ^ sectionSixThetaGap epsilon < (r : Real) := by
      have hrLog := hregionData.1
      change sectionSixThetaGap epsilon < Real.logb X (r : Real) at hrLog
      exact (Real.lt_logb_iff_rpow_lt hX hrPos).1 hrLog
    have hrqLog :
        normalizedPrimeLog XNat r <= normalizedPrimeLog XNat q := by
      change Real.logb X (r : Real) <= Real.logb X (q : Real)
      exact Real.logb_le_logb_of_le hX hrPos (by exact_mod_cast hrq)
    have hpairProductLe :
        primeTupleProduct (sectionSixFirstLowBelowPairTupleEquiv index.1) <=
          primeTupleProduct (sectionSixFirstLowBelowTripleTuple index) := by
      rw [sectionSixFirstLowBelowPairTuple_product_eq,
        sectionSixFirstLowBelowTripleTuple_product_eq]
      unfold sectionSixFirstLowBelowTripleProduct
      calc
        sectionSixFirstPairProduct index.1 =
            sectionSixFirstPairProduct index.1 * 1 := by simp
        _ <= sectionSixFirstPairProduct index.1 * r :=
          Nat.mul_le_mul_left _ hrPrime.one_le
        _ = sectionSixFirstPairProduct index.1 * index.2 := by rfl
    have hpairProductCap :
        (primeTupleProduct
            (sectionSixFirstLowBelowPairTupleEquiv index.1) : Real) <=
          X ^ (1 - sectionSixThetaOne epsilon) := by
      have hpairProductLeReal :
          (primeTupleProduct
              (sectionSixFirstLowBelowPairTupleEquiv index.1) : Real) <=
            (primeTupleProduct
              (sectionSixFirstLowBelowTripleTuple index) : Real) := by
        exact_mod_cast hpairProductLe
      exact hpairProductLeReal.trans hproductCap
    have hpairRegion :
        (fun i => normalizedPrimeLog XNat
            (sectionSixFirstLowBelowPairTupleEquiv index.1 i)) ∈
          sectionSixFirstLowBelowPairRegion epsilon := by
      simpa [sectionSixFirstLowBelowPairRegion,
        sectionSixFirstLowBelowPairTupleEquiv, XNat, p, q] using
          And.intro (hregionData.1.trans_le hrqLog) hregionData.2
    have hpairSource :
        IsPropositionSixOnePrimeTuple epsilon length
          (sectionSixFirstLowBelowPairRegion epsilon)
          (sectionSixFirstLowBelowPairTupleEquiv index.1) := by
      dsimp [IsPropositionSixOnePrimeTuple]
      refine ⟨?_, ?_, ?_, hpairProductCap, hpairRegion⟩
      · intro i
        fin_cases i
        · simpa [sectionSixFirstLowBelowPairTupleEquiv, q] using hqPrime
        · simpa [sectionSixFirstLowBelowPairTupleEquiv, p] using hpPrime
      · intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [sectionSixFirstLowBelowPairTupleEquiv, p, q]
      · intro i
        fin_cases i
        · simpa [sectionSixFirstLowBelowPairTupleEquiv,
            sectionSixFirstLowBelowTripleTuple,
            sectionSixFirstLowBelowTripleTupleEquiv, q] using
              hlower (1 : Fin 3)
        · simpa [sectionSixFirstLowBelowPairTupleEquiv,
            sectionSixFirstLowBelowTripleTuple,
            sectionSixFirstLowBelowTripleTupleEquiv, p] using
              hlower (2 : Fin 3)
    have hpairTuple :
        sectionSixFirstLowBelowPairTupleEquiv index.1 ∈
          propositionSixOnePrimeTuples epsilon 2
            (sectionSixFirstLowBelowPairRegion epsilon) length :=
      (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).2
        hpairSource
    have hpairMapped :
        sectionSixFirstLowBelowPairTupleEquiv index.1 ∈
          (sectionSixFirstPairPieceIndices epsilon length .lowBelow).map
            sectionSixFirstLowBelowPairTupleEquiv.toEmbedding := by
      rw [sectionSixFirstLowBelowPairIndices_map_eq_propositionSixOnePrimeTuples
        epsilon hepsilon hepsilonSmall hlength]
      exact hpairTuple
    have hpair :
        index.1 ∈ sectionSixFirstPairPieceIndices epsilon length .lowBelow := by
      simpa using hpairMapped
    apply mem_sectionSixFirstLowBelowTripleIndices.mpr
    refine ⟨hpair, mem_sievePrimeInterval.mpr ⟨hrPrime, ?_, ?_⟩⟩
    · simpa [sectionSixZOne, X, XNat, r] using hrLower
    · exact_mod_cast hrq

/-- The triple source carrier is exactly the mapped Proposition 6.1 carrier. -/
theorem sectionSixFirstLowBelowTripleIndices_map_eq_propositionSixOnePrimeTuples
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstLowBelowTripleIndices epsilon length).map
        sectionSixFirstLowBelowTripleTupleEquiv.toEmbedding =
      propositionSixOnePrimeTuples epsilon 3
        (sectionSixFirstLowBelowTripleRegion epsilon) length := by
  classical
  ext tuple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstLowBelowTriple_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro htuple
    let index : SectionSixFirstLowBelowTripleIndex :=
      sectionSixFirstLowBelowTripleTupleEquiv.symm tuple
    have hinverse : sectionSixFirstLowBelowTripleTupleEquiv index = tuple :=
      sectionSixFirstLowBelowTripleTupleEquiv.apply_symm_apply tuple
    refine ⟨index, (sectionSixFirstLowBelowTriple_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    simpa only [sectionSixFirstLowBelowTripleTuple, hinverse] using htuple

private theorem sectionSixFirstLowBelowTripleModulus_eq_tupleModulus
    (index : SectionSixFirstLowBelowTripleIndex)
    (hp : index.1.1.Prime) (hq : index.1.2.Prime) (hr : index.2.Prime) :
    sectionSixFirstLowBelowTripleModulus index =
      (primeTupleProduct
        (sectionSixFirstLowBelowTripleTuple index)).toPNat' := by
  rw [sectionSixFirstLowBelowTripleTuple_product_eq]
  apply PNat.eq
  rw [sectionSixFirstLowBelowTripleModulus_coe hp hq hr,
    Nat.toPNat'_coe, if_pos]
  exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos

/-- The triple base sum is exactly its fixed Proposition 6.1 sum. -/
theorem sectionSixFirstLowBelowTripleBaseSum_eq_propositionSixOneSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowBelowTripleBaseSum epsilon digit length =
      propositionSixOneSum epsilon 3
        (sectionSixFirstLowBelowTripleRegion epsilon) digit length := by
  classical
  unfold sectionSixFirstLowBelowTripleBaseSum propositionSixOneSum
  dsimp only
  rw [← sectionSixFirstLowBelowTripleIndices_map_eq_propositionSixOnePrimeTuples
    epsilon hepsilon hepsilonSmall hlength]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro index hindex
  have htuple := (sectionSixFirstLowBelowTriple_mem_iff
    hepsilon hepsilonSmall hlength index).1 hindex
  have hsource :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).1 htuple
  have hp : index.1.1.Prime := by
    simpa [sectionSixFirstLowBelowTripleTuple,
      sectionSixFirstLowBelowTripleTupleEquiv] using
        hsource.1 (2 : Fin 3)
  have hq : index.1.2.Prime := by
    simpa [sectionSixFirstLowBelowTripleTuple,
      sectionSixFirstLowBelowTripleTupleEquiv] using
        hsource.1 (1 : Fin 3)
  have hr : index.2.Prime := by
    simpa [sectionSixFirstLowBelowTripleTuple,
      sectionSixFirstLowBelowTripleTupleEquiv] using
        hsource.1 (0 : Fin 3)
  rw [sectionSixFirstLowBelowTripleModulus_eq_tupleModulus index hp hq hr]
  rfl

end

end PrimesRestrictedDigits
