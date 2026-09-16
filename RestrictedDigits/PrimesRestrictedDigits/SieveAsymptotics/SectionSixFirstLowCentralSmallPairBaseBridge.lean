import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralSmallBasePresentations
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralSmallLedger
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairCarriers
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Low central-small pair base bridge

This file reindexes the pair base sum by the Proposition 6.1 role order `![q, p]`. The omitted
prime floor and upper central-product wall follow from the three-wall region on the
Proposition 6.1 carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137--138, and Section 6, p. 143,
especially Eq. (6.12).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The recurrence-native pair roles in increasing Proposition 6.1 order. -/
def sectionSixFirstLowCentralSmallPairTupleEquiv :
    SectionSixFirstStrictIndex ≃ (Fin 2 -> Nat) where
  toFun index := ![index.2, index.1]
  invFun tuple := ⟨tuple 1, tuple 0⟩
  left_inv index := by
    rcases index with ⟨p, q⟩
    rfl
  right_inv tuple := by
    funext i
    fin_cases i <;> rfl

private abbrev sectionSixFirstLowCentralSmallPairTuple
    (index : SectionSixFirstStrictIndex) : Fin 2 -> Nat :=
  sectionSixFirstLowCentralSmallPairTupleEquiv index

private theorem sectionSixFirstLowCentralSmallPair_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length
        .lowCentralSmall <->
      sectionSixFirstLowCentralSmallPairTuple index ∈
        propositionSixOnePrimeTuples epsilon 2
          (sectionSixFirstLowCentralSmallPairRegion epsilon) length := by
  classical
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1
  let q : Nat := index.2
  have hXNat : 1 < XNat := by
    simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  rw [mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength]
  constructor
  · intro hindex
    have hpiece :
        index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
          sectionSixZThree epsilon X <
              (sectionSixFirstPairProduct index : Real) ∧
            (sectionSixFirstPairProduct index : Real) <
                sectionSixZFive epsilon X ∧
              (sectionSixFirstPairSquareProduct index : Real) <
                sectionSixZSix epsilon X := by
      have hmem := (Finset.mem_filter.mp hindex).2
      simpa [sectionSixFirstPairMem, X, XNat] using hmem
    have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
    have hpData := mem_sievePrimeInterval.mp hdata.1
    have hqData := mem_sievePrimeInterval.mp hdata.2
    have hthreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hpData.1 hqData.1).1
        hqData.2.2
    have hpLog :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
        (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)).2
        (by
          simpa [sectionSixZOne, sectionSixZTwo, X, XNat, p] using
            And.intro hpData.2.1 hpData.2.2)
    have hcentralLog :
        sectionSixThetaTwo epsilon <
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero]
      apply (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).2
      simpa [sectionSixZThree, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hpiece.2.1
    have hsquareLog :
        normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q <
          1 - sectionSixThetaOne epsilon := by
      rw [sectionSixFirst_normalizedPairSquareProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero]
      apply (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).2
      simpa [sectionSixZSix, sectionSixFirstPairSquareProduct,
        X, XNat, p, q, Nat.cast_mul] using hpiece.2.2.2
    have hproductCap :
        (primeTupleProduct
            (sectionSixFirstLowCentralSmallPairTuple index) : Real) <=
          X ^ (1 - sectionSixThetaOne epsilon) := by
      have hraw : (sectionSixFirstPairProduct index : Real) <
          sectionSixZSix epsilon X :=
        hpiece.2.2.1.trans horder.2.2.2.2
      simpa [sectionSixFirstLowCentralSmallPairTuple,
        sectionSixFirstLowCentralSmallPairTupleEquiv,
        primeTupleProduct, Fin.prod_univ_two,
        sectionSixFirstPairProduct, sectionSixZSix,
        X, XNat, p, q, Nat.mul_comm] using hraw.le
    dsimp [IsPropositionSixOnePrimeTuple]
    refine ⟨?_, ?_, ?_, hproductCap, ?_⟩
    · intro i
      fin_cases i
      · simpa [sectionSixFirstLowCentralSmallPairTuple,
          sectionSixFirstLowCentralSmallPairTupleEquiv, q] using hqData.1
      · simpa [sectionSixFirstLowCentralSmallPairTuple,
          sectionSixFirstLowCentralSmallPairTupleEquiv, p] using hpData.1
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [sectionSixFirstLowCentralSmallPairTuple,
          sectionSixFirstLowCentralSmallPairTupleEquiv, p, q]
    · intro i
      fin_cases i
      · simpa [sectionSixFirstLowCentralSmallPairTuple,
          sectionSixFirstLowCentralSmallPairTupleEquiv,
          sectionSixZOne, X, XNat, q] using hqData.2.1.le
      · simpa [sectionSixFirstLowCentralSmallPairTuple,
          sectionSixFirstLowCentralSmallPairTupleEquiv,
          sectionSixZOne, X, XNat, p] using hpData.2.1.le
    · simpa [sectionSixFirstLowCentralSmallPairRegion,
        sectionSixFirstLowCentralSmallPairTuple,
        sectionSixFirstLowCentralSmallPairTupleEquiv, XNat, p, q] using
          And.intro hpLog.2 (And.intro hcentralLog hsquareLog)
  · intro htuple
    dsimp [IsPropositionSixOnePrimeTuple] at htuple
    rcases htuple with
      ⟨hprime, hmonotone, _hlower, _hproductCap, hregion⟩
    have hpPrime : p.Prime := by
      simpa [sectionSixFirstLowCentralSmallPairTuple,
        sectionSixFirstLowCentralSmallPairTupleEquiv, p] using
          hprime (1 : Fin 2)
    have hqPrime : q.Prime := by
      simpa [sectionSixFirstLowCentralSmallPairTuple,
        sectionSixFirstLowCentralSmallPairTupleEquiv, q] using
          hprime (0 : Fin 2)
    have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
    have hqPos : (0 : Real) < q := by exact_mod_cast hqPrime.pos
    have hqp : q <= p := by
      simpa [sectionSixFirstLowCentralSmallPairTuple,
        sectionSixFirstLowCentralSmallPairTupleEquiv, p, q] using
          hmonotone (show (0 : Fin 2) <= 1 by decide)
    have hregionData :
        normalizedPrimeLog XNat p <= sectionSixThetaOne epsilon ∧
          sectionSixThetaTwo epsilon <
              normalizedPrimeLog XNat p + normalizedPrimeLog XNat q ∧
            normalizedPrimeLog XNat p +
                2 * normalizedPrimeLog XNat q <
              1 - sectionSixThetaOne epsilon := by
      simpa [sectionSixFirstLowCentralSmallPairRegion,
        sectionSixFirstLowCentralSmallPairTuple,
        sectionSixFirstLowCentralSmallPairTupleEquiv, XNat, p, q] using
          hregion
    have hqLogLower :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q := by
      simp only [sectionSixThetaGap] at hregionData ⊢
      linarith
    have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) := by
      change sectionSixThetaGap epsilon < Real.logb X (q : Real) at hqLogLower
      exact (Real.lt_logb_iff_rpow_lt hX hqPos).1 hqLogLower
    have hpLower : X ^ sectionSixThetaGap epsilon < (p : Real) :=
      hqLower.trans_le (by exact_mod_cast hqp)
    have hpUpper : (p : Real) <= X ^ sectionSixThetaOne epsilon := by
      have hpLogUpper := hregionData.1
      change Real.logb X (p : Real) <= sectionSixThetaOne epsilon at hpLogUpper
      exact (Real.logb_le_iff_le_rpow hX hpPos).1 hpLogUpper
    have hproductLowerLog : sectionSixThetaTwo epsilon <
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q :=
      hregionData.2.1
    have hproductUpperLog :
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q <
          1 - sectionSixThetaTwo epsilon := by
      have hsquareLog := hregionData.2.2
      simp only [sectionSixThetaGap, sectionSixThetaOne,
        sectionSixThetaTwo] at hqLogLower hsquareLog ⊢
      linarith
    have hproductLower : sectionSixZThree epsilon X <
        (sectionSixFirstPairProduct index : Real) := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpPrime.ne_zero hqPrime.ne_zero] at hproductLowerLog
      have hraw := (Real.lt_logb_iff_rpow_lt hX
        (by exact_mod_cast Nat.mul_pos hpPrime.pos hqPrime.pos)).1
          hproductLowerLog
      simpa [sectionSixZThree, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hproductUpper : (sectionSixFirstPairProduct index : Real) <
        sectionSixZFive epsilon X := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpPrime.ne_zero hqPrime.ne_zero] at hproductUpperLog
      have hraw := (Real.logb_lt_iff_lt_rpow hX
        (by exact_mod_cast Nat.mul_pos hpPrime.pos hqPrime.pos)).1
          hproductUpperLog
      simpa [sectionSixZFive, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hsquare : (sectionSixFirstPairSquareProduct index : Real) <
        sectionSixZSix epsilon X := by
      have hsquareLog := hregionData.2.2
      rw [sectionSixFirst_normalizedPairSquareProduct_eq
        hpPrime.ne_zero hqPrime.ne_zero] at hsquareLog
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpPrime.pos hqPrime.pos) hqPrime.pos)).1 hsquareLog
      simpa [sectionSixZSix, sectionSixFirstPairSquareProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hzSixLtX : sectionSixZSix epsilon X < X := by
      rw [sectionSixZSix]
      calc
        X ^ (1 - sectionSixThetaOne epsilon) < X ^ (1 : Real) :=
          Real.rpow_lt_rpow_of_exponent_lt hX (by
            linarith [(sectionSix_parameter_bounds
              hepsilon hepsilonSmall).2.1])
        _ = X := Real.rpow_one X
    have hcapNat : p * q * q <= XNat := by
      have hcapReal : ((p * q * q : Nat) : Real) <= (XNat : Real) := by
        simpa [sectionSixFirstPairSquareProduct, X, XNat, p, q] using
          (hsquare.trans hzSixLtX).le
      exact_mod_cast hcapReal
    have hlow : index ∈ sectionSixFirstLowStrictIndices epsilon length := by
      apply mem_sectionSixFirstSecondRepeatedIndices.mpr
      constructor
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hpPrime, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, p] using hpLower
        · simpa [sectionSixZTwo, X, XNat, p] using hpUpper
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hqPrime, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, q] using hqLower
        · exact (sectionSixFirst_direct_pairThreshold_iff
            hpPrime hqPrime).2 ⟨hqp, by simpa only [XNat] using hcapNat⟩
    apply Finset.mem_filter.mpr
    constructor
    · simp [sectionSixFirstStrictIndices, hlow]
    · simpa [sectionSixFirstPairMem, X, XNat] using
        And.intro hlow
          (And.intro hproductLower (And.intro hproductUpper hsquare))

/-- The pair source carrier is exactly the mapped Proposition 6.1 carrier. -/
theorem sectionSixFirstLowCentralSmallPairIndices_map_eq_propositionSixOnePrimeTuples
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstPairPieceIndices epsilon length .lowCentralSmall).map
        sectionSixFirstLowCentralSmallPairTupleEquiv.toEmbedding =
      propositionSixOnePrimeTuples epsilon 2
        (sectionSixFirstLowCentralSmallPairRegion epsilon) length := by
  classical
  ext tuple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstLowCentralSmallPair_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro htuple
    let index : SectionSixFirstStrictIndex :=
      sectionSixFirstLowCentralSmallPairTupleEquiv.symm tuple
    have hinverse : sectionSixFirstLowCentralSmallPairTupleEquiv index =
        tuple :=
      sectionSixFirstLowCentralSmallPairTupleEquiv.apply_symm_apply tuple
    refine ⟨index, (sectionSixFirstLowCentralSmallPair_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    simpa only [sectionSixFirstLowCentralSmallPairTuple, hinverse] using htuple

private theorem sectionSixFirstLowCentralSmallPairModulus_eq_tupleModulus
    (index : SectionSixFirstStrictIndex)
    (hp : index.1.Prime) (hq : index.2.Prime) :
    sectionSixFirstPairModulus index =
      (primeTupleProduct
        (sectionSixFirstLowCentralSmallPairTuple index)).toPNat' := by
  apply PNat.eq
  rw [sectionSixFirstPairModulus_coe hp hq, Nat.toPNat'_coe,
    if_pos]
  · simp [sectionSixFirstPairProduct,
      sectionSixFirstLowCentralSmallPairTuple,
      sectionSixFirstLowCentralSmallPairTupleEquiv,
      primeTupleProduct, Fin.prod_univ_two, Nat.mul_comm]
  · simp [sectionSixFirstLowCentralSmallPairTuple,
      sectionSixFirstLowCentralSmallPairTupleEquiv,
      primeTupleProduct, Fin.prod_univ_two, hp.pos, hq.pos]

/-- The pair base sum is exactly its fixed Proposition 6.1 sum. -/
theorem sectionSixFirstLowCentralSmallPairBaseSum_eq_propositionSixOneSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowCentralSmallPairBaseSum epsilon digit length =
      propositionSixOneSum epsilon 2
        (sectionSixFirstLowCentralSmallPairRegion epsilon) digit length := by
  classical
  unfold sectionSixFirstLowCentralSmallPairBaseSum propositionSixOneSum
  dsimp only
  rw [← sectionSixFirstLowCentralSmallPairIndices_map_eq_propositionSixOnePrimeTuples
    epsilon hepsilon hepsilonSmall hlength]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro index hindex
  have htuple := (sectionSixFirstLowCentralSmallPair_mem_iff
    hepsilon hepsilonSmall hlength index).1 hindex
  have hsource :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).1 htuple
  have hp : index.1.Prime := by
    simpa [sectionSixFirstLowCentralSmallPairTuple,
      sectionSixFirstLowCentralSmallPairTupleEquiv] using
        hsource.1 (1 : Fin 2)
  have hq : index.2.Prime := by
    simpa [sectionSixFirstLowCentralSmallPairTuple,
      sectionSixFirstLowCentralSmallPairTupleEquiv] using
        hsource.1 (0 : Fin 2)
  rw [sectionSixFirstLowCentralSmallPairModulus_eq_tupleModulus index hp hq]
  rfl

end

end PrimesRestrictedDigits
