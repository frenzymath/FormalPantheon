import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstHighCentralSmallBasePresentations
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstHighCentralSmallLedger
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairCarriers
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# High central-small pair base bridge

This file reindexes the pair base sum by the Proposition 6.1 role order `![q, p]`. The two
central product walls are recovered from the four-wall presentation on the Proposition 6.1
carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137--138, and the `S3` decomposition,
pp. 145--146, especially Eq. (6.16).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The recurrence-native pair roles in increasing Proposition 6.1 order. -/
def sectionSixFirstHighCentralSmallPairTupleEquiv :
    SectionSixFirstStrictIndex ≃ (Fin 2 -> Nat) where
  toFun index := ![index.2, index.1]
  invFun tuple := ⟨tuple 1, tuple 0⟩
  left_inv index := by
    rcases index with ⟨p, q⟩
    rfl
  right_inv tuple := by
    funext i
    fin_cases i <;> rfl

private abbrev sectionSixFirstHighCentralSmallPairTuple
    (index : SectionSixFirstStrictIndex) : Fin 2 -> Nat :=
  sectionSixFirstHighCentralSmallPairTupleEquiv index

private theorem sectionSixFirstHighCentralSmallPair_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length
        .highCentralSmall <->
      sectionSixFirstHighCentralSmallPairTuple index ∈
        propositionSixOnePrimeTuples epsilon 2
          (sectionSixFirstHighCentralSmallPairRegion epsilon) length := by
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
        index ∈ sectionSixFirstHighStrictIndices epsilon length ∧
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
        (sectionSixThetaTwo epsilon) (1 / 2 : Real)).2
        (by
          simpa [sectionSixZThree, sectionSixZFour_eq_rpow,
            X, XNat, p] using And.intro hpData.2.1 hpData.2.2)
    have hqLogLower :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q := by
      change sectionSixThetaGap epsilon < Real.logb X (q : Real)
      apply (Real.lt_logb_iff_rpow_lt hX
        (by exact_mod_cast hqData.1.pos)).2
      simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
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
            (sectionSixFirstHighCentralSmallPairTuple index) : Real) <=
          X ^ (1 - sectionSixThetaOne epsilon) := by
      have hraw : (sectionSixFirstPairProduct index : Real) <
          sectionSixZSix epsilon X :=
        hpiece.2.2.1.trans horder.2.2.2.2
      simpa [sectionSixFirstHighCentralSmallPairTuple,
        sectionSixFirstHighCentralSmallPairTupleEquiv,
        primeTupleProduct, Fin.prod_univ_two,
        sectionSixFirstPairProduct, sectionSixZSix,
        X, XNat, p, q, Nat.mul_comm] using hraw.le
    dsimp [IsPropositionSixOnePrimeTuple]
    refine ⟨?_, ?_, ?_, hproductCap, ?_⟩
    · intro i
      fin_cases i
      · simpa [sectionSixFirstHighCentralSmallPairTuple,
          sectionSixFirstHighCentralSmallPairTupleEquiv, q] using hqData.1
      · simpa [sectionSixFirstHighCentralSmallPairTuple,
          sectionSixFirstHighCentralSmallPairTupleEquiv, p] using hpData.1
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [sectionSixFirstHighCentralSmallPairTuple,
          sectionSixFirstHighCentralSmallPairTupleEquiv, p, q]
    · intro i
      fin_cases i
      · simpa [sectionSixFirstHighCentralSmallPairTuple,
          sectionSixFirstHighCentralSmallPairTupleEquiv,
          sectionSixZOne, X, XNat, q] using hqData.2.1.le
      · have hqLePReal : (q : Real) <= (p : Real) := by
          exact_mod_cast hthreshold.1
        simpa [sectionSixFirstHighCentralSmallPairTuple,
          sectionSixFirstHighCentralSmallPairTupleEquiv,
          sectionSixZOne, X, XNat, p, q] using
            hqData.2.1.le.trans hqLePReal
    · simpa [sectionSixFirstHighCentralSmallPairRegion,
        sectionSixFirstHighCentralSmallPairTuple,
        sectionSixFirstHighCentralSmallPairTupleEquiv, XNat, p, q] using
          And.intro hqLogLower
            (And.intro hpLog.1 (And.intro hpLog.2 hsquareLog))
  · intro htuple
    dsimp [IsPropositionSixOnePrimeTuple] at htuple
    rcases htuple with
      ⟨hprime, hmonotone, _hlower, _hproductCap, hregion⟩
    have hpPrime : p.Prime := by
      simpa [sectionSixFirstHighCentralSmallPairTuple,
        sectionSixFirstHighCentralSmallPairTupleEquiv, p] using
          hprime (1 : Fin 2)
    have hqPrime : q.Prime := by
      simpa [sectionSixFirstHighCentralSmallPairTuple,
        sectionSixFirstHighCentralSmallPairTupleEquiv, q] using
          hprime (0 : Fin 2)
    have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
    have hqPos : (0 : Real) < q := by exact_mod_cast hqPrime.pos
    have hqp : q <= p := by
      simpa [sectionSixFirstHighCentralSmallPairTuple,
        sectionSixFirstHighCentralSmallPairTupleEquiv, p, q] using
          hmonotone (show (0 : Fin 2) <= 1 by decide)
    have hregionData :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q ∧
          sectionSixThetaTwo epsilon < normalizedPrimeLog XNat p ∧
            normalizedPrimeLog XNat p <= (1 / 2 : Real) ∧
              normalizedPrimeLog XNat p +
                  2 * normalizedPrimeLog XNat q <
                1 - sectionSixThetaOne epsilon := by
      simpa [sectionSixFirstHighCentralSmallPairRegion,
        sectionSixFirstHighCentralSmallPairTuple,
        sectionSixFirstHighCentralSmallPairTupleEquiv, XNat, p, q] using
          hregion
    have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) := by
      have hqLog := hregionData.1
      change sectionSixThetaGap epsilon < Real.logb X (q : Real) at hqLog
      exact (Real.lt_logb_iff_rpow_lt hX hqPos).1 hqLog
    have hpLog : normalizedPrimeLog XNat p ∈
        Set.Ioc (sectionSixThetaTwo epsilon) (1 / 2 : Real) :=
      ⟨hregionData.2.1, hregionData.2.2.1⟩
    have hpRange :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpPrime
        (sectionSixThetaTwo epsilon) (1 / 2 : Real)).1 hpLog
    have hgapPos : 0 < sectionSixThetaGap epsilon :=
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
    have hproductLowerLog : sectionSixThetaTwo epsilon <
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q := by
      linarith [hregionData.1, hregionData.2.1]
    have hproductUpperLog :
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q <
          1 - sectionSixThetaTwo epsilon := by
      have hqLog := hregionData.1
      have hsquareLog := hregionData.2.2.2
      simp only [sectionSixThetaGap, sectionSixThetaOne,
        sectionSixThetaTwo] at hqLog hsquareLog ⊢
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
      have hsquareLog := hregionData.2.2.2
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
    have hhigh : index ∈ sectionSixFirstHighStrictIndices epsilon length := by
      apply mem_sectionSixFirstSecondRepeatedIndices.mpr
      constructor
      · apply mem_sievePrimeInterval.mpr
        simpa [sectionSixZThree, sectionSixZFour_eq_rpow,
          X, XNat, p] using And.intro hpPrime hpRange
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hqPrime, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, q] using hqLower
        · exact (sectionSixFirst_direct_pairThreshold_iff
            hpPrime hqPrime).2 ⟨hqp, by simpa only [XNat] using hcapNat⟩
    apply Finset.mem_filter.mpr
    constructor
    · simp [sectionSixFirstStrictIndices, hhigh]
    · simpa [sectionSixFirstPairMem, X, XNat] using
        And.intro hhigh
          (And.intro hproductLower (And.intro hproductUpper hsquare))

/-- The pair source carrier is exactly the mapped Proposition 6.1 carrier. -/
theorem sectionSixFirstHighCentralSmallPairIndices_map_eq_propositionSixOnePrimeTuples
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstPairPieceIndices epsilon length .highCentralSmall).map
        sectionSixFirstHighCentralSmallPairTupleEquiv.toEmbedding =
      propositionSixOnePrimeTuples epsilon 2
        (sectionSixFirstHighCentralSmallPairRegion epsilon) length := by
  classical
  ext tuple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstHighCentralSmallPair_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro htuple
    let index : SectionSixFirstStrictIndex :=
      sectionSixFirstHighCentralSmallPairTupleEquiv.symm tuple
    have hinverse : sectionSixFirstHighCentralSmallPairTupleEquiv index =
        tuple :=
      sectionSixFirstHighCentralSmallPairTupleEquiv.apply_symm_apply tuple
    refine ⟨index, (sectionSixFirstHighCentralSmallPair_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    simpa only [sectionSixFirstHighCentralSmallPairTuple, hinverse] using htuple

private theorem sectionSixFirstHighCentralSmallPairModulus_eq_tupleModulus
    (index : SectionSixFirstStrictIndex)
    (hp : index.1.Prime) (hq : index.2.Prime) :
    sectionSixFirstPairModulus index =
      (primeTupleProduct
        (sectionSixFirstHighCentralSmallPairTuple index)).toPNat' := by
  apply PNat.eq
  rw [sectionSixFirstPairModulus_coe hp hq, Nat.toPNat'_coe,
    if_pos]
  · simp [sectionSixFirstPairProduct,
      sectionSixFirstHighCentralSmallPairTuple,
      sectionSixFirstHighCentralSmallPairTupleEquiv,
      primeTupleProduct, Fin.prod_univ_two, Nat.mul_comm]
  · simp [sectionSixFirstHighCentralSmallPairTuple,
      sectionSixFirstHighCentralSmallPairTupleEquiv,
      primeTupleProduct, Fin.prod_univ_two, hp.pos, hq.pos]

/-- The pair base sum is exactly its fixed Proposition 6.1 sum. -/
theorem sectionSixFirstHighCentralSmallPairBaseSum_eq_propositionSixOneSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstHighCentralSmallPairBaseSum epsilon digit length =
      propositionSixOneSum epsilon 2
        (sectionSixFirstHighCentralSmallPairRegion epsilon) digit length := by
  classical
  unfold sectionSixFirstHighCentralSmallPairBaseSum propositionSixOneSum
  dsimp only
  rw [← sectionSixFirstHighCentralSmallPairIndices_map_eq_propositionSixOnePrimeTuples
    epsilon hepsilon hepsilonSmall hlength]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro index hindex
  have htuple := (sectionSixFirstHighCentralSmallPair_mem_iff
    hepsilon hepsilonSmall hlength index).1 hindex
  have hsource :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).1 htuple
  have hp : index.1.Prime := by
    simpa [sectionSixFirstHighCentralSmallPairTuple,
      sectionSixFirstHighCentralSmallPairTupleEquiv] using
        hsource.1 (1 : Fin 2)
  have hq : index.2.Prime := by
    simpa [sectionSixFirstHighCentralSmallPairTuple,
      sectionSixFirstHighCentralSmallPairTupleEquiv] using
        hsource.1 (0 : Fin 2)
  rw [sectionSixFirstHighCentralSmallPairModulus_eq_tupleModulus index hp hq]
  rfl

end

end PrimesRestrictedDigits
