import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowBelowBasePresentations
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowBelowLedger
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairCarriers
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Low-below pair base bridge

This file reindexes the low-below pair base sum by the Proposition 6.1 role order `![q, p]`.
The Proposition carrier supplies order and weak floors; the two strict presentation walls
recover the exact low-below product range and the inherited square-root cutoff.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137--138, and Section 6, pp. 143--144,
especially Eq. (6.13).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The recurrence-native pair roles in increasing Proposition 6.1 order. -/
def sectionSixFirstLowBelowPairTupleEquiv :
    SectionSixFirstStrictIndex ≃ (Fin 2 -> Nat) where
  toFun index := ![index.2, index.1]
  invFun tuple := ⟨tuple 1, tuple 0⟩
  left_inv index := by rcases index with ⟨p, q⟩; rfl
  right_inv tuple := by funext i; fin_cases i <;> rfl

private abbrev sectionSixFirstLowBelowPairTuple
    (index : SectionSixFirstStrictIndex) : Fin 2 -> Nat :=
  sectionSixFirstLowBelowPairTupleEquiv index

private theorem sectionSixFirstLowBelowPair_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length .lowBelow <->
      sectionSixFirstLowBelowPairTuple index ∈
        propositionSixOnePrimeTuples epsilon 2
          (sectionSixFirstLowBelowPairRegion epsilon) length := by
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
          sectionSixZOne epsilon X <
              (sectionSixFirstPairProduct index : Real) ∧
            (sectionSixFirstPairProduct index : Real) <
              sectionSixZTwo epsilon X := by
      have hmem := (Finset.mem_filter.mp hindex).2
      simpa [sectionSixFirstPairMem, X, XNat] using hmem
    have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
    have hpData := mem_sievePrimeInterval.mp hdata.1
    have hqData := mem_sievePrimeInterval.mp hdata.2
    have hthreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hpData.1 hqData.1).1
        hqData.2.2
    have hqLogLower :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q := by
      change sectionSixThetaGap epsilon < Real.logb X (q : Real)
      apply (Real.lt_logb_iff_rpow_lt hX
        (by exact_mod_cast hqData.1.pos)).2
      simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
    have hproductUpperLog :
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q <
          sectionSixThetaOne epsilon := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero]
      apply (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).2
      simpa [sectionSixZTwo, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hpiece.2.2
    have hproductCap :
        (primeTupleProduct
            (sectionSixFirstLowBelowPairTuple index) : Real) <=
          X ^ (1 - sectionSixThetaOne epsilon) := by
      have hraw : (sectionSixFirstPairProduct index : Real) <
          sectionSixZSix epsilon X :=
        hpiece.2.2.trans (horder.2.1.trans
          (horder.2.2.1.trans
            (horder.2.2.2.1.trans horder.2.2.2.2)))
      simpa [sectionSixFirstLowBelowPairTuple,
        sectionSixFirstLowBelowPairTupleEquiv,
        primeTupleProduct, Fin.prod_univ_two,
        sectionSixFirstPairProduct, sectionSixZSix,
        X, XNat, p, q, Nat.mul_comm] using hraw.le
    dsimp [IsPropositionSixOnePrimeTuple]
    refine ⟨?_, ?_, ?_, hproductCap, ?_⟩
    · intro i
      fin_cases i
      · simpa [sectionSixFirstLowBelowPairTuple,
          sectionSixFirstLowBelowPairTupleEquiv, q] using hqData.1
      · simpa [sectionSixFirstLowBelowPairTuple,
          sectionSixFirstLowBelowPairTupleEquiv, p] using hpData.1
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [sectionSixFirstLowBelowPairTuple,
          sectionSixFirstLowBelowPairTupleEquiv, p, q]
    · intro i
      fin_cases i
      · simpa [sectionSixFirstLowBelowPairTuple,
          sectionSixFirstLowBelowPairTupleEquiv,
          sectionSixZOne, X, XNat, q] using hqData.2.1.le
      · simpa [sectionSixFirstLowBelowPairTuple,
          sectionSixFirstLowBelowPairTupleEquiv,
          sectionSixZOne, X, XNat, p] using hpData.2.1.le
    · simpa [sectionSixFirstLowBelowPairRegion,
        sectionSixFirstLowBelowPairTuple,
        sectionSixFirstLowBelowPairTupleEquiv, XNat, p, q] using
          And.intro hqLogLower hproductUpperLog
  · intro htuple
    dsimp [IsPropositionSixOnePrimeTuple] at htuple
    rcases htuple with
      ⟨hprime, hmonotone, _hlower, _hproductCap, hregion⟩
    have hpPrime : p.Prime := by
      simpa [sectionSixFirstLowBelowPairTuple,
        sectionSixFirstLowBelowPairTupleEquiv, p] using
          hprime (1 : Fin 2)
    have hqPrime : q.Prime := by
      simpa [sectionSixFirstLowBelowPairTuple,
        sectionSixFirstLowBelowPairTupleEquiv, q] using
          hprime (0 : Fin 2)
    have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
    have hqPos : (0 : Real) < q := by exact_mod_cast hqPrime.pos
    have hpOne : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
    have hqp : q <= p := by
      simpa [sectionSixFirstLowBelowPairTuple,
        sectionSixFirstLowBelowPairTupleEquiv, p, q] using
          hmonotone (show (0 : Fin 2) <= 1 by decide)
    have hregionData :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q ∧
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q <
            sectionSixThetaOne epsilon := by
      simpa [sectionSixFirstLowBelowPairRegion,
        sectionSixFirstLowBelowPairTuple,
        sectionSixFirstLowBelowPairTupleEquiv, XNat, p, q] using hregion
    have hgapPos : 0 < sectionSixThetaGap epsilon :=
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
    have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) := by
      have hqLog := hregionData.1
      change sectionSixThetaGap epsilon < Real.logb X (q : Real) at hqLog
      exact (Real.lt_logb_iff_rpow_lt hX hqPos).1 hqLog
    have hpLower : X ^ sectionSixThetaGap epsilon < (p : Real) :=
      hqLower.trans_le (by exact_mod_cast hqp)
    have hqLogPos : 0 < normalizedPrimeLog XNat q :=
      hgapPos.trans hregionData.1
    have hpLogUpper :
        normalizedPrimeLog XNat p < sectionSixThetaOne epsilon := by
      linarith [hregionData.2, hqLogPos]
    have hpUpper : (p : Real) < X ^ sectionSixThetaOne epsilon := by
      change Real.logb X (p : Real) < sectionSixThetaOne epsilon at hpLogUpper
      exact (Real.logb_lt_iff_lt_rpow hX hpPos).1 hpLogUpper
    have hproductLower : sectionSixZOne epsilon X <
        (sectionSixFirstPairProduct index : Real) := by
      have hqLtProduct : (q : Real) < (p : Real) * (q : Real) := by
        nlinarith
      simpa [sectionSixZOne, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hqLower.trans hqLtProduct
    have hproductUpper : (sectionSixFirstPairProduct index : Real) <
        sectionSixZTwo epsilon X := by
      have hproductUpperLog := hregionData.2
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpPrime.ne_zero hqPrime.ne_zero] at hproductUpperLog
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpPrime.pos hqPrime.pos)).1
          hproductUpperLog
      simpa [sectionSixZTwo, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hqLogLe :
        normalizedPrimeLog XNat q <= normalizedPrimeLog XNat p := by
      change Real.logb X (q : Real) <= Real.logb X (p : Real)
      exact Real.logb_le_logb_of_le hX hqPos (by exact_mod_cast hqp)
    have hsquareLog :
        normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q < 1 := by
      simp only [sectionSixThetaOne] at hregionData
      linarith
    rw [sectionSixFirst_normalizedPairSquareProduct_eq
      hpPrime.ne_zero hqPrime.ne_zero] at hsquareLog
    have hcapReal : ((p * q * q : Nat) : Real) < X := by
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpPrime.pos hqPrime.pos) hqPrime.pos)).1 hsquareLog
      simpa only [Real.rpow_one, X, XNat, p, q] using hraw
    have hcapNat : p * q * q <= XNat := by
      have hcapRealLe : ((p * q * q : Nat) : Real) <= (XNat : Real) := by
        simpa only [X, XNat] using hcapReal.le
      exact_mod_cast hcapRealLe
    have hlow : index ∈ sectionSixFirstLowStrictIndices epsilon length := by
      apply mem_sectionSixFirstSecondRepeatedIndices.mpr
      constructor
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hpPrime, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, p] using hpLower
        · simpa [sectionSixZTwo, X, XNat, p] using hpUpper.le
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hqPrime, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, q] using hqLower
        · exact (sectionSixFirst_direct_pairThreshold_iff
            hpPrime hqPrime).2 ⟨hqp, by simpa only [XNat] using hcapNat⟩
    apply Finset.mem_filter.mpr
    constructor
    · simp [sectionSixFirstStrictIndices, hlow]
    · simpa [sectionSixFirstPairMem, X, XNat] using
        And.intro hlow (And.intro hproductLower hproductUpper)

/-- The pair source carrier is exactly the mapped Proposition 6.1 carrier. -/
theorem sectionSixFirstLowBelowPairIndices_map_eq_propositionSixOnePrimeTuples
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstPairPieceIndices epsilon length .lowBelow).map
        sectionSixFirstLowBelowPairTupleEquiv.toEmbedding =
      propositionSixOnePrimeTuples epsilon 2
        (sectionSixFirstLowBelowPairRegion epsilon) length := by
  classical
  ext tuple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstLowBelowPair_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro htuple
    let index : SectionSixFirstStrictIndex :=
      sectionSixFirstLowBelowPairTupleEquiv.symm tuple
    have hinverse : sectionSixFirstLowBelowPairTupleEquiv index = tuple :=
      sectionSixFirstLowBelowPairTupleEquiv.apply_symm_apply tuple
    refine ⟨index, (sectionSixFirstLowBelowPair_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    simpa only [sectionSixFirstLowBelowPairTuple, hinverse] using htuple

private theorem sectionSixFirstLowBelowPairModulus_eq_tupleModulus
    (index : SectionSixFirstStrictIndex)
    (hp : index.1.Prime) (hq : index.2.Prime) :
    sectionSixFirstPairModulus index =
      (primeTupleProduct
        (sectionSixFirstLowBelowPairTuple index)).toPNat' := by
  apply PNat.eq
  rw [sectionSixFirstPairModulus_coe hp hq, Nat.toPNat'_coe,
    if_pos]
  · simp [sectionSixFirstPairProduct,
      sectionSixFirstLowBelowPairTuple,
      sectionSixFirstLowBelowPairTupleEquiv,
      primeTupleProduct, Fin.prod_univ_two, Nat.mul_comm]
  · simp [sectionSixFirstLowBelowPairTuple,
      sectionSixFirstLowBelowPairTupleEquiv,
      primeTupleProduct, Fin.prod_univ_two, hp.pos, hq.pos]

/-- The pair base sum is exactly its fixed Proposition 6.1 sum. -/
theorem sectionSixFirstLowBelowPairBaseSum_eq_propositionSixOneSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowBelowPairBaseSum epsilon digit length =
      propositionSixOneSum epsilon 2
        (sectionSixFirstLowBelowPairRegion epsilon) digit length := by
  classical
  unfold sectionSixFirstLowBelowPairBaseSum propositionSixOneSum
  dsimp only
  rw [← sectionSixFirstLowBelowPairIndices_map_eq_propositionSixOnePrimeTuples
    epsilon hepsilon hepsilonSmall hlength]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro index hindex
  have htuple := (sectionSixFirstLowBelowPair_mem_iff
    hepsilon hepsilonSmall hlength index).1 hindex
  have hsource :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).1 htuple
  have hp : index.1.Prime := by
    simpa [sectionSixFirstLowBelowPairTuple,
      sectionSixFirstLowBelowPairTupleEquiv] using
        hsource.1 (1 : Fin 2)
  have hq : index.2.Prime := by
    simpa [sectionSixFirstLowBelowPairTuple,
      sectionSixFirstLowBelowPairTupleEquiv] using
        hsource.1 (0 : Fin 2)
  rw [sectionSixFirstLowBelowPairModulus_eq_tupleModulus index hp hq]
  rfl

end

end PrimesRestrictedDigits
