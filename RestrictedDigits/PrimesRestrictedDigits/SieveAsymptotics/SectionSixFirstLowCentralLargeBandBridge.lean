import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeLedger
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeBandPresentation
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoContract
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairCarriers
import Mathlib.Tactic.FinCases

/-!
# Low-central-large continuation-band Type-II bridge

This file reindexes the closed continuation band from the first strict low-central-large
branch by the ordered Proposition 6.2 tuple `![q, r, p]`.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--146.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

local instance sectionSixFirstLowCentralLargeBandPairMemDecidable
    (epsilon : Real) (length : Nat) (piece : SectionSixFirstPairPiece)
    (index : SectionSixFirstStrictIndex) :
    Decidable (sectionSixFirstPairMem epsilon length piece index) :=
  Classical.propDecidable _

private def sectionSixFirstLowCentralLargeBandTuple
    (index : SectionSixFirstPairContinuationIndex) : Fin 3 -> Nat :=
  ![index.1.2, index.2, index.1.1]

/-- A continuation-band index has the unique strict order `q < r < p`. -/
theorem sectionSixFirstLowCentralLargeBand_r_lt_p
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length .band) :
    index.2 < index.1.1 := by
  have hdata :=
    mem_sectionSixFirstLowCentralLargeContinuationPieceIndices.mp hindex
  have hcontinuation :=
    mem_sectionSixFirstLowCentralLargeContinuationIndices.mp hdata.1
  have hpqPiece := (Finset.mem_filter.mp hcontinuation.1).2
  let X : Real := ((10 ^ length : Nat) : Real)
  have hpqLower : sectionSixZThree epsilon X <
      (sectionSixFirstPairProduct index.1 : Real) := by
    simpa [sectionSixFirstPairMem, X] using hpqPiece.2.1
  have hqrUpper : ((index.1.2 * index.2 : Nat) : Real) <=
      sectionSixZThree epsilon X := by
    simpa [sectionSixFirstLowCentralLargeContinuationMem, X] using
      hdata.2.2
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpqPiece.1
  have hqPrime := (mem_sievePrimeInterval.mp hpqData.2).1
  have hqPos : (0 : Real) < index.1.2 := by exact_mod_cast hqPrime.pos
  have hmul : (index.1.2 : Real) * index.2 <
      (index.1.2 : Real) * index.1.1 := by
    calc
      (index.1.2 : Real) * index.2 =
          ((index.1.2 * index.2 : Nat) : Real) := by norm_num
      _ <= sectionSixZThree epsilon X := hqrUpper
      _ < (sectionSixFirstPairProduct index.1 : Real) := hpqLower
      _ = (index.1.2 : Real) * index.1.1 := by
        simp [sectionSixFirstPairProduct, mul_comm]
  exact_mod_cast (lt_of_mul_lt_mul_left hmul hqPos.le)

private theorem sectionSixFirstLowCentralLargeBand_forward
    {epsilon : Real} {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length .band) :
    sectionSixFirstLowCentralLargeBandTuple index ∈
      propositionSixTwoPrimeTuples epsilon 3
        ({0, 1} : Finset (Fin 3)) (1 : Fin 3)
        (sectionSixFirstLowCentralLargeBandRegion epsilon) length .first := by
  classical
  rw [mem_propositionSixTwoPrimeTuples_iff_source]
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
  have hbandData :=
    mem_sectionSixFirstLowCentralLargeContinuationPieceIndices.mp hindex
  have hcontinuation :=
    mem_sectionSixFirstLowCentralLargeContinuationIndices.mp hbandData.1
  have hrData := mem_sievePrimeInterval.mp hcontinuation.2
  have hpqFiltered := Finset.mem_filter.mp hcontinuation.1
  have hpiece :
      index.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
        sectionSixZThree epsilon X <
            (sectionSixFirstPairProduct index.1 : Real) ∧
          (sectionSixFirstPairProduct index.1 : Real) <
              sectionSixZFive epsilon X ∧
            sectionSixZSix epsilon X <=
              (sectionSixFirstPairSquareProduct index.1 : Real) := by
    simpa [sectionSixFirstPairMem, X, XNat] using hpqFiltered.2
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
  have hpData := mem_sievePrimeInterval.mp hpqData.1
  have hqData := mem_sievePrimeInterval.mp hpqData.2
  have hband :
      sectionSixZTwo epsilon X <= ((q * r : Nat) : Real) ∧
        ((q * r : Nat) : Real) <= sectionSixZThree epsilon X := by
    simpa [sectionSixFirstLowCentralLargeContinuationMem, X, XNat, q, r]
      using hbandData.2
  have hpPrime : p.Prime := by simpa [p] using hpData.1
  have hqPrime : q.Prime := by simpa [q] using hqData.1
  have hrPrime : r.Prime := by simpa [r] using hrData.1
  have hqr : q < r := by exact_mod_cast hrData.2.1
  have hrp : r < p := by
    simpa [p, r] using sectionSixFirstLowCentralLargeBand_r_lt_p hindex
  have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hqPrime.pos
  have hrPos : (0 : Real) < r := by exact_mod_cast hrPrime.pos
  have hprime :
      forall i, (sectionSixFirstLowCentralLargeBandTuple index i).Prime := by
    intro i
    fin_cases i
    · simpa [sectionSixFirstLowCentralLargeBandTuple, q] using hqPrime
    · simpa [sectionSixFirstLowCentralLargeBandTuple, r] using hrPrime
    · simpa [sectionSixFirstLowCentralLargeBandTuple, p] using hpPrime
  have hmono : Monotone (sectionSixFirstLowCentralLargeBandTuple index) := by
    rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i
    · simpa [sectionSixFirstLowCentralLargeBandTuple] using hqr.le
    · simpa [sectionSixFirstLowCentralLargeBandTuple] using hrp.le
  have hlower : forall i,
      X ^ sectionSixThetaGap epsilon <=
        (sectionSixFirstLowCentralLargeBandTuple index i : Real) := by
    intro i
    fin_cases i
    · simpa [sectionSixFirstLowCentralLargeBandTuple, sectionSixZOne,
        X, XNat, q] using hqData.2.1.le
    · have hqrReal : (q : Real) < r := by exact_mod_cast hqr
      have hqLower : X ^ sectionSixThetaGap epsilon <= (q : Real) := by
        simpa [sectionSixZOne, X, XNat, q] using hqData.2.1.le
      simpa [sectionSixFirstLowCentralLargeBandTuple, r] using
        hqLower.trans hqrReal.le
    · simpa [sectionSixFirstLowCentralLargeBandTuple, sectionSixZOne,
        X, XNat, p] using hpData.2.1.le
  have hselected :
      sectionSixDirectRangeMembership .first X
        (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
        (primeTupleSubproduct
          (sectionSixFirstLowCentralLargeBandTuple index)
          ({0, 1} : Finset (Fin 3)) : Real) := by
    simpa [sectionSixDirectRangeMembership,
      sectionSixFirstLowCentralLargeBandTuple, primeTupleSubproduct,
      sectionSixZTwo, sectionSixZThree, X, XNat, q, r, Nat.cast_mul]
      using hband
  have hcapNat : sectionSixFirstPairProduct index.1 * r * r <=
      10 ^ length :=
    (sectionSixFirstPair_le_terminalThreshold_iff
      hpData.1 hqData.1 hrData.1).1 hrData.2.2
  have hcap :
      primeTupleProduct (sectionSixFirstLowCentralLargeBandTuple index) *
        sectionSixFirstLowCentralLargeBandTuple index (1 : Fin 3) <=
          XNat := by
    simpa [sectionSixFirstLowCentralLargeBandTuple, primeTupleProduct,
      Fin.prod_univ_succ, sectionSixFirstPairProduct, XNat, p, q, r,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcapNat
  have hqrLog : normalizedPrimeLog XNat q <
      normalizedPrimeLog XNat r := by
    change Real.logb X (q : Real) < Real.logb X (r : Real)
    exact (Real.logb_lt_logb_iff hX hqPos hrPos).2 (by exact_mod_cast hqr)
  have hpLog : normalizedPrimeLog XNat p <=
      sectionSixThetaOne epsilon := by
    change Real.logb X (p : Real) <= sectionSixThetaOne epsilon
    apply (Real.logb_le_iff_le_rpow hX hpPos).2
    simpa [sectionSixZTwo, X, XNat, p] using hpData.2.2
  have hsquareLog : 1 - sectionSixThetaOne epsilon <=
      normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q := by
    rw [sectionSixFirst_normalizedPairSquareProduct_eq
      hpPrime.ne_zero hqPrime.ne_zero]
    apply (Real.le_logb_iff_rpow_le hX (by
      exact_mod_cast Nat.mul_pos (Nat.mul_pos hpPrime.pos hqPrime.pos)
        hqPrime.pos)).2
    simpa [sectionSixZSix, sectionSixFirstPairSquareProduct,
      X, XNat, p, q, Nat.cast_mul] using hpiece.2.2.2
  have hregion :
      (fun i => normalizedPrimeLog XNat
        (sectionSixFirstLowCentralLargeBandTuple index i)) ∈
          sectionSixFirstLowCentralLargeBandRegion epsilon := by
    simpa [sectionSixFirstLowCentralLargeBandRegion,
      sectionSixFirstLowCentralLargeBandTuple, p, q, r] using
        And.intro hqrLog (And.intro hpLog hsquareLog)
  exact ⟨hprime, hmono, hlower, hselected, hcap, hregion⟩

private theorem sectionSixFirstLowCentralLargeBand_reverse
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstPairContinuationIndex}
    (htuple : sectionSixFirstLowCentralLargeBandTuple index ∈
      propositionSixTwoPrimeTuples epsilon 3
        ({0, 1} : Finset (Fin 3)) (1 : Fin 3)
        (sectionSixFirstLowCentralLargeBandRegion epsilon) length .first) :
    index ∈ sectionSixFirstLowCentralLargeContinuationPieceIndices
      epsilon length .band := by
  classical
  rw [mem_propositionSixTwoPrimeTuples_iff_source] at htuple
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
  dsimp [IsPropositionSixTwoPrimeTuple] at htuple
  rcases htuple with ⟨hprime, hmono, hlower, hselected, hcap, hregion⟩
  have hpPrime : p.Prime := by
    simpa [sectionSixFirstLowCentralLargeBandTuple, p] using
      hprime (2 : Fin 3)
  have hqPrime : q.Prime := by
    simpa [sectionSixFirstLowCentralLargeBandTuple, q] using
      hprime (0 : Fin 3)
  have hrPrime : r.Prime := by
    simpa [sectionSixFirstLowCentralLargeBandTuple, r] using
      hprime (1 : Fin 3)
  have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hqPrime.pos
  have hrPos : (0 : Real) < r := by exact_mod_cast hrPrime.pos
  have hqrLe : q <= r := by
    simpa [sectionSixFirstLowCentralLargeBandTuple, q, r] using
      hmono (show (0 : Fin 3) <= 1 by decide)
  have hrpLe : r <= p := by
    simpa [sectionSixFirstLowCentralLargeBandTuple, p, r] using
      hmono (show (1 : Fin 3) <= 2 by decide)
  have hregionData :
      normalizedPrimeLog XNat q < normalizedPrimeLog XNat r ∧
        normalizedPrimeLog XNat p <= sectionSixThetaOne epsilon ∧
          1 - sectionSixThetaOne epsilon <=
            normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q := by
    simpa [sectionSixFirstLowCentralLargeBandRegion,
      sectionSixFirstLowCentralLargeBandTuple, XNat, p, q, r] using hregion
  have hqr : q < r := by
    have hlog := hregionData.1
    change Real.logb X (q : Real) < Real.logb X (r : Real) at hlog
    exact_mod_cast (Real.logb_lt_logb_iff hX hqPos hrPos).1 hlog
  have hgapHalf :
      sectionSixThetaGap epsilon <
        1 / 2 - sectionSixThetaOne epsilon := by
    rw [sectionSixThetaGap_eq]
    simp only [sectionSixThetaOne]
    linarith
  have hqLogLower : sectionSixThetaGap epsilon <
      normalizedPrimeLog XNat q := by
    linarith [hregionData.2.1, hregionData.2.2]
  have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) := by
    apply (Real.lt_logb_iff_rpow_lt hX hqPos).1
    simpa only [X, XNat, normalizedPrimeLog, Real.logb] using hqLogLower
  have hpLower : X ^ sectionSixThetaGap epsilon < (p : Real) := by
    have hqpReal : (q : Real) <= p := by
      exact_mod_cast hqrLe.trans hrpLe
    exact hqLower.trans_le hqpReal
  have hpUpper : (p : Real) <= X ^ sectionSixThetaOne epsilon := by
    apply (Real.logb_le_iff_le_rpow hX hpPos).1
    simpa only [X, XNat, normalizedPrimeLog, Real.logb] using
      hregionData.2.1
  have hselectedData :
      X ^ sectionSixThetaOne epsilon <= ((q * r : Nat) : Real) ∧
        ((q * r : Nat) : Real) <= X ^ sectionSixThetaTwo epsilon := by
    simpa [sectionSixDirectRangeMembership,
      sectionSixFirstLowCentralLargeBandTuple, primeTupleSubproduct,
      X, XNat, q, r, Nat.cast_mul] using hselected
  have hqrLogUpper : normalizedPrimeLog XNat q +
      normalizedPrimeLog XNat r <= sectionSixThetaTwo epsilon := by
    rw [sectionSixFirst_normalizedPairProduct_eq
      hrPrime.ne_zero hqPrime.ne_zero]
    apply (Real.logb_le_iff_le_rpow hX (by
      exact_mod_cast Nat.mul_pos hrPrime.pos hqPrime.pos)).2
    simpa [X, XNat, q, r, Nat.cast_mul, mul_comm] using hselectedData.2
  have hqLogUpper : normalizedPrimeLog XNat q <
      sectionSixThetaTwo epsilon / 2 := by
    linarith [hregionData.1, hqrLogUpper]
  have hmargin : 0 < 1 - sectionSixThetaOne epsilon -
      3 * sectionSixThetaTwo epsilon / 2 := by
    simp only [sectionSixThetaOne, sectionSixThetaTwo]
    linarith
  have hpqLogLower : sectionSixThetaTwo epsilon <
      normalizedPrimeLog XNat p + normalizedPrimeLog XNat q := by
    linarith [hregionData.2.2, hqLogUpper, hmargin]
  have hpqLogUpper : normalizedPrimeLog XNat p +
      normalizedPrimeLog XNat q < 1 - sectionSixThetaTwo epsilon := by
    linarith [hregionData.2.1, hqLogUpper, hmargin]
  have hpqLower : sectionSixZThree epsilon X <
      ((p * q : Nat) : Real) := by
    rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
      hpPrime.ne_zero hqPrime.ne_zero] at hpqLogLower
    have hreal := (Real.lt_logb_iff_rpow_lt hX (by
      exact_mod_cast Nat.mul_pos hpPrime.pos hqPrime.pos)).1 hpqLogLower
    simpa [sectionSixZThree, X, XNat, p, q, Nat.cast_mul] using hreal
  have hpqUpper : ((p * q : Nat) : Real) <
      sectionSixZFive epsilon X := by
    rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
      hpPrime.ne_zero hqPrime.ne_zero] at hpqLogUpper
    have hreal := (Real.logb_lt_iff_lt_rpow hX (by
      exact_mod_cast Nat.mul_pos hpPrime.pos hqPrime.pos)).1 hpqLogUpper
    simpa [sectionSixZFive, X, XNat, p, q, Nat.cast_mul] using hreal
  have hsquareLower : sectionSixZSix epsilon X <=
      ((p * q * q : Nat) : Real) := by
    have hsquareLog := hregionData.2.2
    rw [sectionSixFirst_normalizedPairSquareProduct_eq
      hpPrime.ne_zero hqPrime.ne_zero] at hsquareLog
    have hreal := (Real.le_logb_iff_rpow_le hX (by
      exact_mod_cast Nat.mul_pos (Nat.mul_pos hpPrime.pos hqPrime.pos)
        hqPrime.pos)).1 hsquareLog
    simpa [sectionSixZSix, X, XNat, p, q, Nat.cast_mul] using hreal
  have hfullCap : p * q * r * r <= XNat := by
    simpa [sectionSixFirstLowCentralLargeBandTuple, primeTupleProduct,
      Fin.prod_univ_succ, XNat, p, q, r, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using hcap
  have hpairCap : p * q * q <= XNat := by
    have hfirst : (p * q) * q <= (p * q) * r :=
      Nat.mul_le_mul_left (p * q) hqrLe
    have hsecond : (p * q) * r <= (p * q) * r * r := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (p * q * r) hrPrime.one_le
    exact (hfirst.trans hsecond).trans hfullCap
  have hlow : index.1 ∈
      sectionSixFirstLowStrictIndices epsilon length := by
    apply mem_sectionSixFirstSecondRepeatedIndices.mpr
    constructor
    · apply mem_sievePrimeInterval.mpr
      refine ⟨hpPrime, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, p] using hpLower
      · simpa [sectionSixZTwo, X, XNat, p] using hpUpper
    · apply mem_sievePrimeInterval.mpr
      refine ⟨hqPrime, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, q] using hqLower
      · exact (sectionSixFirst_direct_pairThreshold_iff hpPrime hqPrime).2
          ⟨hqrLe.trans hrpLe, by simpa [XNat] using hpairCap⟩
  have hpqPiece : index.1 ∈
      sectionSixFirstPairPieceIndices epsilon length .lowCentralLarge := by
    apply Finset.mem_filter.mpr
    constructor
    · simp [sectionSixFirstStrictIndices, hlow]
    · simpa [sectionSixFirstPairMem, sectionSixFirstPairProduct,
        sectionSixFirstPairSquareProduct, X, XNat, p, q] using
        And.intro hlow
          (And.intro hpqLower (And.intro hpqUpper hsquareLower))
  have hterminal : (r : Real) <=
      sectionSixFirstPairTerminalThreshold length index.1 := by
    apply (sectionSixFirstPair_le_terminalThreshold_iff
      hpPrime hqPrime hrPrime).2
    simpa [sectionSixFirstPairProduct, XNat, p, q, r, Nat.mul_assoc]
      using hfullCap
  have hcontinuation : index ∈
      sectionSixFirstLowCentralLargeContinuationIndices epsilon length := by
    apply mem_sectionSixFirstLowCentralLargeContinuationIndices.mpr
    refine ⟨hpqPiece, ?_⟩
    apply mem_sievePrimeInterval.mpr
    exact ⟨hrPrime, by exact_mod_cast hqr, hterminal⟩
  apply mem_sectionSixFirstLowCentralLargeContinuationPieceIndices.mpr
  refine ⟨hcontinuation, ?_⟩
  simpa [sectionSixFirstLowCentralLargeContinuationMem,
    sectionSixZTwo, sectionSixZThree, X, XNat, q, r, Nat.cast_mul]
    using hselectedData

private theorem sectionSixFirstLowCentralLargeBand_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstPairContinuationIndex) :
    index ∈ sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length .band <->
      sectionSixFirstLowCentralLargeBandTuple index ∈
        propositionSixTwoPrimeTuples epsilon 3
          ({0, 1} : Finset (Fin 3)) (1 : Fin 3)
          (sectionSixFirstLowCentralLargeBandRegion epsilon) length .first := by
  constructor
  · exact sectionSixFirstLowCentralLargeBand_forward hlength
  · exact sectionSixFirstLowCentralLargeBand_reverse hepsilon hlength

private theorem sectionSixFirstLowCentralLargeBand_term_eq_tupleTerm
    (digit : Fin 10) (length : Nat)
    (index : SectionSixFirstPairContinuationIndex)
    (hp : index.1.1.Prime) (hq : index.1.2.Prime)
    (hr : index.2.Prime) :
    sectionSixStrictPrimeTerm digit length
        (sectionSixFirstPairModulus index.1) index.2 =
      sectionSixSiftedSum digit length
        (primeTupleProduct
          (sectionSixFirstLowCentralLargeBandTuple index)).toPNat'
        (sectionSixFirstLowCentralLargeBandTuple index (1 : Fin 3) : Real) := by
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (sectionSixFirstPairModulus index.1) hr]
  congr 1
  apply PNat.eq
  simp [sectionSixFirstPairModulus,
    sectionSixFirstLowCentralLargeBandTuple, primeTupleProduct,
    Fin.prod_univ_succ, PNat.mul_coe, Nat.toPNat'_coe,
    hp.pos, hq.pos, hr.pos, Nat.mul_comm, Nat.mul_left_comm]

/-- The closed continuation band is exactly one Proposition 6.2 band sum. -/
theorem sectionSixFirstLowCentralLargeBand_eq_propositionSixTwoBandSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowCentralLargeStrictPieceSum
        epsilon digit length .band =
      propositionSixTwoBandSum epsilon 3
        ({0, 1} : Finset (Fin 3)) (1 : Fin 3)
        (sectionSixFirstLowCentralLargeBandRegion epsilon)
        digit length .first := by
  classical
  unfold sectionSixFirstLowCentralLargeStrictPieceSum
    propositionSixTwoBandSum
  apply Finset.sum_bij
    (fun index _ => sectionSixFirstLowCentralLargeBandTuple index)
  · intro index hindex
    exact (sectionSixFirstLowCentralLargeBand_mem_iff
      hepsilon hlength index).1 hindex
  · intro left hleft right hright heq
    rcases left with ⟨⟨p, q⟩, r⟩
    rcases right with ⟨⟨p', q'⟩, r'⟩
    have hp : p = p' := by
      simpa [sectionSixFirstLowCentralLargeBandTuple] using
        congrFun heq (2 : Fin 3)
    have hq : q = q' := by
      simpa [sectionSixFirstLowCentralLargeBandTuple] using
        congrFun heq (0 : Fin 3)
    have hr : r = r' := by
      simpa [sectionSixFirstLowCentralLargeBandTuple] using
        congrFun heq (1 : Fin 3)
    subst p'
    subst q'
    subst r'
    rfl
  · intro tuple htuple
    let index : SectionSixFirstPairContinuationIndex :=
      ⟨⟨tuple 2, tuple 0⟩, tuple 1⟩
    have hinverse : sectionSixFirstLowCentralLargeBandTuple index = tuple := by
      funext i
      fin_cases i <;> rfl
    refine ⟨index, (sectionSixFirstLowCentralLargeBand_mem_iff
      hepsilon hlength index).2 ?_, hinverse⟩
    rw [hinverse]
    exact htuple
  · intro index hindex
    have htuple := (sectionSixFirstLowCentralLargeBand_mem_iff
      hepsilon hlength index).1 hindex
    have hsource := mem_propositionSixTwoPrimeTuples_iff_source.mp htuple
    dsimp [IsPropositionSixTwoPrimeTuple] at hsource
    exact sectionSixFirstLowCentralLargeBand_term_eq_tupleTerm
      digit length index
      (by simpa [sectionSixFirstLowCentralLargeBandTuple] using
        hsource.1 (2 : Fin 3))
      (by simpa [sectionSixFirstLowCentralLargeBandTuple] using
        hsource.1 (0 : Fin 3))
      (by simpa [sectionSixFirstLowCentralLargeBandTuple] using
        hsource.1 (1 : Fin 3))

end

end PrimesRestrictedDigits
