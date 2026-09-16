import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallQuadrupleBandCells
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallTripleBaseBridge
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Low central-small quadruple-band inclusion-exclusion

The five closed pair-band events overlap. Their nonempty intersections are Proposition 6.2
cells, so exact signed inclusion-exclusion applies. Source: `MAYNARD-PRD-PUBLISHED`,
Proposition 6.2, pp. 137--138, and Eq. (6.12), p. 143.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def main005VBandTupleEquiv :
    SectionSixFirstLowCentralSmallQuadrupleIndex ≃ (Fin 4 -> Nat) where
  toFun index := ![index.2, index.1.2, index.1.1.2, index.1.1.1]
  invFun tuple := ⟨⟨⟨tuple 3, tuple 2⟩, tuple 1⟩, tuple 0⟩
  left_inv index := by rcases index with ⟨⟨⟨p, q⟩, r⟩, s⟩; rfl
  right_inv tuple := by funext i; fin_cases i <;> rfl

private abbrev main005VBandTuple (index : SectionSixFirstLowCentralSmallQuadrupleIndex) :
    Fin 4 -> Nat := main005VBandTupleEquiv index

private def main005VOutsideFirstBand (epsilon : Real) (length a b : Nat) : Prop :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ((a * b : Nat) : Real) < sectionSixZTwo epsilon X \/
    sectionSixZThree epsilon X < ((a * b : Nat) : Real)

private def main005VBandEventMem (epsilon : Real) (length : Nat) (event : Fin 5)
    (index : SectionSixFirstLowCentralSmallQuadrupleIndex) : Prop :=
  ![
    ¬ main005VOutsideFirstBand epsilon length index.1.1.1 index.1.2,
    ¬ main005VOutsideFirstBand epsilon length index.1.1.1 index.2,
    ¬ main005VOutsideFirstBand epsilon length index.1.1.2 index.1.2,
    ¬ main005VOutsideFirstBand epsilon length index.1.1.2 index.2,
    ¬ main005VOutsideFirstBand epsilon length index.1.2 index.2] event

local instance main005VBandEventMemDecidable (epsilon : Real) (length : Nat)
    (event : Fin 5) (index : SectionSixFirstLowCentralSmallQuadrupleIndex) :
    Decidable (main005VBandEventMem epsilon length event index) := Classical.propDecidable _

private noncomputable def main005VBandEventIndices (epsilon : Real) (length : Nat)
    (event : Fin 5) : Finset SectionSixFirstLowCentralSmallQuadrupleIndex :=
  (sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length).filter
    (main005VBandEventMem epsilon length event)

private noncomputable def main005VBandCellIndices (epsilon : Real) (length : Nat)
    (cell : Finset (Fin 5)) (hcell : cell.Nonempty) : Finset
      SectionSixFirstLowCentralSmallQuadrupleIndex :=
  cell.inf' hcell (main005VBandEventIndices epsilon length)

private theorem main005VBandEventMem_iff_selectedRange (epsilon : Real) (length : Nat)
    (event : Fin 5) (index : SectionSixFirstLowCentralSmallQuadrupleIndex) :
    main005VBandEventMem epsilon length event index <->
      sectionSixDirectRangeMembership .first ((10 ^ length : Nat) : Real)
        (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
        (primeTupleSubproduct (main005VBandTuple index)
          (sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event) : Real) := by
  fin_cases event <;>
    simp [main005VBandEventMem, main005VOutsideFirstBand,
      main005VBandTuple, main005VBandTupleEquiv,
      sectionSixFirstLowCentralSmallQuadrupleBandPairPositions,
      sectionSixDirectRangeMembership, primeTupleSubproduct,
      sectionSixZTwo, sectionSixZThree, Nat.cast_mul, mul_comm]

private theorem main005V_selectedRange_iff_logBand {epsilon : Real} {length : Nat}
    (hlength : 1 <= length) (tuple : Fin 4 -> Nat)
    (hprime : forall i, (tuple i).Prime) (event : Fin 5) :
    sectionSixDirectRangeMembership .first ((10 ^ length : Nat) : Real)
        (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
        (primeTupleSubproduct tuple
          (sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event) : Real) <->
      sectionSixThetaOne epsilon <= ∑ i ∈
          sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event,
          normalizedPrimeLog (10 ^ length) (tuple i) /\
        (∑ i ∈ sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event,
          normalizedPrimeLog (10 ^ length) (tuple i)) <= sectionSixThetaTwo epsilon := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hXNat : 1 < XNat := by simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by dsimp only [X]; exact_mod_cast hXNat
  have hsubNatPos : 0 < primeTupleSubproduct tuple
      (sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event) :=
    Finset.prod_pos fun i _hi => (hprime i).pos
  have hsubPos : (0 : Real) < primeTupleSubproduct tuple
      (sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event) := by exact_mod_cast hsubNatPos
  rw [sum_normalizedPrimeLog_finset_eq_subproduct tuple _ fun i => (hprime i).ne_zero]
  change (X ^ sectionSixThetaOne epsilon <= _ /\ _ <= X ^ sectionSixThetaTwo epsilon) <->
    sectionSixThetaOne epsilon <= Real.logb X _ /\ Real.logb X _ <= sectionSixThetaTwo epsilon
  exact and_congr (Real.le_logb_iff_rpow_le hX hsubPos).symm
    (Real.logb_le_iff_le_rpow hX hsubPos).symm

private theorem main005V_pLog_lt_thetaOne {epsilon : Real} (hepsilon : 0 < epsilon)
    (event : Fin 5) (x : Fin 4 -> Real) (h01 : x 0 <= x 1)
    (h12 : x 1 <= x 2) (_h23 : x 2 <= x 3)
    (hgap : sectionSixThetaGap epsilon < x 0)
    (hsquare : x 3 + 2 * x 2 < 1 - sectionSixThetaOne epsilon)
    (hband : sectionSixThetaOne epsilon <= ∑ i ∈
        sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event, x i /\
      (∑ i ∈ sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event, x i) <=
        sectionSixThetaTwo epsilon) : x 3 < sectionSixThetaOne epsilon := by
  fin_cases event <;>
    simp [sectionSixFirstLowCentralSmallQuadrupleBandPairPositions] at hband <;>
    simp only [sectionSixThetaGap, sectionSixThetaOne,
      sectionSixThetaTwo] at * <;>
    linarith

private theorem main005V_tripleTuple_product_eq
    (index : SectionSixFirstLowCentralSmallTripleIndex) :
    primeTupleProduct (sectionSixFirstLowCentralSmallTripleTupleEquiv index) =
      sectionSixFirstLowCentralSmallTripleProduct index := by
  simp [sectionSixFirstLowCentralSmallTripleTupleEquiv,
    primeTupleProduct, Fin.prod_univ_succ, sectionSixFirstLowCentralSmallTripleProduct,
    sectionSixFirstPairProduct, Nat.mul_comm, Nat.mul_left_comm]

private theorem main005VBandCell_forward
    {epsilon : Real} (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (cell : Finset (Fin 5)) (hcell : cell.Nonempty)
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex}
    (hindex : index ∈ main005VBandCellIndices epsilon length cell hcell) :
    main005VBandTuple index ∈ propositionSixTwoPrimeTuples epsilon 4
      (sectionSixFirstLowCentralSmallQuadrupleBandPairPositions (cell.min' hcell))
      (0 : Fin 4) (sectionSixFirstLowCentralSmallQuadrupleBandCellRegion epsilon cell hcell)
      length .first := by
  classical
  rw [mem_propositionSixTwoPrimeTuples_iff_source]
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hevents : ∀ event ∈ cell, index ∈ main005VBandEventIndices epsilon length event :=
    (Finset.mem_inf' hcell).1 hindex
  have hselectedIndex := hevents (cell.min' hcell) (cell.min'_mem hcell)
  rw [main005VBandEventIndices] at hselectedIndex
  have hselectedData := Finset.mem_filter.mp hselectedIndex
  have hraw := mem_sectionSixFirstLowCentralSmallRawQuadrupleIndices.mp hselectedData.1
  have hsData := mem_sievePrimeInterval.mp hraw.2
  rw [sectionSixFirstLowCentralSmallTripleReducedThreshold, le_min_iff] at hsData
  have htripleMapped :
      sectionSixFirstLowCentralSmallTripleTupleEquiv index.1 ∈
        (sectionSixFirstLowCentralSmallTripleIndices epsilon length).map
          sectionSixFirstLowCentralSmallTripleTupleEquiv.toEmbedding :=
    Finset.mem_map.mpr ⟨index.1, hraw.1, rfl⟩
  have htripleTuple :
      sectionSixFirstLowCentralSmallTripleTupleEquiv index.1 ∈
        propositionSixOnePrimeTuples epsilon 3
          (sectionSixFirstLowCentralSmallTripleRegion epsilon) length := by
    rw [← sectionSixFirstLowCentralSmallTripleIndices_map_eq_propositionSixOnePrimeTuples
      epsilon hepsilon hepsilonSmall hlength]
    exact htripleMapped
  have htripleSource :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).1 htripleTuple
  dsimp [IsPropositionSixOnePrimeTuple] at htripleSource
  rcases htripleSource with
    ⟨htriplePrime, htripleMono, htripleLower, _htripleCap, htripleRegion⟩
  have hquadPrime : ∀ i, (main005VBandTuple index i).Prime := by
    intro i
    fin_cases i
    · simpa [main005VBandTuple, main005VBandTupleEquiv] using hsData.1
    · simpa [main005VBandTuple, main005VBandTupleEquiv,
        sectionSixFirstLowCentralSmallTripleTupleEquiv] using htriplePrime 0
    · simpa [main005VBandTuple, main005VBandTupleEquiv,
        sectionSixFirstLowCentralSmallTripleTupleEquiv] using htriplePrime 1
    · simpa [main005VBandTuple, main005VBandTupleEquiv,
        sectionSixFirstLowCentralSmallTripleTupleEquiv] using htriplePrime 2
  have hsLog : sectionSixThetaGap epsilon < normalizedPrimeLog XNat index.2 := by
    have hXNat : 1 < XNat := by
      simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
    have hX : (1 : Real) < X := by dsimp only [X]; exact_mod_cast hXNat
    change sectionSixThetaGap epsilon < Real.logb X (index.2 : Real)
    apply (Real.lt_logb_iff_rpow_lt hX (by exact_mod_cast hsData.1.pos)).2
    simpa [sectionSixZOne, X, XNat] using hsData.2.1
  have hfullCap := (sectionSixFirstLowCentralSmall_le_tripleTerminalThreshold_iff
    (htriplePrime 2) (htriplePrime 1) (htriplePrime 0) hsData.1).1 hsData.2.2.2
  dsimp [IsPropositionSixTwoPrimeTuple]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hquadPrime
  · rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i
    · simpa [main005VBandTuple, main005VBandTupleEquiv] using hsData.2.2.1
    · simpa [main005VBandTuple, main005VBandTupleEquiv,
        sectionSixFirstLowCentralSmallTripleTupleEquiv] using htripleMono (show (0 : Fin 3) <= 1 by decide)
    · simpa [main005VBandTuple, main005VBandTupleEquiv,
        sectionSixFirstLowCentralSmallTripleTupleEquiv] using htripleMono (show (1 : Fin 3) <= 2 by decide)
  · intro i
    fin_cases i
    · simpa [main005VBandTuple, main005VBandTupleEquiv,
        sectionSixZOne, X, XNat] using hsData.2.1.le
    · simpa [main005VBandTuple, main005VBandTupleEquiv,
        sectionSixFirstLowCentralSmallTripleTupleEquiv] using htripleLower 0
    · simpa [main005VBandTuple, main005VBandTupleEquiv,
        sectionSixFirstLowCentralSmallTripleTupleEquiv] using htripleLower 1
    · simpa [main005VBandTuple, main005VBandTupleEquiv,
        sectionSixFirstLowCentralSmallTripleTupleEquiv] using htripleLower 2
  · exact (main005VBandEventMem_iff_selectedRange epsilon length _ index).1
      hselectedData.2
  · simpa [main005VBandTuple, main005VBandTupleEquiv,
      primeTupleProduct, Fin.prod_univ_succ,
      sectionSixFirstLowCentralSmallTripleProduct,
      sectionSixFirstPairProduct, XNat, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hfullCap
  · have htripleRegionData := htripleRegion
    simp [sectionSixFirstLowCentralSmallTripleRegion,
      sectionSixFirstLowCentralSmallTripleTupleEquiv] at htripleRegionData
    refine ⟨hsLog, htripleRegionData.2.1, htripleRegionData.2.2.1, ?_⟩
    intro event hevent
    have heventIndex := hevents event (Finset.mem_of_mem_erase hevent)
    rw [main005VBandEventIndices] at heventIndex
    have heventMem := (Finset.mem_filter.mp heventIndex).2
    exact (main005V_selectedRange_iff_logBand hlength (main005VBandTuple index)
      hquadPrime event).1 ((main005VBandEventMem_iff_selectedRange epsilon length
        event index).1 heventMem)

private theorem main005VBandCell_reverse
    {epsilon : Real} (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (cell : Finset (Fin 5)) (hcell : cell.Nonempty)
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex}
    (htuple : main005VBandTuple index ∈ propositionSixTwoPrimeTuples epsilon 4
      (sectionSixFirstLowCentralSmallQuadrupleBandPairPositions (cell.min' hcell))
      (0 : Fin 4) (sectionSixFirstLowCentralSmallQuadrupleBandCellRegion epsilon cell hcell)
      length .first) :
    index ∈ main005VBandCellIndices epsilon length cell hcell := by
  classical
  rw [mem_propositionSixTwoPrimeTuples_iff_source] at htuple
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hXNat : 1 < XNat := by simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by dsimp only [X]; exact_mod_cast hXNat
  dsimp [IsPropositionSixTwoPrimeTuple] at htuple
  rcases htuple with ⟨hprime, hmono, hlower, hselected, hcap, hregion⟩
  have hsPrime : index.2.Prime := by simpa [main005VBandTuple, main005VBandTupleEquiv] using hprime 0
  have hrPrime : index.1.2.Prime := by simpa [main005VBandTuple, main005VBandTupleEquiv] using hprime 1
  have hqPrime : index.1.1.2.Prime := by simpa [main005VBandTuple, main005VBandTupleEquiv] using hprime 2
  have hpPrime : index.1.1.1.Prime := by simpa [main005VBandTuple, main005VBandTupleEquiv] using hprime 3
  have hsr : index.2 <= index.1.2 := by
    simpa [main005VBandTuple, main005VBandTupleEquiv] using
      hmono (show (0 : Fin 4) <= 1 by decide)
  have hrq : index.1.2 <= index.1.1.2 := by
    simpa [main005VBandTuple, main005VBandTupleEquiv] using
      hmono (show (1 : Fin 4) <= 2 by decide)
  have hqp : index.1.1.2 <= index.1.1.1 := by
    simpa [main005VBandTuple, main005VBandTupleEquiv] using
      hmono (show (2 : Fin 4) <= 3 by decide)
  have hregionData := hregion
  simp [sectionSixFirstLowCentralSmallQuadrupleBandCellRegion,
    main005VBandTuple, main005VBandTupleEquiv] at hregionData
  have hselectedLog := (main005V_selectedRange_iff_logBand hlength
    (main005VBandTuple index) hprime (cell.min' hcell)).1 hselected
  have hsrLog : normalizedPrimeLog XNat index.2 <=
      normalizedPrimeLog XNat index.1.2 := by
    change Real.logb X (index.2 : Real) <= Real.logb X (index.1.2 : Real)
    exact Real.logb_le_logb_of_le hX (by exact_mod_cast hsPrime.pos) (by exact_mod_cast hsr)
  have hrqLog : normalizedPrimeLog XNat index.1.2 <=
      normalizedPrimeLog XNat index.1.1.2 := by
    change Real.logb X (index.1.2 : Real) <= Real.logb X (index.1.1.2 : Real)
    exact Real.logb_le_logb_of_le hX (by exact_mod_cast hrPrime.pos) (by exact_mod_cast hrq)
  have hqpLog : normalizedPrimeLog XNat index.1.1.2 <=
      normalizedPrimeLog XNat index.1.1.1 := by
    change Real.logb X (index.1.1.2 : Real) <= Real.logb X (index.1.1.1 : Real)
    exact Real.logb_le_logb_of_le hX (by exact_mod_cast hqPrime.pos) (by exact_mod_cast hqp)
  have hpLog : normalizedPrimeLog XNat index.1.1.1 < sectionSixThetaOne epsilon :=
    main005V_pLog_lt_thetaOne hepsilon (cell.min' hcell)
      (fun i => normalizedPrimeLog XNat (main005VBandTuple index i))
      (by simpa [main005VBandTuple, main005VBandTupleEquiv] using hsrLog)
      (by simpa [main005VBandTuple, main005VBandTupleEquiv] using hrqLog)
      (by simpa [main005VBandTuple, main005VBandTupleEquiv] using hqpLog)
      (by simpa [main005VBandTuple, main005VBandTupleEquiv] using hregionData.1)
      (by simpa [main005VBandTuple, main005VBandTupleEquiv] using hregionData.2.2.1)
      hselectedLog
  have hrLog : sectionSixThetaGap epsilon <
      normalizedPrimeLog XNat index.1.2 := hregionData.1.trans_le hsrLog
  have hsquareReal : (sectionSixFirstPairSquareProduct index.1.1 : Real) <
      X ^ (1 - sectionSixThetaOne epsilon) := by
    have hsquareLog := hregionData.2.2.1
    rw [sectionSixFirst_normalizedPairSquareProduct_eq hpPrime.ne_zero hqPrime.ne_zero]
      at hsquareLog
    exact (Real.logb_lt_iff_lt_rpow hX (by
      exact_mod_cast Nat.mul_pos
        (Nat.mul_pos hpPrime.pos hqPrime.pos) hqPrime.pos)).1 hsquareLog
  have htripleProductLe : sectionSixFirstLowCentralSmallTripleProduct index.1 <=
      sectionSixFirstPairSquareProduct index.1.1 := Nat.mul_le_mul_left _ hrq
  have htripleProductCap :
      (primeTupleProduct (sectionSixFirstLowCentralSmallTripleTupleEquiv index.1) : Real) <=
        X ^ (1 - sectionSixThetaOne epsilon) := by
    rw [main005V_tripleTuple_product_eq]
    exact (by exact_mod_cast htripleProductLe : (sectionSixFirstLowCentralSmallTripleProduct
      index.1 : Real) <= sectionSixFirstPairSquareProduct index.1.1) |>.trans hsquareReal.le
  have htripleSource : IsPropositionSixOnePrimeTuple epsilon length
      (sectionSixFirstLowCentralSmallTripleRegion epsilon)
      (sectionSixFirstLowCentralSmallTripleTupleEquiv index.1) := by
    dsimp [IsPropositionSixOnePrimeTuple]
    refine ⟨?_, ?_, ?_, htripleProductCap, ?_⟩
    · intro i; fin_cases i <;> simp_all [sectionSixFirstLowCentralSmallTripleTupleEquiv]
    · rw [Fin.monotone_iff_le_succ]
      intro i
      fin_cases i
      · simpa [sectionSixFirstLowCentralSmallTripleTupleEquiv] using hrq
      · simpa [sectionSixFirstLowCentralSmallTripleTupleEquiv] using hqp
    · intro i
      fin_cases i
      · simpa [sectionSixFirstLowCentralSmallTripleTupleEquiv,
          main005VBandTuple, main005VBandTupleEquiv] using hlower (1 : Fin 4)
      · simpa [sectionSixFirstLowCentralSmallTripleTupleEquiv,
          main005VBandTuple, main005VBandTupleEquiv] using hlower (2 : Fin 4)
      · simpa [sectionSixFirstLowCentralSmallTripleTupleEquiv,
          main005VBandTuple, main005VBandTupleEquiv] using hlower (3 : Fin 4)
    · simpa [sectionSixFirstLowCentralSmallTripleRegion,
        sectionSixFirstLowCentralSmallTripleTupleEquiv] using
          ⟨hpLog.le, hregionData.2.1, hregionData.2.2.1, hrLog⟩
  have htripleTuple :
      sectionSixFirstLowCentralSmallTripleTupleEquiv index.1 ∈
        propositionSixOnePrimeTuples epsilon 3
          (sectionSixFirstLowCentralSmallTripleRegion epsilon) length :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).2 htripleSource
  have htripleMapped :
      sectionSixFirstLowCentralSmallTripleTupleEquiv index.1 ∈
        (sectionSixFirstLowCentralSmallTripleIndices epsilon length).map
          sectionSixFirstLowCentralSmallTripleTupleEquiv.toEmbedding := by
    rw [sectionSixFirstLowCentralSmallTripleIndices_map_eq_propositionSixOnePrimeTuples
      epsilon hepsilon hepsilonSmall hlength]
    exact htripleTuple
  have htriple : index.1 ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length := by
    simpa using htripleMapped
  have hsLower : X ^ sectionSixThetaGap epsilon < (index.2 : Real) := by
    have hsLog := hregionData.1
    change sectionSixThetaGap epsilon < Real.logb X (index.2 : Real) at hsLog
    exact (Real.lt_logb_iff_rpow_lt hX (by exact_mod_cast hsPrime.pos)).1 hsLog
  have hfullCap :
      sectionSixFirstLowCentralSmallTripleProduct index.1 * index.2 * index.2 <=
        XNat := by
    simpa [main005VBandTuple, main005VBandTupleEquiv,
      primeTupleProduct, Fin.prod_univ_succ,
      sectionSixFirstLowCentralSmallTripleProduct,
      sectionSixFirstPairProduct, XNat, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hcap
  have hraw : index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length := by
    apply mem_sectionSixFirstLowCentralSmallRawQuadrupleIndices.mpr
    refine ⟨htriple, mem_sievePrimeInterval.mpr ⟨hsPrime, ?_, ?_⟩⟩
    · simpa [sectionSixZOne, X, XNat] using hsLower
    · unfold sectionSixFirstLowCentralSmallTripleReducedThreshold
      rw [le_min_iff]
      refine ⟨by exact_mod_cast hsr, ?_⟩
      exact (sectionSixFirstLowCentralSmall_le_tripleTerminalThreshold_iff hpPrime hqPrime
        hrPrime hsPrime).2 hfullCap
  apply (Finset.mem_inf' hcell).2
  intro event hevent
  rw [main005VBandEventIndices]
  apply Finset.mem_filter.mpr
  refine ⟨hraw, ?_⟩
  apply (main005VBandEventMem_iff_selectedRange epsilon length event index).2
  by_cases hselectedEvent : event = cell.min' hcell
  · simpa [hselectedEvent] using hselected
  · apply (main005V_selectedRange_iff_logBand hlength (main005VBandTuple index)
      hprime event).2
    exact hregionData.2.2.2 event hselectedEvent hevent

private theorem main005VBandCellIndices_map_eq
    (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (cell : Finset (Fin 5)) (hcell : cell.Nonempty) :
    (main005VBandCellIndices epsilon length cell hcell).map
        main005VBandTupleEquiv.toEmbedding =
      propositionSixTwoPrimeTuples epsilon 4
        (sectionSixFirstLowCentralSmallQuadrupleBandPairPositions (cell.min' hcell))
        (0 : Fin 4) (sectionSixFirstLowCentralSmallQuadrupleBandCellRegion epsilon cell hcell)
        length .first := by
  classical
  ext tuple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact main005VBandCell_forward hepsilon hepsilonSmall hlength cell hcell hindex
  · intro htuple
    let index := main005VBandTupleEquiv.symm tuple
    have hinverse : main005VBandTuple index = tuple :=
      main005VBandTupleEquiv.apply_symm_apply tuple
    refine ⟨index, main005VBandCell_reverse hepsilon hepsilonSmall hlength cell hcell ?_, hinverse⟩
    simpa only [hinverse] using htuple

private theorem main005VBand_term_eq_tupleTerm (digit : Fin 10) (length : Nat)
    (index : SectionSixFirstLowCentralSmallQuadrupleIndex)
    (hp : index.1.1.1.Prime) (hq : index.1.1.2.Prime)
    (hr : index.1.2.Prime) (hs : index.2.Prime) :
    sectionSixStrictPrimeTerm digit length (sectionSixFirstLowCentralSmallTripleModulus
      index.1) index.2 = sectionSixSiftedSum digit length
        (primeTupleProduct (main005VBandTuple index)).toPNat'
        (main005VBandTuple index (0 : Fin 4) : Real) := by
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (sectionSixFirstLowCentralSmallTripleModulus index.1) hs]
  congr 1
  apply PNat.eq
  simp [sectionSixFirstLowCentralSmallTripleModulus_coe hp hq hr,
    sectionSixFirstLowCentralSmallTripleProduct, sectionSixFirstPairProduct,
    main005VBandTuple, main005VBandTupleEquiv, primeTupleProduct,
    Fin.prod_univ_succ, PNat.mul_coe, Nat.toPNat'_coe,
    hp.pos, hq.pos, hr.pos, hs.pos, Nat.mul_comm, Nat.mul_left_comm]

private theorem main005VBandCellSum_eq
    {epsilon : Real} (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    (cell : Finset (Fin 5)) (hcell : cell.Nonempty) :
    (∑ index ∈ main005VBandCellIndices epsilon length cell hcell,
      sectionSixStrictPrimeTerm digit length
        (sectionSixFirstLowCentralSmallTripleModulus index.1) index.2) =
      sectionSixFirstLowCentralSmallQuadrupleBandCellSum epsilon cell hcell digit length := by
  classical
  unfold sectionSixFirstLowCentralSmallQuadrupleBandCellSum propositionSixTwoBandSum
  rw [← main005VBandCellIndices_map_eq epsilon hepsilon hepsilonSmall hlength cell hcell]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro index hindex
  have htuple := main005VBandCell_forward hepsilon hepsilonSmall hlength cell hcell hindex
  have hsource := mem_propositionSixTwoPrimeTuples_iff_source.mp htuple
  dsimp [IsPropositionSixTwoPrimeTuple] at hsource
  exact main005VBand_term_eq_tupleTerm digit length index
    (by simpa [main005VBandTuple, main005VBandTupleEquiv] using hsource.1 3)
    (by simpa [main005VBandTuple, main005VBandTupleEquiv] using hsource.1 2)
    (by simpa [main005VBandTuple, main005VBandTupleEquiv] using hsource.1 1)
    (by simpa [main005VBandTuple, main005VBandTupleEquiv] using hsource.1 0)

private theorem main005V_not_clean_iff_exists_event
    (epsilon : Real) (length : Nat) (index : SectionSixFirstLowCentralSmallQuadrupleIndex) :
    (¬ sectionSixFirstLowCentralSmallCleanQuadrupleMem epsilon length index) <->
      ∃ event : Fin 5, main005VBandEventMem epsilon length event index := by
  let outside := main005VOutsideFirstBand epsilon length
  change ¬ (outside index.1.1.1 index.1.2 ∧ outside index.1.1.1 index.2 ∧
    outside index.1.1.2 index.1.2 ∧ outside index.1.1.2 index.2 ∧
    outside index.1.2 index.2) <-> _
  by_cases h0 : outside index.1.1.1 index.1.2 <;> by_cases h1 : outside index.1.1.1 index.2 <;>
  by_cases h2 : outside index.1.1.2 index.1.2 <;> by_cases h3 : outside index.1.1.2 index.2 <;>
  by_cases h4 : outside index.1.2 index.2 <;>
    simp_all [main005VBandEventMem, Fin.exists_fin_succ, outside]

private def main005VNonemptyCellEquiv :
    {cell : Finset (Fin 5) //
      cell ∈ (Finset.univ : Finset (Fin 5)).powerset.filter (·.Nonempty)} ≃
      {cell : Finset (Fin 5) // cell.Nonempty} where
  toFun cell := ⟨cell.1, (Finset.mem_filter.mp cell.2).2⟩
  invFun cell := ⟨cell.1, by simp [cell.2]⟩
  left_inv cell := by ext; rfl
  right_inv cell := by ext; rfl

/-- Exact inclusion-exclusion over the five closed pair-band events. -/
theorem sectionSixFirstLowCentralSmallQuadrupleBandSum_eq_inclusionExclusion
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowCentralSmallQuadrupleBandSum epsilon digit length =
      ∑ cell : {cell : Finset (Fin 5) // cell.Nonempty},
        ((-1 : Int) ^ (cell.1.card + 1)) •
          sectionSixFirstLowCentralSmallQuadrupleBandCellSum
            epsilon cell.1 cell.2 digit length := by
  classical
  unfold sectionSixFirstLowCentralSmallQuadrupleBandSum
  calc
    _ = ∑ index ∈ (Finset.univ : Finset (Fin 5)).biUnion
          (main005VBandEventIndices epsilon length),
        sectionSixStrictPrimeTerm digit length
          (sectionSixFirstLowCentralSmallTripleModulus index.1) index.2 := by
      apply Finset.sum_congr
      · ext index
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ,
          true_and, main005VBandEventIndices]
        constructor
        · rintro ⟨hraw, hnot⟩
          have hnot' : ¬ sectionSixFirstLowCentralSmallCleanQuadrupleMem epsilon length
              index := of_decide_eq_false (Bool.eq_false_of_not_eq_true' hnot)
          obtain ⟨event, hevent⟩ := (main005V_not_clean_iff_exists_event epsilon
            length index).1 hnot'
          exact ⟨event, hraw, hevent⟩
        · rintro ⟨event, hraw, hevent⟩
          have hnot := (main005V_not_clean_iff_exists_event epsilon length index).2
            ⟨event, hevent⟩
          refine ⟨hraw, ?_⟩
          rw [decide_eq_false hnot]
          rfl
      · intro index _hindex; rfl
    _ = _ := by
      rw [Finset.inclusion_exclusion_sum_biUnion]
      apply Fintype.sum_equiv main005VNonemptyCellEquiv
      intro cell
      change ((-1 : Int) ^ (cell.1.card + 1)) •
          (∑ index ∈ main005VBandCellIndices epsilon length cell.1 _,
            sectionSixStrictPrimeTerm digit length
              (sectionSixFirstLowCentralSmallTripleModulus index.1) index.2) =
        ((-1 : Int) ^ (cell.1.card + 1)) •
          sectionSixFirstLowCentralSmallQuadrupleBandCellSum epsilon cell.1 _ digit length
      rw [main005VBandCellSum_eq hepsilon hepsilonSmall digit hlength]

end
end PrimesRestrictedDigits
