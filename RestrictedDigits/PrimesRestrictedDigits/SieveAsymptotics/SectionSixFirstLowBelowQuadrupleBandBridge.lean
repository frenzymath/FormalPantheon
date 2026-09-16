import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleBandCells
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleEquiv
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowTripleBaseBridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Low-below quadruple band
The six failures partition into seven cells (`MAYNARD-PRD-PUBLISHED`, pp. 137--138, 143--144).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def main005ADBandTupleEquiv :
    SectionSixFirstLowBelowQuadrupleIndex ≃ (Fin 4 -> Nat) where
  toFun index := ![index.2, index.1.2, index.1.1.2, index.1.1.1]
  invFun tuple := ⟨⟨⟨tuple 3, tuple 2⟩, tuple 1⟩, tuple 0⟩
  left_inv index := by rcases index with ⟨⟨⟨p, q⟩, r⟩, s⟩; rfl
  right_inv tuple := by funext i; fin_cases i <;> rfl
private abbrev main005ADBandTuple (index : SectionSixFirstLowBelowQuadrupleIndex) :
    Fin 4 -> Nat := main005ADBandTupleEquiv index

private def main005ADLogBandMem (epsilon : Real) (band : SectionSixDirectBand)
    (y : Real) : Prop :=
  match band with
  | .first => sectionSixThetaOne epsilon <= y ∧ y <= sectionSixThetaTwo epsilon
  | .second => 1 - sectionSixThetaTwo epsilon <= y ∧ y <= 1 - sectionSixThetaOne epsilon
private def main005ADBandCellLogMem (epsilon : Real) (cell : Fin 7)
    (x : Fin 4 -> Real) : Prop :=
  main005ADLogBandMem epsilon (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).2
      (∑ i ∈ (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).1, x i) ∧
    x ∈ sectionSixFirstLowBelowQuadrupleBandCellRegion epsilon cell
private def main005ADBandLogEvents (epsilon : Real) (x : Fin 4 -> Real) : Prop :=
  main005ADLogBandMem epsilon .first (∑ i ∈ ({1, 2, 3} : Finset (Fin 4)), x i) ∨
  main005ADLogBandMem epsilon .first (∑ i ∈ ({0, 2, 3} : Finset (Fin 4)), x i) ∨
  main005ADLogBandMem epsilon .first (∑ i ∈ ({0, 1, 3} : Finset (Fin 4)), x i) ∨
  main005ADLogBandMem epsilon .first (∑ i ∈ ({0, 1, 2} : Finset (Fin 4)), x i) ∨
  main005ADLogBandMem epsilon .first (∑ i, x i) ∨
  main005ADLogBandMem epsilon .second (∑ i, x i)
private noncomputable def main005ADBandCellIndices (epsilon : Real) (length : Nat)
    (cell : Fin 7) : Finset SectionSixFirstLowBelowQuadrupleIndex := by
  classical
  exact (sectionSixFirstLowBelowRawQuadrupleIndices epsilon length).filter fun index =>
    main005ADBandCellLogMem epsilon cell fun i =>
      normalizedPrimeLog (10 ^ length) (main005ADBandTuple index i)

private theorem main005AD_directRange_iff_logBand
    {epsilon : Real} {length : Nat} (hlength : 1 <= length)
    (tuple : Fin 4 -> Nat) (hprime : ∀ i, (tuple i).Prime)
    (I : Finset (Fin 4)) (band : SectionSixDirectBand) :
    sectionSixDirectRangeMembership band ((10 ^ length : Nat) : Real)
        (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
        (primeTupleSubproduct tuple I : Real) ↔
      main005ADLogBandMem epsilon band
        (∑ i ∈ I, normalizedPrimeLog (10 ^ length) (tuple i)) := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hXNat : 1 < XNat := by simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by dsimp only [X]; exact_mod_cast hXNat
  have hsubPos : (0 : Real) < primeTupleSubproduct tuple I := by
    exact_mod_cast Finset.prod_pos fun i _ => (hprime i).pos
  rw [sum_normalizedPrimeLog_finset_eq_subproduct tuple I fun i => (hprime i).ne_zero]
  change sectionSixDirectRangeMembership band X _ _ _ ↔ _
  cases band <;> exact and_congr (Real.le_logb_iff_rpow_le hX hsubPos).symm
    (Real.logb_le_iff_le_rpow hX hsubPos).symm

private theorem main005AD_normalized_monotone {XNat : Nat} (hX : (1 : Real) < XNat)
    {tuple : Fin 4 -> Nat} (hprime : ∀ i, (tuple i).Prime) (hmono : Monotone tuple) :
    Monotone fun i => normalizedPrimeLog XNat (tuple i) := by
  intro i j hij
  exact Real.logb_le_logb_of_le hX (by exact_mod_cast (hprime i).pos) (by exact_mod_cast hmono hij)

private theorem main005AD_fullCap {epsilon : Real} (hepsilonSmall : epsilon <= 1 / 64)
    {XNat : Nat} (hXNat : 1 < XNat) {tuple : Fin 4 -> Nat}
    (hprime : ∀ i, (tuple i).Prime)
    (hlogMono : Monotone fun i => normalizedPrimeLog XNat (tuple i))
    (hpair : normalizedPrimeLog XNat (tuple 3) +
      normalizedPrimeLog XNat (tuple 2) < sectionSixThetaOne epsilon) :
    primeTupleProduct tuple * tuple 0 <= XNat := by
  let x := fun i => normalizedPrimeLog XNat (tuple i)
  have h01 : x 0 <= x 1 := hlogMono (by decide)
  have h12 : x 1 <= x 2 := hlogMono (by decide)
  have h23 : x 2 <= x 3 := hlogMono (by decide)
  have hsum : x 0 + x 0 + x 1 + x 2 + x 3 < 1 := by
    simp only [sectionSixThetaOne] at hpair
    linarith
  let capTuple : Fin 5 -> Nat := ![tuple 0, tuple 0, tuple 1, tuple 2, tuple 3]
  have hcapPrime : ∀ i, (capTuple i).Prime := by intro i; fin_cases i <;> simp [capTuple, hprime]
  have hcapLog : normalizedPrimeLog XNat (primeTupleProduct capTuple) < 1 := by
    rw [← sum_normalizedPrimeLog_eq_normalizedPrimeLog_product fun i => (hcapPrime i).ne_zero]
    simpa [capTuple, Fin.sum_univ_succ, x, add_assoc] using hsum
  let X : Real := (XNat : Real)
  have hX : (1 : Real) < X := by dsimp only [X]; exact_mod_cast hXNat
  have hcapPos : (0 : Real) < primeTupleProduct capTuple := by
    exact_mod_cast primeTupleProduct_pos fun i => (hcapPrime i).ne_zero
  change Real.logb X (primeTupleProduct capTuple : Real) < 1 at hcapLog
  have hcapReal := (Real.logb_lt_iff_lt_rpow hX hcapPos).1 hcapLog
  rw [Real.rpow_one] at hcapReal
  change (primeTupleProduct capTuple : Real) < (XNat : Real) at hcapReal
  have hcapNat : primeTupleProduct capTuple < XNat := by exact_mod_cast hcapReal
  calc
    primeTupleProduct tuple * tuple 0 = primeTupleProduct capTuple := by
      simp [capTuple, primeTupleProduct, Fin.prod_univ_succ]; ring
    _ <= XNat := hcapNat.le

private theorem main005AD_tripleCap {epsilon : Real} (hepsilonSmall : epsilon <= 1 / 64)
    {XNat : Nat} (hXNat : 1 < XNat) {tuple : Fin 4 -> Nat}
    (hprime : ∀ i, (tuple i).Prime)
    (hlogMono : Monotone fun i => normalizedPrimeLog XNat (tuple i))
    (hpair : normalizedPrimeLog XNat (tuple 3) +
      normalizedPrimeLog XNat (tuple 2) < sectionSixThetaOne epsilon) :
    (primeTupleProduct (![tuple 1, tuple 2, tuple 3] : Fin 3 -> Nat) : Real) <=
      (XNat : Real) ^ (1 - sectionSixThetaOne epsilon) := by
  let triple : Fin 3 -> Nat := ![tuple 1, tuple 2, tuple 3]
  have htriplePrime : ∀ i, (triple i).Prime := by intro i; fin_cases i <;> simp [triple, hprime]
  have h12 := hlogMono (show (1 : Fin 4) <= 2 by decide)
  have h23 := hlogMono (show (2 : Fin 4) <= 3 by decide)
  have hsum : (∑ i, normalizedPrimeLog XNat (triple i)) <
      1 - sectionSixThetaOne epsilon := by
    simp [triple, Fin.sum_univ_succ, sectionSixThetaOne] at hpair ⊢
    linarith
  rw [sum_normalizedPrimeLog_eq_normalizedPrimeLog_product fun i => (htriplePrime i).ne_zero] at hsum
  let X : Real := (XNat : Real)
  have hX : (1 : Real) < X := by dsimp only [X]; exact_mod_cast hXNat
  have hproductPos : (0 : Real) < primeTupleProduct triple := by
    exact_mod_cast primeTupleProduct_pos fun i => (htriplePrime i).ne_zero
  exact ((Real.logb_lt_iff_lt_rpow hX hproductPos).1 hsum).le

private structure Main005ADRawData (epsilon : Real) (length : Nat)
    (tuple : Fin 4 -> Nat) : Prop where
  prime : ∀ i, (tuple i).Prime
  monotone : Monotone tuple
  lower : ∀ i, ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon <= tuple i
  cap : primeTupleProduct tuple * tuple 0 <= 10 ^ length
  logMonotone : Monotone fun i => normalizedPrimeLog (10 ^ length) (tuple i)
  gap : sectionSixThetaGap epsilon < normalizedPrimeLog (10 ^ length) (tuple 0)
  pair : normalizedPrimeLog (10 ^ length) (tuple 3) + normalizedPrimeLog (10 ^ length)
    (tuple 2) < sectionSixThetaOne epsilon

private theorem main005AD_rawData {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowBelowQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstLowBelowRawQuadrupleIndices epsilon length) :
    Main005ADRawData epsilon length (main005ADBandTuple index) := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hXNat : 1 < XNat := by simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by dsimp only [X]; exact_mod_cast hXNat
  have hraw := mem_sectionSixFirstLowBelowRawQuadrupleIndices.mp hindex
  have hsData := mem_sievePrimeInterval.mp hraw.2
  have htripleMapped : sectionSixFirstLowBelowTripleTupleEquiv index.1 ∈
      (sectionSixFirstLowBelowTripleIndices epsilon length).map
        sectionSixFirstLowBelowTripleTupleEquiv.toEmbedding :=
    Finset.mem_map.mpr ⟨index.1, hraw.1, rfl⟩
  have htripleTuple : sectionSixFirstLowBelowTripleTupleEquiv index.1 ∈ propositionSixOnePrimeTuples
      epsilon 3 (sectionSixFirstLowBelowTripleRegion epsilon) length := by
    rw [← sectionSixFirstLowBelowTripleIndices_map_eq_propositionSixOnePrimeTuples
      epsilon hepsilon hepsilonSmall hlength]
    exact htripleMapped
  have htripleSource := (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).1 htripleTuple
  dsimp [IsPropositionSixOnePrimeTuple] at htripleSource
  rcases htripleSource with
    ⟨htriplePrime, htripleMono, htripleLower, _htripleCap, htripleRegion⟩
  have hprime : ∀ i, (main005ADBandTuple index i).Prime := by
    intro i; fin_cases i
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv] using hsData.1
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv, sectionSixFirstLowBelowTripleTupleEquiv] using htriplePrime 0
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv, sectionSixFirstLowBelowTripleTupleEquiv] using htriplePrime 1
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv, sectionSixFirstLowBelowTripleTupleEquiv] using htriplePrime 2
  have hmono : Monotone (main005ADBandTuple index) := by
    rw [Fin.monotone_iff_le_succ]
    intro i; fin_cases i
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv] using hsData.2.2
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv, sectionSixFirstLowBelowTripleTupleEquiv] using htripleMono (show (0 : Fin 3) <= 1 by decide)
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv, sectionSixFirstLowBelowTripleTupleEquiv] using htripleMono (show (1 : Fin 3) <= 2 by decide)
  have hlower : ∀ i, X ^ sectionSixThetaGap epsilon <= (main005ADBandTuple index i : Real) := by
    intro i; fin_cases i
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv, sectionSixZOne, X, XNat] using hsData.2.1.le
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv, sectionSixFirstLowBelowTripleTupleEquiv, X, XNat] using htripleLower 0
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv, sectionSixFirstLowBelowTripleTupleEquiv, X, XNat] using htripleLower 1
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv, sectionSixFirstLowBelowTripleTupleEquiv, X, XNat] using htripleLower 2
  have hlogMono := main005AD_normalized_monotone hX hprime hmono
  have hregionData : sectionSixThetaGap epsilon < normalizedPrimeLog XNat index.1.2 ∧
      normalizedPrimeLog XNat index.1.1.1 + normalizedPrimeLog XNat index.1.1.2 <
        sectionSixThetaOne epsilon := by
    simpa [sectionSixFirstLowBelowTripleRegion, sectionSixFirstLowBelowTripleTupleEquiv, XNat] using htripleRegion
  have hsLog : sectionSixThetaGap epsilon < normalizedPrimeLog XNat index.2 := by
    change sectionSixThetaGap epsilon < Real.logb X (index.2 : Real)
    apply (Real.lt_logb_iff_rpow_lt hX (by exact_mod_cast hsData.1.pos)).2
    simpa [sectionSixZOne, X, XNat] using hsData.2.1
  have hcap := main005AD_fullCap hepsilonSmall hXNat hprime hlogMono
    (by simpa [main005ADBandTuple, main005ADBandTupleEquiv, XNat] using hregionData.2)
  exact ⟨hprime, hmono, by simpa [X, XNat] using hlower, hcap, hlogMono,
    by simpa [main005ADBandTuple, main005ADBandTupleEquiv, XNat] using hsLog,
    by simpa [main005ADBandTuple, main005ADBandTupleEquiv, XNat] using hregionData.2⟩

private theorem main005ADBandCell_forward {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) {length : Nat} (hlength : 1 <= length) (cell : Fin 7)
    {index : SectionSixFirstLowBelowQuadrupleIndex}
    (hindex : index ∈ main005ADBandCellIndices epsilon length cell) :
    main005ADBandTuple index ∈ propositionSixTwoPrimeTuples epsilon 4
      (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).1 (0 : Fin 4)
      (sectionSixFirstLowBelowQuadrupleBandCellRegion epsilon cell) length
      (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).2 := by
  classical
  have hfilter := Finset.mem_filter.mp hindex
  have hdata := main005AD_rawData hepsilon hepsilonSmall hlength hfilter.1
  rw [mem_propositionSixTwoPrimeTuples_iff_source]
  dsimp [IsPropositionSixTwoPrimeTuple]
  refine ⟨hdata.prime, hdata.monotone, hdata.lower, ?_, hdata.cap, hfilter.2.2⟩
  exact (main005AD_directRange_iff_logBand hlength _ hdata.prime _ _).2 hfilter.2.1

private theorem main005ADBandCell_reverse {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) {length : Nat} (hlength : 1 <= length) (cell : Fin 7)
    {index : SectionSixFirstLowBelowQuadrupleIndex}
    (htuple : main005ADBandTuple index ∈ propositionSixTwoPrimeTuples epsilon 4
      (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).1 (0 : Fin 4)
      (sectionSixFirstLowBelowQuadrupleBandCellRegion epsilon cell) length
      (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).2) :
    index ∈ main005ADBandCellIndices epsilon length cell := by
  classical
  rw [mem_propositionSixTwoPrimeTuples_iff_source] at htuple
  dsimp [IsPropositionSixTwoPrimeTuple] at htuple
  rcases htuple with ⟨hprime, hmono, hlower, hselected, _hcap, hregion⟩
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hXNat : 1 < XNat := by simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by dsimp only [X]; exact_mod_cast hXNat
  have hlogMono := main005AD_normalized_monotone hX hprime hmono
  have hregionData := hregion
  change sectionSixThetaGap epsilon < normalizedPrimeLog XNat index.2 ∧
    normalizedPrimeLog XNat index.1.1.1 + normalizedPrimeLog XNat index.1.1.2 <
      sectionSixThetaOne epsilon ∧ _ at hregionData
  rcases hregionData with ⟨hgap, hpair, hextra⟩
  have htripleCap := main005AD_tripleCap hepsilonSmall hXNat hprime hlogMono
    (by simpa [main005ADBandTuple, main005ADBandTupleEquiv, XNat] using hpair)
  have htripleSource : IsPropositionSixOnePrimeTuple epsilon length
      (sectionSixFirstLowBelowTripleRegion epsilon) (sectionSixFirstLowBelowTripleTupleEquiv index.1) := by
    dsimp [IsPropositionSixOnePrimeTuple]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i
      · simpa [sectionSixFirstLowBelowTripleTupleEquiv, main005ADBandTuple, main005ADBandTupleEquiv] using hprime 1
      · simpa [sectionSixFirstLowBelowTripleTupleEquiv, main005ADBandTuple, main005ADBandTupleEquiv] using hprime 2
      · simpa [sectionSixFirstLowBelowTripleTupleEquiv, main005ADBandTuple, main005ADBandTupleEquiv] using hprime 3
    · rw [Fin.monotone_iff_le_succ]
      intro i; fin_cases i
      · simpa [sectionSixFirstLowBelowTripleTupleEquiv, main005ADBandTuple,
          main005ADBandTupleEquiv] using hmono (show (1 : Fin 4) <= 2 by decide)
      · simpa [sectionSixFirstLowBelowTripleTupleEquiv, main005ADBandTuple,
          main005ADBandTupleEquiv] using hmono (show (2 : Fin 4) <= 3 by decide)
    · intro i; fin_cases i
      · simpa [sectionSixFirstLowBelowTripleTupleEquiv, main005ADBandTuple, main005ADBandTupleEquiv, X, XNat] using hlower (1 : Fin 4)
      · simpa [sectionSixFirstLowBelowTripleTupleEquiv, main005ADBandTuple, main005ADBandTupleEquiv, X, XNat] using hlower (2 : Fin 4)
      · simpa [sectionSixFirstLowBelowTripleTupleEquiv, main005ADBandTuple, main005ADBandTupleEquiv, X, XNat] using hlower (3 : Fin 4)
    · simpa [sectionSixFirstLowBelowTripleTupleEquiv, main005ADBandTuple,
        main005ADBandTupleEquiv, XNat] using htripleCap
    · simp only [sectionSixFirstLowBelowTripleRegion, Set.mem_setOf_eq]
      exact ⟨hgap.trans_le (hlogMono (show (0 : Fin 4) <= 1 by decide)), by
        simpa [sectionSixFirstLowBelowTripleTupleEquiv, main005ADBandTuple,
          main005ADBandTupleEquiv, XNat] using hpair⟩
  have htripleTuple := (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).2 htripleSource
  have htripleMapped : sectionSixFirstLowBelowTripleTupleEquiv index.1 ∈
      (sectionSixFirstLowBelowTripleIndices epsilon length).map sectionSixFirstLowBelowTripleTupleEquiv.toEmbedding := by
    rw [sectionSixFirstLowBelowTripleIndices_map_eq_propositionSixOnePrimeTuples
      epsilon hepsilon hepsilonSmall hlength]
    exact htripleTuple
  have htriple : index.1 ∈ sectionSixFirstLowBelowTripleIndices epsilon length := by simpa using htripleMapped
  have hsLower : X ^ sectionSixThetaGap epsilon < (index.2 : Real) := by
    change sectionSixThetaGap epsilon < Real.logb X (index.2 : Real) at hgap
    exact (Real.lt_logb_iff_rpow_lt hX (by exact_mod_cast (hprime (0 : Fin 4)).pos)).1
      hgap
  have hraw : index ∈ sectionSixFirstLowBelowRawQuadrupleIndices epsilon length := by
    apply mem_sectionSixFirstLowBelowRawQuadrupleIndices.mpr
    refine ⟨htriple, mem_sievePrimeInterval.mpr ⟨?_, ?_, ?_⟩⟩
    · simpa [main005ADBandTuple, main005ADBandTupleEquiv] using hprime (0 : Fin 4)
    · simpa [sectionSixZOne, X, XNat] using hsLower
    · exact_mod_cast hmono (show (0 : Fin 4) <= 1 by decide)
  apply Finset.mem_filter.mpr; refine ⟨hraw, ?_⟩
  exact ⟨(main005AD_directRange_iff_logBand hlength _ hprime _ _).1 hselected, hregion⟩

private theorem main005ADBandCellIndices_map_eq
    (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) (cell : Fin 7) :
    (main005ADBandCellIndices epsilon length cell).map
        main005ADBandTupleEquiv.toEmbedding =
      propositionSixTwoPrimeTuples epsilon 4
        (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).1 (0 : Fin 4)
        (sectionSixFirstLowBelowQuadrupleBandCellRegion epsilon cell) length
        (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).2 := by
  classical
  ext tuple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩; exact main005ADBandCell_forward hepsilon hepsilonSmall hlength cell hindex
  · intro htuple
    let index := main005ADBandTupleEquiv.symm tuple
    have hinverse : main005ADBandTuple index = tuple := main005ADBandTupleEquiv.apply_symm_apply tuple
    refine ⟨index, main005ADBandCell_reverse hepsilon hepsilonSmall hlength cell ?_, hinverse⟩
    simpa only [hinverse] using htuple

private theorem main005ADBand_term_eq_tupleTerm (digit : Fin 10) (length : Nat)
    (index : SectionSixFirstLowBelowQuadrupleIndex)
    (hp : index.1.1.1.Prime) (hq : index.1.1.2.Prime)
    (hr : index.1.2.Prime) (hs : index.2.Prime) :
    sectionSixStrictPrimeTerm digit length
        (sectionSixFirstLowBelowTripleModulus index.1) index.2 =
      sectionSixSiftedSum digit length
        (primeTupleProduct (main005ADBandTuple index)).toPNat'
        (main005ADBandTuple index (0 : Fin 4) : Real) := by
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (sectionSixFirstLowBelowTripleModulus index.1) hs]
  congr 1
  apply PNat.eq
  simp [sectionSixFirstLowBelowTripleModulus_coe hp hq hr,
    sectionSixFirstLowBelowTripleProduct, sectionSixFirstPairProduct,
    main005ADBandTuple, main005ADBandTupleEquiv, primeTupleProduct,
    Fin.prod_univ_succ, PNat.mul_coe, Nat.toPNat'_coe,
    hp.pos, hq.pos, hr.pos, hs.pos, Nat.mul_comm, Nat.mul_left_comm]

private theorem main005ADBandCellSum_eq
    {epsilon : Real} (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) (cell : Fin 7) :
    (∑ index ∈ main005ADBandCellIndices epsilon length cell,
      sectionSixStrictPrimeTerm digit length
        (sectionSixFirstLowBelowTripleModulus index.1) index.2) =
      sectionSixFirstLowBelowQuadrupleBandCellSum epsilon cell digit length := by
  classical
  unfold sectionSixFirstLowBelowQuadrupleBandCellSum propositionSixTwoBandSum
  rw [← main005ADBandCellIndices_map_eq epsilon hepsilon hepsilonSmall hlength cell]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro index hindex
  have htuple := main005ADBandCell_forward hepsilon hepsilonSmall hlength cell hindex
  have hsource := mem_propositionSixTwoPrimeTuples_iff_source.mp htuple
  dsimp [IsPropositionSixTwoPrimeTuple] at hsource
  exact main005ADBand_term_eq_tupleTerm digit length index
    (by simpa [main005ADBandTuple, main005ADBandTupleEquiv] using hsource.1 3)
    (by simpa [main005ADBandTuple, main005ADBandTupleEquiv] using hsource.1 2)
    (by simpa [main005ADBandTuple, main005ADBandTupleEquiv] using hsource.1 1)
    (by simpa [main005ADBandTuple, main005ADBandTupleEquiv] using hsource.1 0)

private theorem main005AD_exists_cell {epsilon : Real} (x : Fin 4 -> Real)
    (hgap : sectionSixThetaGap epsilon < x 0)
    (hpair : x 3 + x 2 < sectionSixThetaOne epsilon)
    (hmono : Monotone x)
    (hevents : main005ADBandLogEvents epsilon x) :
    ∃ cell : Fin 7, main005ADBandCellLogMem epsilon cell x := by
  have h01 := hmono (show (0 : Fin 4) <= 1 by decide)
  have h12 := hmono (show (1 : Fin 4) <= 2 by decide)
  have h23 := hmono (show (2 : Fin 4) <= 3 by decide)
  by_cases hA : main005ADLogBandMem epsilon .first (∑ i ∈ ({1, 2, 3} : Finset (Fin 4)), x i)
  · refine ⟨0, ?_⟩
    simp [main005ADBandCellLogMem, main005ADLogBandMem,
      sectionSixFirstLowBelowQuadrupleBandCellSelected,
      sectionSixFirstLowBelowQuadrupleBandCellRegion] at hA ⊢
    exact ⟨hA, hgap, hpair⟩
  by_cases hB : main005ADLogBandMem epsilon .first (∑ i ∈ ({0, 2, 3} : Finset (Fin 4)), x i)
  · refine ⟨1, ?_⟩
    simp [main005ADBandCellLogMem, sectionSixFirstLowBelowQuadrupleBandCellSelected, sectionSixFirstLowBelowQuadrupleBandCellRegion, main005ADLogBandMem] at hA hB ⊢
    exact ⟨hB, hgap, hpair, by linarith [hA (by linarith [hB.1, h01])]⟩
  by_cases hC : main005ADLogBandMem epsilon .first (∑ i ∈ ({0, 1, 3} : Finset (Fin 4)), x i)
  · refine ⟨2, ?_⟩
    simp [main005ADBandCellLogMem, sectionSixFirstLowBelowQuadrupleBandCellSelected, sectionSixFirstLowBelowQuadrupleBandCellRegion, main005ADLogBandMem] at hB hC ⊢
    exact ⟨hC, hgap, hpair, by linarith [hB (by linarith [hC.1, h12])]⟩
  by_cases hD : main005ADLogBandMem epsilon .first (∑ i ∈ ({0, 1, 2} : Finset (Fin 4)), x i)
  · refine ⟨3, ?_⟩
    simp [main005ADBandCellLogMem, sectionSixFirstLowBelowQuadrupleBandCellSelected, sectionSixFirstLowBelowQuadrupleBandCellRegion, main005ADLogBandMem] at hC hD ⊢
    exact ⟨hD, hgap, hpair, by linarith [hC (by linarith [hD.1, h23])]⟩
  by_cases hE : main005ADLogBandMem epsilon .first (∑ i, x i)
  · refine ⟨4, ?_⟩
    simp [main005ADBandCellLogMem, main005ADLogBandMem, Fin.sum_univ_succ,
      sectionSixFirstLowBelowQuadrupleBandCellSelected,
      sectionSixFirstLowBelowQuadrupleBandCellRegion] at hE ⊢
    exact ⟨hE, hgap, hpair⟩
  have hF : main005ADLogBandMem epsilon .second (∑ i, x i) := by
    rcases hevents with hA' | hB' | hC' | hD' | hE' | hF <;> simp_all
  by_cases hDlow : (∑ i ∈ ({0, 1, 2} : Finset (Fin 4)), x i) <
      sectionSixThetaOne epsilon
  · refine ⟨5, ?_⟩
    simp [main005ADBandCellLogMem, sectionSixFirstLowBelowQuadrupleBandCellSelected,
      sectionSixFirstLowBelowQuadrupleBandCellRegion, main005ADLogBandMem,
      Fin.sum_univ_succ, hgap, hpair] at hF hDlow ⊢
    exact ⟨hF, by linarith⟩
  · refine ⟨6, ?_⟩
    simp [main005ADBandCellLogMem, sectionSixFirstLowBelowQuadrupleBandCellSelected,
      sectionSixFirstLowBelowQuadrupleBandCellRegion, main005ADLogBandMem,
      Fin.sum_univ_succ] at hD hF hDlow ⊢
    exact ⟨hF, hgap, hpair, by linarith [hD hDlow]⟩

set_option maxHeartbeats 800000
private theorem main005AD_cell_unique {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {x : Fin 4 -> Real} (hmono : Monotone x) {a b : Fin 7}
    (ha : main005ADBandCellLogMem epsilon a x)
    (hb : main005ADBandCellLogMem epsilon b x) : a = b := by
  have h01 := hmono (show (0 : Fin 4) <= 1 by decide)
  have h12 := hmono (show (1 : Fin 4) <= 2 by decide)
  have h23 := hmono (show (2 : Fin 4) <= 3 by decide)
  fin_cases a <;> fin_cases b <;>
    simp [main005ADBandCellLogMem, main005ADLogBandMem,
      sectionSixFirstLowBelowQuadrupleBandCellSelected,
      sectionSixFirstLowBelowQuadrupleBandCellRegion,
      sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo,
      Fin.sum_univ_succ] at ha hb ⊢ <;>
    linarith

private theorem main005AD_cell_implies_events {epsilon : Real} {x : Fin 4 -> Real} {cell : Fin 7}
    (hcell : main005ADBandCellLogMem epsilon cell x) :
    main005ADBandLogEvents epsilon x := by
  fin_cases cell <;>
    simp [main005ADBandCellLogMem, main005ADBandLogEvents,
      sectionSixFirstLowBelowQuadrupleBandCellSelected,
      sectionSixFirstLowBelowQuadrupleBandCellRegion] at hcell ⊢ <;> tauto

private theorem main005AD_not_clean_iff_events
    {epsilon : Real} {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstLowBelowQuadrupleIndex)
    (hprime : ∀ i, (main005ADBandTuple index i).Prime) :
    (¬ sectionSixFirstLowBelowCleanQuadrupleMem epsilon length index) ↔
      main005ADBandLogEvents epsilon
        (fun i => normalizedPrimeLog (10 ^ length) (main005ADBandTuple index i)) := by
  have hA := main005AD_directRange_iff_logBand (epsilon := epsilon) hlength _ hprime ({1, 2, 3} : Finset (Fin 4)) .first
  have hB := main005AD_directRange_iff_logBand (epsilon := epsilon) hlength _ hprime ({0, 2, 3} : Finset (Fin 4)) .first
  have hC := main005AD_directRange_iff_logBand (epsilon := epsilon) hlength _ hprime ({0, 1, 3} : Finset (Fin 4)) .first
  have hD := main005AD_directRange_iff_logBand (epsilon := epsilon) hlength _ hprime ({0, 1, 2} : Finset (Fin 4)) .first
  have hE := main005AD_directRange_iff_logBand (epsilon := epsilon) hlength _ hprime (Finset.univ : Finset (Fin 4)) .first
  have hF := main005AD_directRange_iff_logBand (epsilon := epsilon) hlength _ hprime (Finset.univ : Finset (Fin 4)) .second
  unfold main005ADBandLogEvents
  rw [← hA, ← hB, ← hC, ← hD, ← hE, ← hF]
  simp only [sectionSixFirstLowBelowCleanQuadrupleMem, not_and_or, not_or, not_lt]
  simp [sectionSixDirectRangeMembership, sectionSixZTwo, sectionSixZThree,
    sectionSixZFive, sectionSixZSix, main005ADBandTuple, main005ADBandTupleEquiv,
    primeTupleSubproduct, Nat.cast_mul, Fin.prod_univ_succ, mul_comm, mul_left_comm]

private theorem main005ADBandCellIndices_pairwiseDisjoint
    {epsilon : Real} (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    ((Finset.univ : Finset (Fin 7)) : Set (Fin 7)).PairwiseDisjoint
      (main005ADBandCellIndices epsilon length) := by
  classical
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro index ha hb
  have haData := Finset.mem_filter.mp ha
  have hbData := Finset.mem_filter.mp hb
  have hdata := main005AD_rawData hepsilon hepsilonSmall hlength haData.1
  exact hab (main005AD_cell_unique hepsilon hepsilonSmall hdata.logMonotone
    haData.2 hbData.2)
private local instance main005ADCleanDecidable (epsilon : Real) (length : Nat) :
    DecidablePred (sectionSixFirstLowBelowCleanQuadrupleMem epsilon length) := Classical.decPred _
private theorem main005ADBandCells_biUnion_eq
    {epsilon : Real} (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (Finset.univ : Finset (Fin 7)).biUnion
        (main005ADBandCellIndices epsilon length) =
      (sectionSixFirstLowBelowRawQuadrupleIndices epsilon length).filter
        fun index => ¬ sectionSixFirstLowBelowCleanQuadrupleMem epsilon length index := by
  classical
  ext index
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, main005ADBandCellIndices,
    Finset.mem_filter]
  constructor
  · rintro ⟨cell, hraw, hcell⟩
    refine ⟨hraw, ?_⟩
    have hdata := main005AD_rawData hepsilon hepsilonSmall hlength hraw
    exact (main005AD_not_clean_iff_events hlength index hdata.prime).2
      (main005AD_cell_implies_events hcell)
  · rintro ⟨hraw, hnot⟩
    have hdata := main005AD_rawData hepsilon hepsilonSmall hlength hraw
    have hevents := (main005AD_not_clean_iff_events hlength index hdata.prime).1 hnot
    obtain ⟨cell, hcell⟩ := main005AD_exists_cell _ hdata.gap hdata.pair
      hdata.logMonotone hevents
    exact ⟨cell, hraw, hcell⟩

/-- The low-below quadruple band is the coefficient-one sum of its seven
disjoint first-hit Proposition 6.2 cells. -/
theorem sectionSixFirstLowBelowQuadrupleBandSum_eq_firstHitCells
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowBelowQuadrupleBandSum epsilon digit length =
      ∑ cell : Fin 7,
        sectionSixFirstLowBelowQuadrupleBandCellSum epsilon cell digit length := by
  classical
  unfold sectionSixFirstLowBelowQuadrupleBandSum
  rw [← main005ADBandCells_biUnion_eq hepsilon hepsilonSmall hlength]
  rw [Finset.sum_biUnion
    (main005ADBandCellIndices_pairwiseDisjoint hepsilon hepsilonSmall hlength)]
  apply Finset.sum_congr rfl
  intro cell _
  exact main005ADBandCellSum_eq hepsilon hepsilonSmall digit hlength cell

end

end PrimesRestrictedDigits
