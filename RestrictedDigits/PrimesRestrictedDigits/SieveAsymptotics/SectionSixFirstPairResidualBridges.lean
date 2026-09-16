import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstPairSums
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstPairPresentations
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoContract
import Mathlib.Tactic.FinCases

/-!
# Finite Type-II bridges for the first strict pair residuals

The three closed product-band pieces of the first strict Section 6 branches are reindexed by
the weakly ordered tuple `![q, p]`. This is the exact finite bridge used before applying
Proposition 6.2.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 140--146.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def sectionSixFirstPairTuple
    (index : SectionSixFirstStrictIndex) : Fin 2 -> Nat :=
  ![index.2, index.1]

private def IsSectionSixFirstPairTupleBase
    (epsilon : Real) (length : Nat) (region : Set (Fin 2 -> Real))
    (index : SectionSixFirstStrictIndex) : Prop :=
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let tuple := sectionSixFirstPairTuple index
  (forall i, (tuple i).Prime) ∧
    Monotone tuple ∧
    (forall i, X ^ sectionSixThetaGap epsilon <= (tuple i : Real)) ∧
    primeTupleProduct tuple * tuple 0 <= XNat ∧
    (fun i => normalizedPrimeLog XNat (tuple i)) ∈ region

private theorem sectionSixFirst_hXNat
    {length : Nat} (hlength : 1 <= length) :
    1 < 10 ^ length :=
  Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)

private theorem sectionSixFirst_pairThreshold_iff
    {length p q : Nat} (hp : p.Prime) (hq : q.Prime) :
    (q : Real) <= sectionSixFirstFactorThreshold length p <->
      q <= p ∧ p * q * q <= 10 ^ length := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hpPos : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  have hqPos : (0 : Real) < (q : Real) := by exact_mod_cast hq.pos
  unfold sectionSixFirstFactorThreshold
  change (q : Real) <= min (p : Real) (Real.sqrt (X / (p : Real))) <-> _
  rw [le_min_iff]
  constructor
  · rintro ⟨hqp, hqsqrt⟩
    have hsq : (q : Real) ^ 2 <= X / (p : Real) :=
      (Real.le_sqrt' hqPos).1 hqsqrt
    have hcapReal : (p : Real) * (q : Real) * (q : Real) <= X := by
      apply (le_div_iff₀ hpPos).1 at hsq
      nlinarith
    constructor
    · exact_mod_cast hqp
    · dsimp only [X, XNat] at hcapReal
      exact_mod_cast hcapReal
  · rintro ⟨hqp, hcap⟩
    constructor
    · exact_mod_cast hqp
    · apply (Real.le_sqrt' hqPos).2
      apply (le_div_iff₀ hpPos).2
      have hcapReal :
          ((p * q * q : Nat) : Real) <= ((10 ^ length : Nat) : Real) := by
        exact_mod_cast hcap
      norm_num only [Nat.cast_mul] at hcapReal
      nlinarith

private theorem sectionSixFirst_lowStrict_iff_tupleBase
    {epsilon : Real} (_hepsilon : 0 < epsilon)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstStrictIndex} :
    index ∈ sectionSixFirstLowStrictIndices epsilon length <->
      IsSectionSixFirstPairTupleBase epsilon length
        (sectionSixFirstLowResidualRegion epsilon) index := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1
  let q : Nat := index.2
  have hXNat : 1 < XNat := by
    simpa only [XNat] using sectionSixFirst_hXNat hlength
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  constructor
  · intro hindex
    have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hindex
    have hpData := mem_sievePrimeInterval.mp hdata.1
    have hqData := mem_sievePrimeInterval.mp hdata.2
    have hthreshold :=
      (sectionSixFirst_pairThreshold_iff hpData.1 hqData.1).1 hqData.2.2
    have hpLog :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
        (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)).2
        (by simpa [sectionSixZOne, sectionSixZTwo, X, XNat, p] using
          And.intro hpData.2.1 hpData.2.2)
    have hqLogLower :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q := by
      change sectionSixThetaGap epsilon < Real.logb X (q : Real)
      apply (Real.lt_logb_iff_rpow_lt hX (by exact_mod_cast hqData.1.pos)).2
      simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
    have hqLeP : q <= p := hthreshold.1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa [sectionSixFirstPairTuple, q] using hqData.1
      · simpa [sectionSixFirstPairTuple, p] using hpData.1
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [sectionSixFirstPairTuple, p, q]
    · intro i
      fin_cases i
      · simpa [sectionSixFirstPairTuple, sectionSixZOne, X, XNat, q] using
          hqData.2.1.le
      · simpa [sectionSixFirstPairTuple, sectionSixZOne, X, XNat, p] using
          hpData.2.1.le
    · simpa [sectionSixFirstPairTuple, primeTupleProduct, Fin.prod_univ_two,
        p, q, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, XNat] using
        hthreshold.2
    · simpa [sectionSixFirstLowResidualRegion, sectionSixFirstPairTuple,
        p, q] using And.intro hqLogLower hpLog
  · intro hbase
    dsimp [IsSectionSixFirstPairTupleBase] at hbase
    rcases hbase with ⟨hprime, hmono, _hlower, hcap, hregion⟩
    have hpPrime : p.Prime := by
      simpa [sectionSixFirstPairTuple, p] using hprime (1 : Fin 2)
    have hqPrime : q.Prime := by
      simpa [sectionSixFirstPairTuple, q] using hprime (0 : Fin 2)
    have hqp : q <= p := by
      simpa [sectionSixFirstPairTuple, p, q] using
        hmono (show (0 : Fin 2) <= 1 by decide)
    have hcap' : p * q * q <= XNat := by
      simpa [sectionSixFirstPairTuple, primeTupleProduct, Fin.prod_univ_two,
        p, q, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, XNat] using hcap
    have hpLog : normalizedPrimeLog XNat p ∈
        Set.Ioc (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon) := by
      simpa [sectionSixFirstLowResidualRegion, sectionSixFirstPairTuple,
        p, q] using And.intro hregion.2.1 hregion.2.2
    have hpRange :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpPrime
        (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)).1 hpLog
    have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) := by
      apply (Real.lt_logb_iff_rpow_lt hX (by exact_mod_cast hqPrime.pos)).1
      simpa [sectionSixFirstLowResidualRegion, sectionSixFirstPairTuple,
        normalizedPrimeLog, Real.logb, X, XNat, p, q] using hregion.1
    apply mem_sectionSixFirstSecondRepeatedIndices.mpr
    constructor
    · apply mem_sievePrimeInterval.mpr
      simpa [sectionSixZOne, sectionSixZTwo, X, XNat, p] using
        And.intro hpPrime hpRange
    · apply mem_sievePrimeInterval.mpr
      refine ⟨hqPrime, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, q] using hqLower
      · exact (sectionSixFirst_pairThreshold_iff hpPrime hqPrime).2
          ⟨hqp, by simpa only [XNat] using hcap'⟩

private theorem sectionSixFirst_highStrict_iff_tupleBase
    {epsilon : Real} (_hepsilon : 0 < epsilon)
    (_hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstStrictIndex} :
    index ∈ sectionSixFirstHighStrictIndices epsilon length <->
      IsSectionSixFirstPairTupleBase epsilon length
        (sectionSixFirstHighResidualRegion epsilon) index := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1
  let q : Nat := index.2
  have hXNat : 1 < XNat := by
    simpa only [XNat] using sectionSixFirst_hXNat hlength
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  constructor
  · intro hindex
    have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hindex
    have hpData := mem_sievePrimeInterval.mp hdata.1
    have hqData := mem_sievePrimeInterval.mp hdata.2
    have hthreshold :=
      (sectionSixFirst_pairThreshold_iff hpData.1 hqData.1).1 hqData.2.2
    have hpLog :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
        (sectionSixThetaTwo epsilon) (1 / 2 : Real)).2
        (by simpa [sectionSixZThree, sectionSixZFour, Real.sqrt_eq_rpow,
            X, XNat, p] using
          And.intro hpData.2.1 hpData.2.2)
    have hqLogLower :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q := by
      change sectionSixThetaGap epsilon < Real.logb X (q : Real)
      apply (Real.lt_logb_iff_rpow_lt hX (by exact_mod_cast hqData.1.pos)).2
      simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
    have hqLeP : q <= p := hthreshold.1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa [sectionSixFirstPairTuple, q] using hqData.1
      · simpa [sectionSixFirstPairTuple, p] using hpData.1
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [sectionSixFirstPairTuple, p, q]
    · intro i
      fin_cases i
      · simpa [sectionSixFirstPairTuple, sectionSixZOne, X, XNat, q] using
          hqData.2.1.le
      · have hqLePReal : (q : Real) <= (p : Real) := by
          exact_mod_cast hqLeP
        simpa [sectionSixFirstPairTuple, sectionSixZOne, X, XNat, p, q] using
          hqData.2.1.le.trans hqLePReal
    · simpa [sectionSixFirstPairTuple, primeTupleProduct, Fin.prod_univ_two,
        p, q, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, XNat] using
        hthreshold.2
    · simpa [sectionSixFirstHighResidualRegion, sectionSixFirstPairTuple,
        p, q] using And.intro hqLogLower hpLog
  · intro hbase
    dsimp [IsSectionSixFirstPairTupleBase] at hbase
    rcases hbase with ⟨hprime, hmono, _hlower, hcap, hregion⟩
    have hpPrime : p.Prime := by
      simpa [sectionSixFirstPairTuple, p] using hprime (1 : Fin 2)
    have hqPrime : q.Prime := by
      simpa [sectionSixFirstPairTuple, q] using hprime (0 : Fin 2)
    have hqp : q <= p := by
      simpa [sectionSixFirstPairTuple, p, q] using
        hmono (show (0 : Fin 2) <= 1 by decide)
    have hcap' : p * q * q <= XNat := by
      simpa [sectionSixFirstPairTuple, primeTupleProduct, Fin.prod_univ_two,
        p, q, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, XNat] using hcap
    have hpLog : normalizedPrimeLog XNat p ∈
        Set.Ioc (sectionSixThetaTwo epsilon) (1 / 2 : Real) := by
      simpa [sectionSixFirstHighResidualRegion, sectionSixFirstPairTuple,
        p, q] using And.intro hregion.2.1 hregion.2.2
    have hpRange :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpPrime
        (sectionSixThetaTwo epsilon) (1 / 2 : Real)).1 hpLog
    have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) := by
      apply (Real.lt_logb_iff_rpow_lt hX (by exact_mod_cast hqPrime.pos)).1
      simpa [sectionSixFirstHighResidualRegion, sectionSixFirstPairTuple,
        normalizedPrimeLog, Real.logb, X, XNat, p, q] using hregion.1
    apply mem_sectionSixFirstSecondRepeatedIndices.mpr
    constructor
    · apply mem_sievePrimeInterval.mpr
      simpa [sectionSixZThree, sectionSixZFour, Real.sqrt_eq_rpow,
          X, XNat, p] using
        And.intro hpPrime hpRange
    · apply mem_sievePrimeInterval.mpr
      refine ⟨hqPrime, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, q] using hqLower
      · exact (sectionSixFirst_pairThreshold_iff hpPrime hqPrime).2
          ⟨hqp, by simpa only [XNat] using hcap'⟩

private theorem sectionSixFirst_pairPiece_mem_iff
    {epsilon : Real} {length : Nat}
    {piece : SectionSixFirstPairPiece} {band : SectionSixDirectBand}
    {region : Set (Fin 2 -> Real)}
    (branch : Finset SectionSixFirstStrictIndex)
    (hbase : forall index,
      index ∈ branch <->
        IsSectionSixFirstPairTupleBase epsilon length region index)
    (hbranch : branch ⊆ sectionSixFirstStrictIndices epsilon length)
    (hpiece : forall index,
      sectionSixFirstPairMem epsilon length piece index <->
        index ∈ branch ∧
          sectionSixDirectRangeMembership band
            (((10 ^ length : Nat) : Real))
            (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
            (primeTupleSubproduct
              (sectionSixFirstPairTuple index) Finset.univ : Real))
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length piece <->
      sectionSixFirstPairTuple index ∈
        propositionSixTwoPrimeTuples epsilon 2 Finset.univ (0 : Fin 2)
          region length band := by
  classical
  rw [mem_propositionSixTwoPrimeTuples_iff_source]
  constructor
  · intro hindex
    have hfiltered :
        index ∈ sectionSixFirstStrictIndices epsilon length ∧
          sectionSixFirstPairMem epsilon length piece index := by
      simpa [sectionSixFirstPairPieceIndices] using hindex
    have hpieceData := (hpiece index).1 hfiltered.2
    have hbaseData := (hbase index).1 hpieceData.1
    dsimp [IsSectionSixFirstPairTupleBase] at hbaseData
    dsimp [IsPropositionSixTwoPrimeTuple]
    exact ⟨hbaseData.1, hbaseData.2.1, hbaseData.2.2.1,
      hpieceData.2, hbaseData.2.2.2.1, hbaseData.2.2.2.2⟩
  · intro htuple
    dsimp [IsPropositionSixTwoPrimeTuple] at htuple
    have hbaseData :
        IsSectionSixFirstPairTupleBase epsilon length region index := by
      exact ⟨htuple.1, htuple.2.1, htuple.2.2.1,
        htuple.2.2.2.2.1, htuple.2.2.2.2.2⟩
    have hbranchIndex := (hbase index).2 hbaseData
    have hfiltered :
        index ∈ sectionSixFirstStrictIndices epsilon length ∧
          sectionSixFirstPairMem epsilon length piece index :=
      ⟨hbranch hbranchIndex,
        (hpiece index).2 ⟨hbranchIndex, htuple.2.2.2.1⟩⟩
    simpa [sectionSixFirstPairPieceIndices] using hfiltered

private theorem sectionSixFirstLowBandFirst_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (_hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length .lowBandFirst <->
      sectionSixFirstPairTuple index ∈
        propositionSixTwoPrimeTuples epsilon 2 Finset.univ (0 : Fin 2)
          (sectionSixFirstLowResidualRegion epsilon) length .first := by
  apply sectionSixFirst_pairPiece_mem_iff
      (sectionSixFirstLowStrictIndices epsilon length)
  · intro candidate
    exact sectionSixFirst_lowStrict_iff_tupleBase hepsilon hlength
  · intro candidate hcandidate
    simp [sectionSixFirstStrictIndices, hcandidate]
  · intro candidate
    simp [sectionSixFirstPairMem, sectionSixDirectRangeMembership,
      sectionSixFirstPairTuple, sectionSixFirstPairProduct,
      primeTupleSubproduct, Fin.prod_univ_two,
      sectionSixZTwo, sectionSixZThree, Nat.cast_mul, mul_comm]

private theorem sectionSixFirstLowBandSecond_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (_hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length .lowBandSecond <->
      sectionSixFirstPairTuple index ∈
        propositionSixTwoPrimeTuples epsilon 2 Finset.univ (0 : Fin 2)
          (sectionSixFirstLowResidualRegion epsilon) length .second := by
  apply sectionSixFirst_pairPiece_mem_iff
      (sectionSixFirstLowStrictIndices epsilon length)
  · intro candidate
    exact sectionSixFirst_lowStrict_iff_tupleBase hepsilon hlength
  · intro candidate hcandidate
    simp [sectionSixFirstStrictIndices, hcandidate]
  · intro candidate
    simp [sectionSixFirstPairMem, sectionSixDirectRangeMembership,
      sectionSixFirstPairTuple, sectionSixFirstPairProduct,
      primeTupleSubproduct, Fin.prod_univ_two,
      sectionSixZFive, sectionSixZSix, Nat.cast_mul, mul_comm]

private theorem sectionSixFirstHighBandSecond_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length .highBandSecond <->
      sectionSixFirstPairTuple index ∈
        propositionSixTwoPrimeTuples epsilon 2 Finset.univ (0 : Fin 2)
          (sectionSixFirstHighResidualRegion epsilon) length .second := by
  apply sectionSixFirst_pairPiece_mem_iff
      (sectionSixFirstHighStrictIndices epsilon length)
  · intro candidate
    exact sectionSixFirst_highStrict_iff_tupleBase
      hepsilon hepsilonSmall hlength
  · intro candidate hcandidate
    simp [sectionSixFirstStrictIndices, hcandidate]
  · intro candidate
    simp [sectionSixFirstPairMem, sectionSixDirectRangeMembership,
      sectionSixFirstPairTuple, sectionSixFirstPairProduct,
      primeTupleSubproduct, Fin.prod_univ_two,
      sectionSixZFive, sectionSixZSix, Nat.cast_mul, mul_comm]

private theorem sectionSixFirstPairTerm_eq_tupleTerm
    (digit : Fin 10) (length : Nat) (index : SectionSixFirstStrictIndex)
    (hp : index.1.Prime) (hq : index.2.Prime) :
    sectionSixStrictPrimeTerm digit length (Nat.toPNat' index.1) index.2 =
      sectionSixSiftedSum digit length
        (primeTupleProduct (sectionSixFirstPairTuple index)).toPNat'
        (sectionSixFirstPairTuple index 0 : Real) := by
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (Nat.toPNat' index.1) hq]
  congr 1
  apply PNat.eq
  simp [PNat.mul_coe, Nat.toPNat'_coe, hp.pos, hq.pos,
    sectionSixFirstPairTuple, primeTupleProduct, Fin.prod_univ_two,
    Nat.mul_comm]

private theorem sectionSixFirstPairPieceSum_eq_bandSum
    {epsilon : Real} (digit : Fin 10) {length : Nat}
    {piece : SectionSixFirstPairPiece} {band : SectionSixDirectBand}
    {region : Set (Fin 2 -> Real)}
    (hmem : forall index,
      index ∈ sectionSixFirstPairPieceIndices epsilon length piece <->
        sectionSixFirstPairTuple index ∈
          propositionSixTwoPrimeTuples epsilon 2 Finset.univ (0 : Fin 2)
            region length band) :
    sectionSixFirstPairPieceSum epsilon digit length piece =
      propositionSixTwoBandSum epsilon 2 Finset.univ (0 : Fin 2)
        region digit length band := by
  classical
  unfold sectionSixFirstPairPieceSum propositionSixTwoBandSum
  apply Finset.sum_bij (fun index _ => sectionSixFirstPairTuple index)
  · intro index hindex
    exact (hmem index).1 hindex
  · intro left hleft right hright heq
    rcases left with ⟨p, q⟩
    rcases right with ⟨p', q'⟩
    have hp : p = p' := by
      simpa [sectionSixFirstPairTuple] using congrFun heq (1 : Fin 2)
    have hq : q = q' := by
      simpa [sectionSixFirstPairTuple] using congrFun heq (0 : Fin 2)
    subst p'
    subst q'
    rfl
  · intro tuple htuple
    let index : SectionSixFirstStrictIndex := ⟨tuple 1, tuple 0⟩
    have hinverse : sectionSixFirstPairTuple index = tuple := by
      funext i
      fin_cases i <;> rfl
    refine ⟨index, (hmem index).2 ?_, hinverse⟩
    rw [hinverse]
    exact htuple
  · intro index hindex
    have htuple := (hmem index).1 hindex
    have hsource := mem_propositionSixTwoPrimeTuples_iff_source.mp htuple
    dsimp [IsPropositionSixTwoPrimeTuple] at hsource
    exact sectionSixFirstPairTerm_eq_tupleTerm digit length index
      (by simpa [sectionSixFirstPairTuple] using hsource.1 (1 : Fin 2))
      (by simpa [sectionSixFirstPairTuple] using hsource.1 (0 : Fin 2))

/-- The low first closed product band is exactly its Proposition 6.2 sum. -/
theorem sectionSixFirstLowBandFirst_eq_propositionSixTwoBandSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstPairPieceSum epsilon digit length .lowBandFirst =
      propositionSixTwoBandSum epsilon 2 Finset.univ (0 : Fin 2)
        (sectionSixFirstLowResidualRegion epsilon) digit length .first := by
  apply sectionSixFirstPairPieceSum_eq_bandSum digit
  intro index
  exact sectionSixFirstLowBandFirst_mem_iff
    hepsilon hepsilonSmall hlength index

/-- The low second closed product band is exactly its Proposition 6.2 sum. -/
theorem sectionSixFirstLowBandSecond_eq_propositionSixTwoBandSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstPairPieceSum epsilon digit length .lowBandSecond =
      propositionSixTwoBandSum epsilon 2 Finset.univ (0 : Fin 2)
        (sectionSixFirstLowResidualRegion epsilon) digit length .second := by
  apply sectionSixFirstPairPieceSum_eq_bandSum digit
  intro index
  exact sectionSixFirstLowBandSecond_mem_iff
    hepsilon hepsilonSmall hlength index

/-- The high second closed product band is exactly its Proposition 6.2 sum. -/
theorem sectionSixFirstHighBandSecond_eq_propositionSixTwoBandSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstPairPieceSum epsilon digit length .highBandSecond =
      propositionSixTwoBandSum epsilon 2 Finset.univ (0 : Fin 2)
        (sectionSixFirstHighResidualRegion epsilon) digit length .second := by
  apply sectionSixFirstPairPieceSum_eq_bandSum digit
  intro index
  exact sectionSixFirstHighBandSecond_mem_iff
    hepsilon hepsilonSmall hlength index

end

end PrimesRestrictedDigits
