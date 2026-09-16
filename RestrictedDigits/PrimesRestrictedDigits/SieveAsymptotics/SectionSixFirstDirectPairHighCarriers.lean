import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairCarriers

/-!
# High normalized carriers for the first direct pair pieces

This file proves the two high-branch carrier identities.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstHighStrict_mem_iff_normalizedBase
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let p := index.1
    let q := index.2
    index ∈ sectionSixFirstHighStrictIndices epsilon length ↔
      q ∈ sievePrimeInterval (X ^ sectionSixThetaGap epsilon)
          (X ^ (1 / 2 : Real)) ∧
        p ∈ sievePrimeInterval (X ^ sectionSixThetaGap epsilon)
          (X ^ (1 / 2 : Real)) ∧
        normalizedPrimeLog XNat q <= normalizedPrimeLog XNat p ∧
        sectionSixThetaTwo epsilon < normalizedPrimeLog XNat p ∧
        normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q <= 1 := by
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
  dsimp only
  constructor
  · intro hindex
    have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hindex
    have hpData := mem_sievePrimeInterval.mp hdata.1
    have hqData := mem_sievePrimeInterval.mp hdata.2
    have hthreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hpData.1 hqData.1).1
        hqData.2.2
    have hpBroad :
        p ∈ sievePrimeInterval (X ^ sectionSixThetaGap epsilon)
          (X ^ (1 / 2 : Real)) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [p] using hpData.1, ?_, ?_⟩
      · have hpLower := horder.1.trans horder.2.1 |>.trans hpData.2.1
        simpa [sectionSixZOne, X, XNat, p] using hpLower
      · simpa [sectionSixZFour_eq_rpow, X, XNat, p] using hpData.2.2
    have hqBroad :
        q ∈ sievePrimeInterval (X ^ sectionSixThetaGap epsilon)
          (X ^ (1 / 2 : Real)) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [q] using hqData.1, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
      · have hqpReal : (q : Real) <= (p : Real) := by
          exact_mod_cast hthreshold.1
        exact hqpReal.trans (mem_sievePrimeInterval.mp hpBroad).2.2
    have hlogOrder :
        normalizedPrimeLog XNat q <= normalizedPrimeLog XNat p := by
      change Real.logb X (q : Real) <= Real.logb X (p : Real)
      exact Real.logb_le_logb_of_le hX (by exact_mod_cast hqData.1.pos)
        (by exact_mod_cast hthreshold.1)
    have hpHighLog :
        sectionSixThetaTwo epsilon < normalizedPrimeLog XNat p := by
      have hpLog :=
        (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
          (sectionSixThetaTwo epsilon) (1 / 2 : Real)).2
          (by simpa [sectionSixZThree, sectionSixZFour,
              Real.sqrt_eq_rpow, X, XNat, p] using hpData.2)
      exact hpLog.1
    have hcapLog :
        normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q <= 1 := by
      rw [sectionSixFirst_normalizedPairSquareProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero]
      apply (Real.logb_le_iff_le_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).2
      norm_num only [Real.rpow_one]
      have hcapReal : (((p * q * q : Nat) : Real) <=
          ((10 ^ length : Nat) : Real)) := by
        exact_mod_cast hthreshold.2
      simpa only [X, XNat, p, q] using hcapReal
    exact ⟨hqBroad, hpBroad, hlogOrder, hpHighLog, hcapLog⟩
  · rintro ⟨hqBroad, hpBroad, hlogOrder, hpHighLog, hcapLog⟩
    have hqData := mem_sievePrimeInterval.mp hqBroad
    have hpData := mem_sievePrimeInterval.mp hpBroad
    have hqp : q <= p := by
      change Real.logb X (q : Real) <= Real.logb X (p : Real) at hlogOrder
      have hlogX : 0 < Real.log X := Real.log_pos hX
      have hlogOrder' : Real.log (q : Real) <= Real.log (p : Real) :=
        (div_le_div_iff_of_pos_right hlogX).1 hlogOrder
      have hqpReal : (q : Real) <= (p : Real) := by
        calc
          (q : Real) = Real.exp (Real.log (q : Real)) :=
            (Real.exp_log (by exact_mod_cast hqData.1.pos)).symm
          _ <= Real.exp (Real.log (p : Real)) := Real.exp_le_exp.mpr hlogOrder'
          _ = (p : Real) := Real.exp_log (by exact_mod_cast hpData.1.pos)
      exact_mod_cast hqpReal
    have hcap : p * q * q <= XNat := by
      rw [sectionSixFirst_normalizedPairSquareProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero] at hcapLog
      have hcapReal := (Real.logb_le_iff_le_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).1 hcapLog
      norm_num only [Real.rpow_one] at hcapReal
      have hcapCast : (((p * q * q : Nat) : Real) <=
          ((10 ^ length : Nat) : Real)) := by
        simpa only [X, XNat, p, q] using hcapReal
      exact_mod_cast hcapCast
    have hpHighLogData : normalizedPrimeLog XNat p ∈
        Set.Ioc (sectionSixThetaTwo epsilon) (1 / 2 : Real) := by
      have hpBroadLog :=
        (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
          (sectionSixThetaGap epsilon) (1 / 2 : Real)).2
          (by simpa [X, XNat, p] using hpData.2)
      exact ⟨by simpa [XNat, p] using hpHighLog, hpBroadLog.2⟩
    have hpHighRange :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
        (sectionSixThetaTwo epsilon) (1 / 2 : Real)).1 hpHighLogData
    apply mem_sectionSixFirstSecondRepeatedIndices.mpr
    constructor
    · apply mem_sievePrimeInterval.mpr
      simpa [sectionSixZThree, sectionSixZFour, Real.sqrt_eq_rpow,
        X, XNat, p] using And.intro hpData.1 hpHighRange
    · apply mem_sievePrimeInterval.mpr
      refine ⟨hqData.1, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
      · exact (sectionSixFirst_direct_pairThreshold_iff
          hpData.1 hqData.1).2 ⟨hqp, by simpa only [XNat] using hcap⟩

private theorem sectionSixFirstHighFar_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length .highFar ↔
      sectionSixFirstNatPair index ∈
        normalizedPrimeLogPairIndices (sectionSixThetaGap epsilon) (1 / 2)
          (10 ^ length) (sectionSixFirstHighFarRegion epsilon) := by
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
  rw [sectionSixFirstNatPair_mem_normalizedPrimeLogPairIndices_iff]
  have hbase := sectionSixFirstHighStrict_mem_iff_normalizedBase
    hepsilon hepsilonSmall hlength index
  dsimp only at hbase
  constructor
  · intro hindex
    have hpiece :
        index ∈ sectionSixFirstHighStrictIndices epsilon length ∧
          sectionSixZSix epsilon X <
            (sectionSixFirstPairProduct index : Real) := by
      have hmem := (Finset.mem_filter.mp hindex).2
      simpa [sectionSixFirstPairMem, X, XNat] using hmem
    rcases hbase.mp hpiece.1 with
      ⟨hqBroad, hpBroad, hlogOrder, hpHighLog, hcapLog⟩
    have hpBroadLog :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat
        (mem_sievePrimeInterval.mp hpBroad).1
        (sectionSixThetaGap epsilon) (1 / 2 : Real)).2
        (by simpa [X, XNat, p] using (mem_sievePrimeInterval.mp hpBroad).2)
    have hfarLog : 1 - sectionSixThetaOne epsilon <
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        (mem_sievePrimeInterval.mp hpBroad).1.ne_zero
        (mem_sievePrimeInterval.mp hqBroad).1.ne_zero]
      apply (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos
          (mem_sievePrimeInterval.mp hpBroad).1.pos
          (mem_sievePrimeInterval.mp hqBroad).1.pos)).2
      simpa [sectionSixZSix, sectionSixFirstPairProduct, X, XNat, p, q,
        Nat.cast_mul] using hpiece.2
    have hqBroadLog :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat
        (mem_sievePrimeInterval.mp hqBroad).1
        (sectionSixThetaGap epsilon) (1 / 2 : Real)).2
        (by simpa [X, XNat, q] using (mem_sievePrimeInterval.mp hqBroad).2)
    have hregionLocal :
        (normalizedPrimeLog XNat q, normalizedPrimeLog XNat p) ∈
          sectionSixFirstHighFarRegion epsilon :=
      ⟨hqBroadLog.1, by simpa only [XNat, p, q] using hlogOrder,
        by simpa only [XNat, p] using hpHighLog, hpBroadLog.2,
        by simpa only [XNat, p, q] using hcapLog, hfarLog⟩
    exact ⟨hqBroad, hpBroad, by simpa only [XNat, p, q] using hregionLocal⟩
  · rintro ⟨hqBroad, hpBroad, hregion⟩
    rcases hregion with
      ⟨hqLogLower, hlogOrder, hpHighLog, hpLogUpper, hcapLog, hfarLog⟩
    have hhigh := hbase.mpr ⟨hqBroad, hpBroad, hlogOrder,
      hpHighLog, hcapLog⟩
    have hpPrime := (mem_sievePrimeInterval.mp hpBroad).1
    have hqPrime := (mem_sievePrimeInterval.mp hqBroad).1
    have hfar : sectionSixZSix epsilon X <
        (sectionSixFirstPairProduct index : Real) := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpPrime.ne_zero hqPrime.ne_zero] at hfarLog
      have hfarReal :=
        (Real.lt_logb_iff_rpow_lt hX (by
          exact_mod_cast Nat.mul_pos hpPrime.pos hqPrime.pos)).1 hfarLog
      simpa [sectionSixZSix, sectionSixFirstPairProduct, X, XNat, p, q,
        Nat.cast_mul] using hfarReal
    simpa [sectionSixFirstPairPieceIndices, sectionSixFirstStrictIndices,
      sectionSixFirstPairMem, X, XNat, hhigh] using hfar

theorem image_sectionSixFirstHighFarPairPieceIndices
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstPairPieceIndices epsilon length .highFar).image
        sectionSixFirstNatPair =
      normalizedPrimeLogPairIndices (sectionSixThetaGap epsilon) (1 / 2)
        (10 ^ length) (sectionSixFirstHighFarRegion epsilon) := by
  classical
  ext pair
  rw [Finset.mem_image]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstHighFar_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro hpair
    let index : SectionSixFirstStrictIndex := ⟨pair.2, pair.1⟩
    have hinverse : sectionSixFirstNatPair index = pair := by
      rcases pair with ⟨q, p⟩
      rfl
    refine ⟨index, (sectionSixFirstHighFar_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    rw [hinverse]
    exact hpair

private theorem sectionSixFirstHighCentralLarge_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length .highCentralLarge ↔
      sectionSixFirstNatPair index ∈
        normalizedPrimeLogPairIndices (sectionSixThetaGap epsilon) (1 / 2)
          (10 ^ length)
          (sectionSixFirstHighCentralLargeRegion epsilon) := by
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
  rw [sectionSixFirstNatPair_mem_normalizedPrimeLogPairIndices_iff]
  have hbase := sectionSixFirstHighStrict_mem_iff_normalizedBase
    hepsilon hepsilonSmall hlength index
  dsimp only at hbase
  constructor
  · intro hindex
    have hpiece :
        index ∈ sectionSixFirstHighStrictIndices epsilon length ∧
          sectionSixZThree epsilon X <
              (sectionSixFirstPairProduct index : Real) ∧
            (sectionSixFirstPairProduct index : Real) <
              sectionSixZFive epsilon X ∧
            sectionSixZSix epsilon X <=
              (sectionSixFirstPairSquareProduct index : Real) := by
      have hmem := (Finset.mem_filter.mp hindex).2
      simpa [sectionSixFirstPairMem, X, XNat] using hmem
    rcases hbase.mp hpiece.1 with
      ⟨hqBroad, hpBroad, hlogOrder, hpHighLog, hcapLog⟩
    have hqData := mem_sievePrimeInterval.mp hqBroad
    have hpData := mem_sievePrimeInterval.mp hpBroad
    have hqBroadLog :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hqData.1
        (sectionSixThetaGap epsilon) (1 / 2 : Real)).2
        (by simpa [X, XNat, q] using hqData.2)
    have hpBroadLog :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
        (sectionSixThetaGap epsilon) (1 / 2 : Real)).2
        (by simpa [X, XNat, p] using hpData.2)
    have hproductEq := sectionSixFirst_normalizedPairProduct_eq (X := XNat)
      hpData.1.ne_zero hqData.1.ne_zero
    have hsquareEq := sectionSixFirst_normalizedPairSquareProduct_eq (X := XNat)
      hpData.1.ne_zero hqData.1.ne_zero
    have hproductLower : sectionSixThetaTwo epsilon <
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q := by
      rw [add_comm, hproductEq]
      apply (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).2
      simpa [sectionSixZThree, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hpiece.2.1
    have hproductUpper :
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q <
          1 - sectionSixThetaTwo epsilon := by
      rw [add_comm, hproductEq]
      apply (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).2
      simpa [sectionSixZFive, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hpiece.2.2.1
    have hsquareLower : 1 - sectionSixThetaOne epsilon <=
        normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q := by
      rw [hsquareEq]
      apply (Real.le_logb_iff_rpow_le hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).2
      simpa [sectionSixZSix, sectionSixFirstPairSquareProduct,
        X, XNat, p, q, Nat.cast_mul] using hpiece.2.2.2
    have hregionLocal :
        (normalizedPrimeLog XNat q, normalizedPrimeLog XNat p) ∈
          sectionSixFirstHighCentralLargeRegion epsilon :=
      ⟨hqBroadLog.1, by simpa only [XNat, p, q] using hlogOrder,
        by simpa only [XNat, p] using hpHighLog, hpBroadLog.2,
        by simpa only [XNat, p, q] using hcapLog, hproductLower,
        hproductUpper, hsquareLower⟩
    exact ⟨hqBroad, hpBroad, by simpa only [XNat, p, q] using hregionLocal⟩
  · rintro ⟨hqBroad, hpBroad, hregion⟩
    rcases hregion with
      ⟨hqLogLower, hlogOrder, hpHighLog, hpLogUpper, hcapLog,
        hproductLower, hproductUpper, hsquareLower⟩
    have hhigh := hbase.mpr ⟨hqBroad, hpBroad, hlogOrder,
      hpHighLog, hcapLog⟩
    have hqPrime := (mem_sievePrimeInterval.mp hqBroad).1
    have hpPrime := (mem_sievePrimeInterval.mp hpBroad).1
    have hproductEq := sectionSixFirst_normalizedPairProduct_eq (X := XNat)
      hpPrime.ne_zero hqPrime.ne_zero
    have hsquareEq := sectionSixFirst_normalizedPairSquareProduct_eq (X := XNat)
      hpPrime.ne_zero hqPrime.ne_zero
    have hproductLowerRaw : sectionSixZThree epsilon X <
        (sectionSixFirstPairProduct index : Real) := by
      rw [add_comm, hproductEq] at hproductLower
      have hraw := (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos hpPrime.pos hqPrime.pos)).1
        hproductLower
      simpa [sectionSixZThree, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hproductUpperRaw : (sectionSixFirstPairProduct index : Real) <
        sectionSixZFive epsilon X := by
      rw [add_comm, hproductEq] at hproductUpper
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpPrime.pos hqPrime.pos)).1
        hproductUpper
      simpa [sectionSixZFive, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hsquareLowerRaw : sectionSixZSix epsilon X <=
        (sectionSixFirstPairSquareProduct index : Real) := by
      rw [hsquareEq] at hsquareLower
      have hraw := (Real.le_logb_iff_rpow_le hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpPrime.pos hqPrime.pos) hqPrime.pos)).1
        hsquareLower
      simpa [sectionSixZSix, sectionSixFirstPairSquareProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    apply Finset.mem_filter.mpr
    constructor
    · simp [sectionSixFirstStrictIndices, hhigh]
    · change index ∈ sectionSixFirstHighStrictIndices epsilon length ∧
        sectionSixZThree epsilon (((10 ^ length : Nat) : Real)) <
            (sectionSixFirstPairProduct index : Real) ∧
          (sectionSixFirstPairProduct index : Real) <
            sectionSixZFive epsilon (((10 ^ length : Nat) : Real)) ∧
          sectionSixZSix epsilon (((10 ^ length : Nat) : Real)) <=
            (sectionSixFirstPairSquareProduct index : Real)
      exact ⟨hhigh, by simpa only [X, XNat] using hproductLowerRaw,
        by simpa only [X, XNat] using hproductUpperRaw,
        by simpa only [X, XNat] using hsquareLowerRaw⟩

theorem image_sectionSixFirstHighCentralLargePairPieceIndices
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstPairPieceIndices epsilon length
        .highCentralLarge).image sectionSixFirstNatPair =
      normalizedPrimeLogPairIndices (sectionSixThetaGap epsilon) (1 / 2)
        (10 ^ length) (sectionSixFirstHighCentralLargeRegion epsilon) := by
  classical
  ext pair
  rw [Finset.mem_image]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstHighCentralLarge_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro hpair
    let index : SectionSixFirstStrictIndex := ⟨pair.2, pair.1⟩
    have hinverse : sectionSixFirstNatPair index = pair := by
      rcases pair with ⟨q, p⟩
      rfl
    refine ⟨index, (sectionSixFirstHighCentralLarge_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    rw [hinverse]
    exact hpair

end

end PrimesRestrictedDigits
