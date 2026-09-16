import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalRegions

/-!
# Low central-large terminal normalized carrier

This file maps the exact low central-large pair carrier to the weak-wall normalized region for
Maynard's `I_2` term.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstLowCentralLargeTerminal_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length .lowCentralLarge ↔
      sectionSixFirstNatPair index ∈
        normalizedPrimeLogPairIndices (sectionSixThetaGap epsilon) (1 / 2)
          (10 ^ length)
          (sectionSixFirstLowCentralLargeTerminalRegion epsilon) := by
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
  rw [sectionSixFirstNatPair_mem_normalizedPrimeLogPairIndices_iff]
  constructor
  · intro hindex
    have hpiece :
        index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
          sectionSixZThree epsilon X <
              (sectionSixFirstPairProduct index : Real) ∧
            (sectionSixFirstPairProduct index : Real) <
              sectionSixZFive epsilon X ∧
            sectionSixZSix epsilon X <=
              (sectionSixFirstPairSquareProduct index : Real) := by
      have hmem := (Finset.mem_filter.mp hindex).2
      simpa [sectionSixFirstPairMem, X, XNat] using hmem
    have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
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
      · simpa [sectionSixZOne, X, XNat, p] using hpData.2.1
      · have hpUpper : (p : Real) < sectionSixZFour X :=
          hpData.2.2.trans_lt (horder.2.1.trans horder.2.2.1)
        simpa [sectionSixZFour_eq_rpow] using hpUpper.le
    have hqBroad :
        q ∈ sievePrimeInterval (X ^ sectionSixThetaGap epsilon)
          (X ^ (1 / 2 : Real)) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [q] using hqData.1, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
      · have hqUpper : (q : Real) <= (p : Real) := by
          exact_mod_cast hthreshold.1
        exact hqUpper.trans (mem_sievePrimeInterval.mp hpBroad).2.2
    have hpLog :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
        (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)).2
        (by simpa [sectionSixZOne, sectionSixZTwo, X, XNat, p] using
          And.intro hpData.2.1 hpData.2.2)
    have hqLogLower :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat q := by
      change sectionSixThetaGap epsilon < Real.logb X (q : Real)
      apply (Real.lt_logb_iff_rpow_lt hX
        (by exact_mod_cast hqData.1.pos)).2
      simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
    have hlogOrder :
        normalizedPrimeLog XNat q <= normalizedPrimeLog XNat p := by
      change Real.logb X (q : Real) <= Real.logb X (p : Real)
      exact Real.logb_le_logb_of_le hX (by exact_mod_cast hqData.1.pos)
        (by exact_mod_cast hthreshold.1)
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
    have hsquareLower' : 1 <=
        normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q +
          sectionSixThetaOne epsilon := by
      linarith
    refine ⟨by simpa [X, XNat, q] using hqBroad,
      by simpa [X, XNat, p] using hpBroad, ?_⟩
    simpa [sectionSixFirstLowCentralLargeTerminalRegion, XNat, p, q] using
      ⟨hqLogLower, hlogOrder, hpLog.2, hproductLower,
        hproductUpper, hsquareLower', hcapLog⟩
  · rintro ⟨hqBroad, hpBroad, hregion⟩
    have hqData := mem_sievePrimeInterval.mp hqBroad
    have hpData := mem_sievePrimeInterval.mp hpBroad
    rcases hregion with
      ⟨hqLogLower, hlogOrder, hpLogUpper, hproductLower,
        hproductUpper, hsquareLower, hcapLog⟩
    have hpLowLog : normalizedPrimeLog XNat p ∈
        Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon) := by
      have hpBroadLog :=
        (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
          (sectionSixThetaGap epsilon) (1 / 2 : Real)).2
          (by simpa [X, XNat, p] using hpData.2)
      exact ⟨hpBroadLog.1, by simpa [XNat, p] using hpLogUpper⟩
    have hpLowRange :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
        (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)).1 hpLowLog
    have hqp : q <= p := by
      change Real.logb X (q : Real) <= Real.logb X (p : Real) at hlogOrder
      have hlogX : 0 < Real.log X := Real.log_pos hX
      have hlogOrder' : Real.log (q : Real) <= Real.log (p : Real) :=
        (div_le_div_iff_of_pos_right hlogX).1 hlogOrder
      have hqpReal : (q : Real) <= (p : Real) := by
        calc
          (q : Real) = Real.exp (Real.log (q : Real)) :=
            (Real.exp_log (by exact_mod_cast hqData.1.pos)).symm
          _ <= Real.exp (Real.log (p : Real)) :=
            Real.exp_le_exp.mpr hlogOrder'
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
    have hlow : index ∈ sectionSixFirstLowStrictIndices epsilon length := by
      apply mem_sectionSixFirstSecondRepeatedIndices.mpr
      constructor
      · apply mem_sievePrimeInterval.mpr
        simpa [sectionSixZOne, sectionSixZTwo, X, XNat, p] using
          And.intro hpData.1 hpLowRange
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hqData.1, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
        · exact (sectionSixFirst_direct_pairThreshold_iff
            hpData.1 hqData.1).2 ⟨hqp, by simpa only [XNat] using hcap⟩
    have hproductEq := sectionSixFirst_normalizedPairProduct_eq (X := XNat)
      hpData.1.ne_zero hqData.1.ne_zero
    have hsquareEq := sectionSixFirst_normalizedPairSquareProduct_eq (X := XNat)
      hpData.1.ne_zero hqData.1.ne_zero
    have hproductLowerRaw : sectionSixZThree epsilon X <
        (sectionSixFirstPairProduct index : Real) := by
      rw [add_comm, hproductEq] at hproductLower
      have hraw := (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).1 hproductLower
      simpa [sectionSixZThree, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hproductUpperRaw : (sectionSixFirstPairProduct index : Real) <
        sectionSixZFive epsilon X := by
      rw [add_comm, hproductEq] at hproductUpper
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).1 hproductUpper
      simpa [sectionSixZFive, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hsquareLowerRaw : sectionSixZSix epsilon X <=
        (sectionSixFirstPairSquareProduct index : Real) := by
      rw [hsquareEq] at hsquareLower
      have hraw := (Real.le_logb_iff_rpow_le hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).1
        hsquareLower
      simpa [sectionSixZSix, sectionSixFirstPairSquareProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    apply Finset.mem_filter.mpr
    constructor
    · simp [sectionSixFirstStrictIndices, hlow]
    · change index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
        sectionSixZThree epsilon (((10 ^ length : Nat) : Real)) <
            (sectionSixFirstPairProduct index : Real) ∧
          (sectionSixFirstPairProduct index : Real) <
            sectionSixZFive epsilon (((10 ^ length : Nat) : Real)) ∧
          sectionSixZSix epsilon (((10 ^ length : Nat) : Real)) <=
            (sectionSixFirstPairSquareProduct index : Real)
      exact ⟨hlow, by simpa only [X, XNat] using hproductLowerRaw,
        by simpa only [X, XNat] using hproductUpperRaw,
        by simpa only [X, XNat] using hsquareLowerRaw⟩

theorem image_sectionSixFirstLowCentralLargePairPieceIndices
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge).image sectionSixFirstNatPair =
      normalizedPrimeLogPairIndices
        (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
        (sectionSixFirstLowCentralLargeTerminalRegion epsilon) := by
  classical
  ext pair
  rw [Finset.mem_image]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstLowCentralLargeTerminal_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro hpair
    let index : SectionSixFirstStrictIndex := ⟨pair.2, pair.1⟩
    have hinverse : sectionSixFirstNatPair index = pair := by
      rcases pair with ⟨q, p⟩
      rfl
    refine ⟨index, (sectionSixFirstLowCentralLargeTerminal_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    rw [hinverse]
    exact hpair

end

end PrimesRestrictedDigits
