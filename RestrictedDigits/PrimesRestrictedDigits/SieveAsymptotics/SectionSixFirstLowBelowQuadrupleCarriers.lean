import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogFourfold
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleEquiv
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleRegions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Normalized carrier for the low-below clean quadruple term

This module identifies the exact recurrence-native carrier with the normalized left-associated
fourfold prime-log carrier, preserving all weak role-order faces and all six closed-band
exclusions.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.13), region `R_4`.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem lowBelowNested_mem_iff
    {a b : Real} {X : Nat}
    {region : Set (((Real × Real) × Real) × Real)}
    (index : SectionSixFirstLowBelowQuadrupleIndex) :
    sectionSixFirstLowBelowQuadrupleNestedEquiv index ∈
        normalizedPrimeLogFourfoldIndices a b X region ↔
      index.1.1.1 ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b) ∧
        index.1.1.2 ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b) ∧
        index.1.2 ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b) ∧
        index.2 ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b) ∧
        (((normalizedPrimeLog X index.1.1.1,
            normalizedPrimeLog X index.1.1.2),
          normalizedPrimeLog X index.1.2),
          normalizedPrimeLog X index.2) ∈ region := by
  classical
  simp only [normalizedPrimeLogFourfoldIndices,
    sectionSixFirstLowBelowQuadrupleNestedEquiv,
    Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  tauto

private theorem lowBelow_normalizedTripleProduct_eq
    {X a b c : Nat} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    normalizedPrimeLog X a + normalizedPrimeLog X b +
        normalizedPrimeLog X c =
      Real.logb (X : Real) ((a * b * c : Nat) : Real) := by
  have hab := sectionSixFirst_normalizedPairProduct_eq
    (X := X) (p := a) (q := b) ha hb
  calc
    normalizedPrimeLog X a + normalizedPrimeLog X b +
          normalizedPrimeLog X c =
        (normalizedPrimeLog X b + normalizedPrimeLog X a) +
          normalizedPrimeLog X c := by ring
    _ = Real.logb (X : Real) ((a * b : Nat) : Real) +
          Real.logb (X : Real) (c : Real) := by
      rw [hab]
      rfl
    _ = Real.logb (X : Real)
          (((a * b : Nat) : Real) * (c : Real)) := by
      rw [Real.logb_mul]
      · exact_mod_cast Nat.mul_ne_zero ha hb
      · exact_mod_cast hc
    _ = Real.logb (X : Real) ((a * b * c : Nat) : Real) := by
      norm_num only [Nat.cast_mul]

private theorem lowBelow_normalizedFourfoldProduct_eq
    {X a b c d : Nat} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    normalizedPrimeLog X a + normalizedPrimeLog X b +
          normalizedPrimeLog X c + normalizedPrimeLog X d =
      Real.logb (X : Real) ((a * b * c * d : Nat) : Real) := by
  have habc := lowBelow_normalizedTripleProduct_eq
    (X := X) (a := a) (b := b) (c := c) ha hb hc
  calc
    normalizedPrimeLog X a + normalizedPrimeLog X b +
          normalizedPrimeLog X c + normalizedPrimeLog X d =
          Real.logb (X : Real) ((a * b * c : Nat) : Real) +
          Real.logb (X : Real) (d : Real) := by
      rw [habc]
      rfl
    _ = Real.logb (X : Real)
          (((a * b * c : Nat) : Real) * (d : Real)) := by
      rw [Real.logb_mul]
      · exact_mod_cast Nat.mul_ne_zero (Nat.mul_ne_zero ha hb) hc
      · exact_mod_cast hd
    _ = Real.logb (X : Real) ((a * b * c * d : Nat) : Real) := by
      norm_num only [Nat.cast_mul]

private theorem lowBelow_logb_not_mem_Icc_iff
    {X n : Real} (hX : 1 < X) (hn : 0 < n) {lower upper : Real} :
    Real.logb X n ∉ Set.Icc lower upper ↔
      n < X ^ lower ∨ X ^ upper < n := by
  constructor
  · intro hnot
    by_cases hlow : n < X ^ lower
    · exact Or.inl hlow
    · right
      have hlower : lower <= Real.logb X n :=
        (Real.le_logb_iff_rpow_le hX hn).2 (le_of_not_gt hlow)
      by_contra hhigh
      have hupper : Real.logb X n <= upper :=
        (Real.logb_le_iff_le_rpow hX hn).2 (le_of_not_gt hhigh)
      exact hnot ⟨hlower, hupper⟩
  · rintro (hlow | hhigh) hmem
    · exact (not_lt_of_ge hmem.1)
        ((Real.logb_lt_iff_lt_rpow hX hn).2 hlow)
    · exact (not_lt_of_ge hmem.2)
        ((Real.lt_logb_iff_rpow_lt hX hn).2 hhigh)

private theorem lowBelowTriple_not_mem_Icc_iff
    {X a b c : Nat} (hX : 1 < (X : Real))
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    {lower upper : Real} :
    normalizedPrimeLog X a + normalizedPrimeLog X b +
          normalizedPrimeLog X c ∉ Set.Icc lower upper ↔
      (((a * b * c : Nat) : Real) < (X : Real) ^ lower ∨
        (X : Real) ^ upper < ((a * b * c : Nat) : Real)) := by
  rw [lowBelow_normalizedTripleProduct_eq
    ha.ne_zero hb.ne_zero hc.ne_zero]
  apply lowBelow_logb_not_mem_Icc_iff hX
  exact_mod_cast Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hc.pos

private theorem lowBelowFourfold_not_mem_Icc_iff
    {X a b c d : Nat} (hX : 1 < (X : Real))
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    {lower upper : Real} :
    normalizedPrimeLog X a + normalizedPrimeLog X b +
          normalizedPrimeLog X c + normalizedPrimeLog X d ∉
        Set.Icc lower upper ↔
      (((a * b * c * d : Nat) : Real) < (X : Real) ^ lower ∨
        (X : Real) ^ upper < ((a * b * c * d : Nat) : Real)) := by
  rw [lowBelow_normalizedFourfoldProduct_eq
    ha.ne_zero hb.ne_zero hc.ne_zero hd.ne_zero]
  apply lowBelow_logb_not_mem_Icc_iff hX
  exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hc.pos) hd.pos

private theorem lowBelowQuadruple_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstLowBelowQuadrupleIndex) :
    index ∈ sectionSixFirstLowBelowQuadrupleIndices epsilon length ↔
      sectionSixFirstLowBelowQuadrupleNestedEquiv index ∈
        normalizedPrimeLogFourfoldIndices
          (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)
          (10 ^ length)
          (sectionSixFirstLowBelowQuadrupleRegion epsilon) := by
  classical
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1.1.1
  let q : Nat := index.1.1.2
  let r : Nat := index.1.2
  let s : Nat := index.2
  have hXNat : 1 < XNat := by
    simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hgapPos : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  rw [lowBelowNested_mem_iff]
  constructor
  · intro hindex
    have hquad := mem_sectionSixFirstLowBelowQuadrupleIndices.mp hindex
    have hraw := mem_sectionSixFirstLowBelowRawQuadrupleIndices.mp hquad.1
    have htriple := mem_sectionSixFirstLowBelowTripleIndices.mp hraw.1
    have hpiece :
        index.1.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
          sectionSixZOne epsilon X <
              (sectionSixFirstPairProduct index.1.1 : Real) ∧
            (sectionSixFirstPairProduct index.1.1 : Real) <
              sectionSixZTwo epsilon X := by
      simpa [sectionSixFirstPairMem, X, XNat] using
        (Finset.mem_filter.mp htriple.1).2
    have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
    have hpData := mem_sievePrimeInterval.mp hpqData.1
    have hqData := mem_sievePrimeInterval.mp hpqData.2
    have hrData := mem_sievePrimeInterval.mp htriple.2
    have hsData := mem_sievePrimeInterval.mp hraw.2
    have hthreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hpData.1 hqData.1).1
        hqData.2.2
    have hpBroad : p ∈ sievePrimeInterval
        (X ^ sectionSixThetaGap epsilon)
        (X ^ sectionSixThetaOne epsilon) := by
      apply mem_sievePrimeInterval.mpr
      simpa [sectionSixZOne, sectionSixZTwo, X, XNat, p] using hpData
    have hqBroad : q ∈ sievePrimeInterval
        (X ^ sectionSixThetaGap epsilon)
        (X ^ sectionSixThetaOne epsilon) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [q] using hqData.1, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
      · exact (by exact_mod_cast hthreshold.1 : (q : Real) <= p) |>.trans
          (mem_sievePrimeInterval.mp hpBroad).2.2
    have hrBroad : r ∈ sievePrimeInterval
        (X ^ sectionSixThetaGap epsilon)
        (X ^ sectionSixThetaOne epsilon) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [r] using hrData.1, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, r] using hrData.2.1
      · exact hrData.2.2.trans
          (by simpa [X, XNat, q] using
            (mem_sievePrimeInterval.mp hqBroad).2.2)
    have hsBroad : s ∈ sievePrimeInterval
        (X ^ sectionSixThetaGap epsilon)
        (X ^ sectionSixThetaOne epsilon) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [s] using hsData.1, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, s] using hsData.2.1
      · exact hsData.2.2.trans
          (by simpa [X, XNat, r] using
            (mem_sievePrimeInterval.mp hrBroad).2.2)
    have hsLog : sectionSixThetaGap epsilon <
        normalizedPrimeLog XNat s := by
      change sectionSixThetaGap epsilon < Real.logb X (s : Real)
      apply (Real.lt_logb_iff_rpow_lt hX
        (by exact_mod_cast hsData.1.pos)).2
      simpa [sectionSixZOne, X, XNat, s] using hsData.2.1
    have hsrLog : normalizedPrimeLog XNat s <= normalizedPrimeLog XNat r := by
      exact Real.logb_le_logb_of_le hX (by exact_mod_cast hsData.1.pos)
        (by exact_mod_cast hsData.2.2)
    have hrqLog : normalizedPrimeLog XNat r <= normalizedPrimeLog XNat q := by
      exact Real.logb_le_logb_of_le hX (by exact_mod_cast hrData.1.pos)
        (by exact_mod_cast hrData.2.2)
    have hqpLog : normalizedPrimeLog XNat q <= normalizedPrimeLog XNat p := by
      exact Real.logb_le_logb_of_le hX (by exact_mod_cast hqData.1.pos)
        (by exact_mod_cast hthreshold.1)
    have hpqLog : normalizedPrimeLog XNat p + normalizedPrimeLog XNat q <
        sectionSixThetaOne epsilon := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero]
      apply (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).2
      simpa [sectionSixZTwo, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hpiece.2.2
    have hclean :
        (((p * q * r : Nat) : Real) < X ^ sectionSixThetaOne epsilon ∨
            X ^ sectionSixThetaTwo epsilon < ((p * q * r : Nat) : Real)) ∧
          (((p * q * s : Nat) : Real) < X ^ sectionSixThetaOne epsilon ∨
            X ^ sectionSixThetaTwo epsilon < ((p * q * s : Nat) : Real)) ∧
          (((p * r * s : Nat) : Real) < X ^ sectionSixThetaOne epsilon ∨
            X ^ sectionSixThetaTwo epsilon < ((p * r * s : Nat) : Real)) ∧
          (((q * r * s : Nat) : Real) < X ^ sectionSixThetaOne epsilon ∨
            X ^ sectionSixThetaTwo epsilon < ((q * r * s : Nat) : Real)) ∧
          (((p * q * r * s : Nat) : Real) < X ^ sectionSixThetaOne epsilon ∨
            X ^ sectionSixThetaTwo epsilon < ((p * q * r * s : Nat) : Real)) ∧
          (((p * q * r * s : Nat) : Real) < X ^ (1 - sectionSixThetaTwo epsilon) ∨
            X ^ (1 - sectionSixThetaOne epsilon) <
              ((p * q * r * s : Nat) : Real)) := by
      simpa [sectionSixFirstLowBelowCleanQuadrupleMem,
        sectionSixZTwo, sectionSixZThree, sectionSixZFive, sectionSixZSix,
        X, XNat, p, q, r, s] using hquad.2
    refine ⟨hpBroad, hqBroad, hrBroad, hsBroad, ?_⟩
    simp only [sectionSixFirstLowBelowQuadrupleRegion, Set.mem_setOf_eq]
    exact ⟨hsLog, hsrLog, hrqLog, hqpLog, hpqLog,
      (lowBelowTriple_not_mem_Icc_iff hX hpData.1 hqData.1 hrData.1).2 hclean.1,
      (lowBelowTriple_not_mem_Icc_iff hX hpData.1 hqData.1 hsData.1).2 hclean.2.1,
      (lowBelowTriple_not_mem_Icc_iff hX hpData.1 hrData.1 hsData.1).2 hclean.2.2.1,
      (lowBelowTriple_not_mem_Icc_iff hX hqData.1 hrData.1 hsData.1).2
        hclean.2.2.2.1,
      (lowBelowFourfold_not_mem_Icc_iff hX hpData.1 hqData.1 hrData.1
        hsData.1).2 hclean.2.2.2.2.1,
      (lowBelowFourfold_not_mem_Icc_iff hX hpData.1 hqData.1 hrData.1
        hsData.1).2 hclean.2.2.2.2.2⟩
  · rintro ⟨hpBroad, hqBroad, hrBroad, hsBroad, hregion⟩
    have hpData := mem_sievePrimeInterval.mp hpBroad
    have hqData := mem_sievePrimeInterval.mp hqBroad
    have hrData := mem_sievePrimeInterval.mp hrBroad
    have hsData := mem_sievePrimeInterval.mp hsBroad
    have hregionData :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat s ∧
          normalizedPrimeLog XNat s <= normalizedPrimeLog XNat r ∧
          normalizedPrimeLog XNat r <= normalizedPrimeLog XNat q ∧
          normalizedPrimeLog XNat q <= normalizedPrimeLog XNat p ∧
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q <
            sectionSixThetaOne epsilon ∧
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q +
              normalizedPrimeLog XNat r ∉
            Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q +
              normalizedPrimeLog XNat s ∉
            Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat r +
              normalizedPrimeLog XNat s ∉
            Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
          normalizedPrimeLog XNat q + normalizedPrimeLog XNat r +
              normalizedPrimeLog XNat s ∉
            Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q +
              normalizedPrimeLog XNat r + normalizedPrimeLog XNat s ∉
            Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q +
              normalizedPrimeLog XNat r + normalizedPrimeLog XNat s ∉
            Set.Icc (1 - sectionSixThetaTwo epsilon)
              (1 - sectionSixThetaOne epsilon) := by
      simpa [sectionSixFirstLowBelowQuadrupleRegion,
        XNat, p, q, r, s] using hregion
    rcases hregionData with
      ⟨hsLowerLog, hsrLog, hrqLog, hqpLog, hpqUpperLog,
        hA, hB, hC, hD, hE, hF⟩
    have hpPos : (0 : Real) < p := by exact_mod_cast hpData.1.pos
    have hqPos : (0 : Real) < q := by exact_mod_cast hqData.1.pos
    have hrPos : (0 : Real) < r := by exact_mod_cast hrData.1.pos
    have hsPos : (0 : Real) < s := by exact_mod_cast hsData.1.pos
    have hsr : s <= r := by
      exact_mod_cast (Real.logb_le_logb hX hsPos hrPos).1 hsrLog
    have hrq : r <= q := by
      exact_mod_cast (Real.logb_le_logb hX hrPos hqPos).1 hrqLog
    have hqp : q <= p := by
      exact_mod_cast (Real.logb_le_logb hX hqPos hpPos).1 hqpLog
    have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) :=
      hqData.2.1
    have hpLower : X ^ sectionSixThetaGap epsilon < (p : Real) :=
      hqLower.trans_le (by exact_mod_cast hqp)
    have hpUpperLog : normalizedPrimeLog XNat p <
        sectionSixThetaOne epsilon := by
      have hqLogPos : 0 < normalizedPrimeLog XNat q := by
        exact hgapPos.trans
          (hsLowerLog.trans_le (hsrLog.trans hrqLog))
      linarith
    have hpUpper : (p : Real) < X ^ sectionSixThetaOne epsilon := by
      exact (Real.logb_lt_iff_lt_rpow hX hpPos).1 hpUpperLog
    have hproductLower : sectionSixZOne epsilon X <
        (sectionSixFirstPairProduct index.1.1 : Real) := by
      have hqLtProduct : (q : Real) < p * q := by
        have hpOne : (1 : Real) < p := by exact_mod_cast hpData.1.one_lt
        nlinarith
      simpa [sectionSixZOne, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hqLower.trans hqLtProduct
    have hproductUpper : (sectionSixFirstPairProduct index.1.1 : Real) <
        sectionSixZTwo epsilon X := by
      have hproductUpperLog := hpqUpperLog
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero] at hproductUpperLog
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).1 hproductUpperLog
      simpa [sectionSixZTwo, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hsquareLog : normalizedPrimeLog XNat p +
        2 * normalizedPrimeLog XNat q < 1 := by
      simp only [sectionSixThetaOne] at hpqUpperLog
      linarith
    rw [sectionSixFirst_normalizedPairSquareProduct_eq
      hpData.1.ne_zero hqData.1.ne_zero] at hsquareLog
    have hcapReal : ((p * q * q : Nat) : Real) < X := by
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).1 hsquareLog
      simpa only [Real.rpow_one, X, XNat, p, q] using hraw
    have hcapNat : p * q * q <= XNat := by
      have hcapCast : ((p * q * q : Nat) : Real) <= (XNat : Real) := by
        simpa only [X] using hcapReal.le
      exact_mod_cast hcapCast
    have hlow : index.1.1 ∈ sectionSixFirstLowStrictIndices epsilon length := by
      apply mem_sectionSixFirstSecondRepeatedIndices.mpr
      constructor
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hpData.1, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, p] using hpLower
        · simpa [sectionSixZTwo, X, XNat, p] using hpUpper.le
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hqData.1, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, q] using hqLower
        · exact (sectionSixFirst_direct_pairThreshold_iff
            hpData.1 hqData.1).2 ⟨hqp, by simpa only [XNat] using hcapNat⟩
    have hpair : index.1.1 ∈
        sectionSixFirstPairPieceIndices epsilon length .lowBelow := by
      apply Finset.mem_filter.mpr
      refine ⟨by simp [sectionSixFirstStrictIndices, hlow], ?_⟩
      simpa [sectionSixFirstPairMem, X, XNat] using
        And.intro hlow (And.intro hproductLower hproductUpper)
    have htriple : index.1 ∈
        sectionSixFirstLowBelowTripleIndices epsilon length := by
      apply mem_sectionSixFirstLowBelowTripleIndices.mpr
      refine ⟨hpair, mem_sievePrimeInterval.mpr ⟨hrData.1, ?_, ?_⟩⟩
      · simpa [sectionSixZOne, X, XNat, r] using hrData.2.1
      · exact_mod_cast hrq
    have hraw : index ∈
        sectionSixFirstLowBelowRawQuadrupleIndices epsilon length := by
      apply mem_sectionSixFirstLowBelowRawQuadrupleIndices.mpr
      refine ⟨htriple, mem_sievePrimeInterval.mpr ⟨hsData.1, ?_, ?_⟩⟩
      · simpa [sectionSixZOne, X, XNat, s] using hsData.2.1
      · exact_mod_cast hsr
    have hclean : sectionSixFirstLowBelowCleanQuadrupleMem
        epsilon length index := by
      unfold sectionSixFirstLowBelowCleanQuadrupleMem
      dsimp only
      exact ⟨
        by simpa [sectionSixZTwo, sectionSixZThree, X, XNat, p, q, r] using
          (lowBelowTriple_not_mem_Icc_iff hX hpData.1 hqData.1 hrData.1).1 hA,
        by simpa [sectionSixZTwo, sectionSixZThree, X, XNat, p, q, s] using
          (lowBelowTriple_not_mem_Icc_iff hX hpData.1 hqData.1 hsData.1).1 hB,
        by simpa [sectionSixZTwo, sectionSixZThree, X, XNat, p, r, s] using
          (lowBelowTriple_not_mem_Icc_iff hX hpData.1 hrData.1 hsData.1).1 hC,
        by simpa [sectionSixZTwo, sectionSixZThree, X, XNat, q, r, s] using
          (lowBelowTriple_not_mem_Icc_iff hX hqData.1 hrData.1 hsData.1).1 hD,
        by simpa [sectionSixZTwo, sectionSixZThree, X, XNat, p, q, r, s] using
          (lowBelowFourfold_not_mem_Icc_iff hX hpData.1 hqData.1 hrData.1
            hsData.1).1 hE,
        by simpa [sectionSixZFive, sectionSixZSix, X, XNat, p, q, r, s] using
          (lowBelowFourfold_not_mem_Icc_iff hX hpData.1 hqData.1 hrData.1
            hsData.1).1 hF⟩
    exact mem_sectionSixFirstLowBelowQuadrupleIndices.mpr ⟨hraw, hclean⟩

theorem sectionSixFirstLowBelowQuadrupleIndices_map_eq_normalizedPrimeLogFourfoldIndices
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstLowBelowQuadrupleIndices epsilon length).map
        sectionSixFirstLowBelowQuadrupleNestedEquiv.toEmbedding =
      normalizedPrimeLogFourfoldIndices
        (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)
        (10 ^ length)
        (sectionSixFirstLowBelowQuadrupleRegion epsilon) := by
  classical
  ext quadruple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (lowBelowQuadruple_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro hquadruple
    let index : SectionSixFirstLowBelowQuadrupleIndex :=
      sectionSixFirstLowBelowQuadrupleNestedEquiv.symm quadruple
    have hinverse : sectionSixFirstLowBelowQuadrupleNestedEquiv index =
        quadruple :=
      sectionSixFirstLowBelowQuadrupleNestedEquiv.apply_symm_apply quadruple
    refine ⟨index, (lowBelowQuadruple_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    simpa only [hinverse] using hquadruple

end

end PrimesRestrictedDigits
