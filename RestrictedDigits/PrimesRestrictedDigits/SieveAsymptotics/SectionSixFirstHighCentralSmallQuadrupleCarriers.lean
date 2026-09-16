import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogFourfold
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleRegions
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstHighCentralSmallIndices
import Mathlib.Tactic.Linarith

/-!
# Normalized carrier for the high central-small quadruple term

This file maps the exact nested index `(((p,q),r),s)` to the same left-associated analytic
role order. The map has coefficient one and retains the weak ties `s = r` and `r = q`.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 145--146, Eq. (6.16) and region `R_5`.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The recurrence-native quadruple roles in their literal nested order. -/
def sectionSixFirstHighCentralSmallQuadrupleNestedEquiv :
    SectionSixFirstHighCentralSmallQuadrupleIndex ≃
      (((Nat × Nat) × Nat) × Nat) where
  toFun index :=
    (((index.1.1.1, index.1.1.2), index.1.2), index.2)
  invFun quadruple :=
    ⟨⟨⟨quadruple.1.1.1, quadruple.1.1.2⟩, quadruple.1.2⟩,
      quadruple.2⟩
  left_inv index := by
    rcases index with ⟨⟨⟨p, q⟩, r⟩, s⟩
    rfl
  right_inv quadruple := by
    rcases quadruple with ⟨⟨⟨p, q⟩, r⟩, s⟩
    rfl

private theorem sectionSixFirstHighCentralSmallQuadrupleNested_mem_iff
    {a b : Real} {X : Nat}
    {region : Set (((Real × Real) × Real) × Real)}
    (index : SectionSixFirstHighCentralSmallQuadrupleIndex) :
    sectionSixFirstHighCentralSmallQuadrupleNestedEquiv index ∈
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
    sectionSixFirstHighCentralSmallQuadrupleNestedEquiv,
    Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  tauto

private theorem sectionSixFirstHighCentralSmallQuadruple_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstHighCentralSmallQuadrupleIndex) :
    index ∈ sectionSixFirstHighCentralSmallQuadrupleIndices epsilon length ↔
      sectionSixFirstHighCentralSmallQuadrupleNestedEquiv index ∈
        normalizedPrimeLogFourfoldIndices
          (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
          (sectionSixFirstHighCentralSmallQuadrupleRegion epsilon) := by
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
  have hcutoffs := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  have hgapPos : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  rw [sectionSixFirstHighCentralSmallQuadrupleNested_mem_iff]
  constructor
  · intro hindex
    have hquad :=
      mem_sectionSixFirstHighCentralSmallQuadrupleIndices.mp hindex
    have htriple :=
      mem_sectionSixFirstHighCentralSmallTripleIndices.mp hquad.1
    have hpiece :
        index.1.1 ∈ sectionSixFirstHighStrictIndices epsilon length ∧
          sectionSixZThree epsilon X <
              (sectionSixFirstPairProduct index.1.1 : Real) ∧
            (sectionSixFirstPairProduct index.1.1 : Real) <
                sectionSixZFive epsilon X ∧
              (sectionSixFirstPairSquareProduct index.1.1 : Real) <
                sectionSixZSix epsilon X := by
      have hmem := (Finset.mem_filter.mp htriple.1).2
      simpa [sectionSixFirstPairMem, X, XNat] using hmem
    have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
    have hpData := mem_sievePrimeInterval.mp hpqData.1
    have hqData := mem_sievePrimeInterval.mp hpqData.2
    have hrData := mem_sievePrimeInterval.mp htriple.2
    have hsData := mem_sievePrimeInterval.mp hquad.2
    have horder := sectionSixFirstHighCentralSmall_quadruple_order_and_caps
      hepsilon hepsilonSmall hlength hindex
    have hpBroad : p ∈ sievePrimeInterval
        (X ^ sectionSixThetaGap epsilon) (X ^ (1 / 2 : Real)) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [p] using hpData.1, ?_, ?_⟩
      · have hpLower : sectionSixZThree epsilon X < (p : Real) := by
          simpa [X, XNat, p] using hpData.2.1
        exact hcutoffs.1.trans (hcutoffs.2.1.trans hpLower)
      · simpa [sectionSixZFour_eq_rpow, X, XNat, p] using hpData.2.2
    have hqBroad : q ∈ sievePrimeInterval
        (X ^ sectionSixThetaGap epsilon) (X ^ (1 / 2 : Real)) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [q] using hqData.1, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
      · exact (by exact_mod_cast horder.2.2.1.le : (q : Real) <= p) |>.trans
          (mem_sievePrimeInterval.mp hpBroad).2.2
    have hrBroad : r ∈ sievePrimeInterval
        (X ^ sectionSixThetaGap epsilon) (X ^ (1 / 2 : Real)) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [r] using hrData.1, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, r] using hrData.2.1
      · exact (by exact_mod_cast horder.2.1 : (r : Real) <= q) |>.trans
          (mem_sievePrimeInterval.mp hqBroad).2.2
    have hsBroad : s ∈ sievePrimeInterval
        (X ^ sectionSixThetaGap epsilon) (X ^ (1 / 2 : Real)) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [s] using hsData.1, ?_, ?_⟩
      · simpa [sectionSixZOne, X, XNat, s] using hsData.2.1
      · exact (by exact_mod_cast horder.1 : (s : Real) <= r) |>.trans
          (mem_sievePrimeInterval.mp hrBroad).2.2
    have hpLog :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
        (sectionSixThetaTwo epsilon) (1 / 2 : Real)).2
        (by simpa [sectionSixZThree, sectionSixZFour_eq_rpow,
          X, XNat, p] using And.intro hpData.2.1 hpData.2.2)
    have hsLog : sectionSixThetaGap epsilon <
        normalizedPrimeLog XNat s := by
      change sectionSixThetaGap epsilon < Real.logb X (s : Real)
      apply (Real.lt_logb_iff_rpow_lt hX
        (by exact_mod_cast hsData.1.pos)).2
      simpa [sectionSixZOne, X, XNat, s] using hsData.2.1
    have hsrLog : normalizedPrimeLog XNat s <=
        normalizedPrimeLog XNat r := by
      change Real.logb X (s : Real) <= Real.logb X (r : Real)
      exact Real.logb_le_logb_of_le hX (by exact_mod_cast hsData.1.pos)
        (by exact_mod_cast horder.1)
    have hrqLog : normalizedPrimeLog XNat r <=
        normalizedPrimeLog XNat q := by
      change Real.logb X (r : Real) <= Real.logb X (q : Real)
      exact Real.logb_le_logb_of_le hX (by exact_mod_cast hrData.1.pos)
        (by exact_mod_cast horder.2.1)
    have hsquareLog : normalizedPrimeLog XNat p +
        2 * normalizedPrimeLog XNat q <
          1 - sectionSixThetaOne epsilon := by
      rw [sectionSixFirst_normalizedPairSquareProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero]
      apply (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).2
      simpa [sectionSixZSix, sectionSixFirstPairSquareProduct,
        X, XNat, p, q, Nat.cast_mul] using hpiece.2.2.2
    refine ⟨hpBroad, hqBroad, hrBroad, hsBroad, ?_⟩
    simpa [sectionSixFirstHighCentralSmallQuadrupleRegion,
      XNat, p, q, r, s] using
        And.intro hsLog
          (And.intro hsrLog
            (And.intro hrqLog
              (And.intro hpLog.1 (And.intro hpLog.2 hsquareLog))))
  · rintro ⟨hpBroad, hqBroad, hrBroad, hsBroad, hregion⟩
    have hpDataBroad := mem_sievePrimeInterval.mp hpBroad
    have hqDataBroad := mem_sievePrimeInterval.mp hqBroad
    have hrDataBroad := mem_sievePrimeInterval.mp hrBroad
    have hsDataBroad := mem_sievePrimeInterval.mp hsBroad
    have hregionData :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat s ∧
          normalizedPrimeLog XNat s <= normalizedPrimeLog XNat r ∧
          normalizedPrimeLog XNat r <= normalizedPrimeLog XNat q ∧
          sectionSixThetaTwo epsilon < normalizedPrimeLog XNat p ∧
          normalizedPrimeLog XNat p <= (1 / 2 : Real) ∧
          normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q <
            1 - sectionSixThetaOne epsilon := by
      simpa [sectionSixFirstHighCentralSmallQuadrupleRegion,
        XNat, p, q, r, s] using hregion
    have hpRange :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpDataBroad.1
        (sectionSixThetaTwo epsilon) (1 / 2 : Real)).1
        ⟨hregionData.2.2.2.1, hregionData.2.2.2.2.1⟩
    have hsPos : (0 : Real) < s := by exact_mod_cast hsDataBroad.1.pos
    have hrPos : (0 : Real) < r := by exact_mod_cast hrDataBroad.1.pos
    have hqPos : (0 : Real) < q := by exact_mod_cast hqDataBroad.1.pos
    have hpPos : (0 : Real) < p := by exact_mod_cast hpDataBroad.1.pos
    have hsr : s <= r := by
      exact_mod_cast (Real.logb_le_logb hX hsPos hrPos).1 hregionData.2.1
    have hrq : r <= q := by
      exact_mod_cast (Real.logb_le_logb hX hrPos hqPos).1 hregionData.2.2.1
    have hqpLog : normalizedPrimeLog XNat q < normalizedPrimeLog XNat p := by
      have hpLowerLog := hregionData.2.2.2.1
      have hsquareLog := hregionData.2.2.2.2.2
      simp only [sectionSixThetaOne, sectionSixThetaTwo] at hpLowerLog hsquareLog
      linarith
    have hqp : q <= p := by
      have : (q : Real) < p :=
        (Real.logb_lt_logb_iff hX hqPos hpPos).1 hqpLog
      exact_mod_cast this.le
    have hsLower : X ^ sectionSixThetaGap epsilon < (s : Real) := by
      exact (Real.lt_logb_iff_rpow_lt hX hsPos).1 hregionData.1
    have hrLower : X ^ sectionSixThetaGap epsilon < (r : Real) :=
      hsLower.trans_le (by exact_mod_cast hsr)
    have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) :=
      hrLower.trans_le (by exact_mod_cast hrq)
    have hqLogPos : 0 < normalizedPrimeLog XNat q := by
      have hqLogLower : sectionSixThetaGap epsilon <
          normalizedPrimeLog XNat q := by
        change sectionSixThetaGap epsilon < Real.logb X (q : Real)
        exact (Real.lt_logb_iff_rpow_lt hX hqPos).2 hqLower
      exact hgapPos.trans hqLogLower
    have hproductLowerLog : sectionSixThetaTwo epsilon <
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q := by
      linarith [hregionData.2.2.2.1, hqLogPos]
    have hproductUpperLog : normalizedPrimeLog XNat p +
        normalizedPrimeLog XNat q < 1 - sectionSixThetaTwo epsilon := by
      have hsquareLog := hregionData.2.2.2.2.2
      have hqLogLower : sectionSixThetaGap epsilon <
          normalizedPrimeLog XNat q := by
        change sectionSixThetaGap epsilon < Real.logb X (q : Real)
        exact (Real.lt_logb_iff_rpow_lt hX hqPos).2 hqLower
      simp only [sectionSixThetaGap, sectionSixThetaOne,
        sectionSixThetaTwo] at hqLogLower hsquareLog ⊢
      linarith
    have hproductLower : sectionSixZThree epsilon X <
        (sectionSixFirstPairProduct index.1.1 : Real) := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpDataBroad.1.ne_zero hqDataBroad.1.ne_zero] at hproductLowerLog
      have hraw := (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos hpDataBroad.1.pos hqDataBroad.1.pos)).1
          hproductLowerLog
      simpa [sectionSixZThree, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hproductUpper :
        (sectionSixFirstPairProduct index.1.1 : Real) <
          sectionSixZFive epsilon X := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpDataBroad.1.ne_zero hqDataBroad.1.ne_zero] at hproductUpperLog
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpDataBroad.1.pos hqDataBroad.1.pos)).1
          hproductUpperLog
      simpa [sectionSixZFive, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hsquare : (sectionSixFirstPairSquareProduct index.1.1 : Real) <
        sectionSixZSix epsilon X := by
      have hsquareLog := hregionData.2.2.2.2.2
      rw [sectionSixFirst_normalizedPairSquareProduct_eq
        hpDataBroad.1.ne_zero hqDataBroad.1.ne_zero] at hsquareLog
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpDataBroad.1.pos hqDataBroad.1.pos)
            hqDataBroad.1.pos)).1 hsquareLog
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
    have hhigh : index.1.1 ∈
        sectionSixFirstHighStrictIndices epsilon length := by
      apply mem_sectionSixFirstSecondRepeatedIndices.mpr
      constructor
      · apply mem_sievePrimeInterval.mpr
        simpa [sectionSixZThree, sectionSixZFour_eq_rpow,
          X, XNat, p] using And.intro hpDataBroad.1 hpRange
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hqDataBroad.1, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, q] using hqLower
        · exact (sectionSixFirst_direct_pairThreshold_iff
            hpDataBroad.1 hqDataBroad.1).2
              ⟨hqp, by simpa only [XNat, p, q] using hcapNat⟩
    have hpair : index.1.1 ∈
        sectionSixFirstPairPieceIndices epsilon length .highCentralSmall := by
      apply Finset.mem_filter.mpr
      constructor
      · simp [sectionSixFirstStrictIndices, hhigh]
      · simpa [sectionSixFirstPairMem, X, XNat] using
          And.intro hhigh
            (And.intro hproductLower (And.intro hproductUpper hsquare))
    have htriple : index.1 ∈
        sectionSixFirstHighCentralSmallTripleIndices epsilon length := by
      apply mem_sectionSixFirstHighCentralSmallTripleIndices.mpr
      refine ⟨hpair, mem_sievePrimeInterval.mpr ⟨hrDataBroad.1, ?_, ?_⟩⟩
      · simpa [sectionSixZOne, X, XNat, r] using hrLower
      · exact_mod_cast hrq
    apply mem_sectionSixFirstHighCentralSmallQuadrupleIndices.mpr
    refine ⟨htriple, mem_sievePrimeInterval.mpr ⟨hsDataBroad.1, ?_, ?_⟩⟩
    · simpa [sectionSixZOne, X, XNat, s] using hsLower
    · exact_mod_cast hsr

/-- The exact nested carrier is the normalized fourfold carrier, with no
symmetry or multiplicity factor. -/
theorem
    sectionSixFirstHighCentralSmallQuadrupleIndices_map_eq_normalizedPrimeLogFourfoldIndices
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstHighCentralSmallQuadrupleIndices epsilon length).map
        sectionSixFirstHighCentralSmallQuadrupleNestedEquiv.toEmbedding =
      normalizedPrimeLogFourfoldIndices
        (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
        (sectionSixFirstHighCentralSmallQuadrupleRegion epsilon) := by
  classical
  ext quadruple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstHighCentralSmallQuadruple_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro hquadruple
    let index : SectionSixFirstHighCentralSmallQuadrupleIndex :=
      sectionSixFirstHighCentralSmallQuadrupleNestedEquiv.symm quadruple
    have hinverse : sectionSixFirstHighCentralSmallQuadrupleNestedEquiv index =
        quadruple :=
      sectionSixFirstHighCentralSmallQuadrupleNestedEquiv.apply_symm_apply
        quadruple
    refine ⟨index, (sectionSixFirstHighCentralSmallQuadruple_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    simpa only [hinverse] using hquadruple

end

end PrimesRestrictedDigits
