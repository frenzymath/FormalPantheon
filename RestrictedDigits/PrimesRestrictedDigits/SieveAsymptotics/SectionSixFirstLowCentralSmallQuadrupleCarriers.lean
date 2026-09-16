import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogFourfold
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallQuadrupleRegions
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralSmallIndices
import Mathlib.Tactic.Linarith
/-!
# Normalized carrier for the low central-small clean quadruple term
Maps the exact clean nested index `(((p,q),r),s)` to the same analytic role
order with coefficient one. Source: `MAYNARD-PRD-PUBLISHED`, Section 6,
p. 143, Eq. (6.12), region `R_3`.
-/
namespace PrimesRestrictedDigits
noncomputable section
/-- The recurrence-native quadruple roles in their literal nested order. -/
def sectionSixFirstLowCentralSmallQuadrupleNestedEquiv :
    SectionSixFirstLowCentralSmallQuadrupleIndex ≃
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
private theorem sectionSixFirstLowCentralSmallQuadrupleNested_mem_iff
    {a b : Real} {X : Nat}
    {region : Set (((Real × Real) × Real) × Real)}
    (index : SectionSixFirstLowCentralSmallQuadrupleIndex) :
    sectionSixFirstLowCentralSmallQuadrupleNestedEquiv index ∈
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
    sectionSixFirstLowCentralSmallQuadrupleNestedEquiv,
    Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  tauto
private theorem sectionSixFirstLowCentralSmall_normalizedProduct_eq
    {X a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) :
    normalizedPrimeLog X a + normalizedPrimeLog X b =
      Real.logb (X : Real) ((a * b : Nat) : Real) := by
  simpa only [add_comm] using
    (sectionSixFirst_normalizedPairProduct_eq (X := X) (p := a) (q := b)
      ha hb)
private theorem sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff
    {epsilon : Real} {X a b : Nat} (hX : 1 < (X : Real))
    (ha : a.Prime) (hb : b.Prime) :
    normalizedPrimeLog X a + normalizedPrimeLog X b ∉
        Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ↔
      (((a * b : Nat) : Real) < (X : Real) ^ sectionSixThetaOne epsilon ∨
        (X : Real) ^ sectionSixThetaTwo epsilon <
          ((a * b : Nat) : Real)) := by
  rw [sectionSixFirstLowCentralSmall_normalizedProduct_eq
    ha.ne_zero hb.ne_zero]
  have habPos : (0 : Real) < ((a * b : Nat) : Real) := by
    exact_mod_cast Nat.mul_pos ha.pos hb.pos
  constructor
  · intro hnot
    by_cases hlow : ((a * b : Nat) : Real) <
        (X : Real) ^ sectionSixThetaOne epsilon
    · exact Or.inl hlow
    · right
      have hthetaOne : sectionSixThetaOne epsilon <=
          Real.logb (X : Real) ((a * b : Nat) : Real) :=
        (Real.le_logb_iff_rpow_le hX habPos).2 (le_of_not_gt hlow)
      by_contra hhigh
      have hthetaTwo :
          Real.logb (X : Real) ((a * b : Nat) : Real) <=
            sectionSixThetaTwo epsilon :=
        (Real.logb_le_iff_le_rpow hX habPos).2 (le_of_not_gt hhigh)
      exact hnot ⟨hthetaOne, hthetaTwo⟩
  · rintro (hlow | hhigh) hmem
    · have hlog := (Real.logb_lt_iff_lt_rpow hX habPos).2 hlow
      exact (not_lt_of_ge hmem.1) hlog
    · have hlog := (Real.lt_logb_iff_rpow_lt hX habPos).2 hhigh
      exact (not_lt_of_ge hmem.2) hlog
private theorem sectionSixFirstLowCentralSmall_normalizedFullProduct_eq
    {X p q r s : Nat} (hp : p ≠ 0) (hq : q ≠ 0)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    normalizedPrimeLog X p + normalizedPrimeLog X q +
          normalizedPrimeLog X r + 2 * normalizedPrimeLog X s =
      Real.logb (X : Real) ((p * q * r * s * s : Nat) : Real) := by
  change Real.logb (X : Real) (p : Real) +
        Real.logb (X : Real) (q : Real) +
        Real.logb (X : Real) (r : Real) +
        2 * Real.logb (X : Real) (s : Real) = _
  norm_num only [Nat.cast_mul]
  rw [Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_mul]
  · ring
  · exact_mod_cast hp
  · exact_mod_cast hq
  · exact_mod_cast mul_ne_zero hp hq
  · exact_mod_cast hr
  · exact_mod_cast mul_ne_zero (mul_ne_zero hp hq) hr
  · exact_mod_cast hs
  · exact_mod_cast mul_ne_zero (mul_ne_zero (mul_ne_zero hp hq) hr) hs
  · exact_mod_cast hs
private theorem sectionSixFirstLowCentralSmallQuadruple_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstLowCentralSmallQuadrupleIndex) :
    index ∈ sectionSixFirstLowCentralSmallQuadrupleIndices epsilon length ↔
      sectionSixFirstLowCentralSmallQuadrupleNestedEquiv index ∈
        normalizedPrimeLogFourfoldIndices
          (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)
          (10 ^ length)
          (sectionSixFirstLowCentralSmallQuadrupleRegion epsilon) := by
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
  rw [sectionSixFirstLowCentralSmallQuadrupleNested_mem_iff]
  constructor
  · intro hindex
    have hquad :=
      mem_sectionSixFirstLowCentralSmallQuadrupleIndices.mp hindex
    have hraw :=
      mem_sectionSixFirstLowCentralSmallRawQuadrupleIndices.mp hquad.1
    have htriple :=
      mem_sectionSixFirstLowCentralSmallTripleIndices.mp hraw.1
    have hpiece :
        index.1.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
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
    have hsData := mem_sievePrimeInterval.mp hraw.2
    have hthreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hpData.1 hqData.1).1
        hqData.2.2
    have hsReduced := hsData.2.2
    rw [sectionSixFirstLowCentralSmallTripleReducedThreshold,
      le_min_iff] at hsReduced
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
      · exact hsReduced.1.trans
          (by simpa [X, XNat, r] using
            (mem_sievePrimeInterval.mp hrBroad).2.2)
    have hpLog :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
        (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)).2
        (by simpa [sectionSixZOne, sectionSixZTwo, X, XNat, p] using
          hpData.2)
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
        (by exact_mod_cast hsReduced.1)
    have hrqLog : normalizedPrimeLog XNat r <=
        normalizedPrimeLog XNat q := by
      change Real.logb X (r : Real) <= Real.logb X (q : Real)
      exact Real.logb_le_logb_of_le hX (by exact_mod_cast hrData.1.pos)
        (by exact_mod_cast hrData.2.2)
    have hqpLog : normalizedPrimeLog XNat q <=
        normalizedPrimeLog XNat p := by
      change Real.logb X (q : Real) <= Real.logb X (p : Real)
      exact Real.logb_le_logb_of_le hX (by exact_mod_cast hqData.1.pos)
        (by exact_mod_cast hthreshold.1)
    have hproductLowerLog : sectionSixThetaTwo epsilon <
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero]
      apply (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).2
      simpa [sectionSixZThree, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hpiece.2.1
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
    have hfullCapNat :
        sectionSixFirstLowCentralSmallTripleProduct index.1 * s * s <=
          XNat :=
      (sectionSixFirstLowCentralSmall_le_tripleTerminalThreshold_iff
        hpData.1 hqData.1 hrData.1 hsData.1).1 hsReduced.2
    have hfullCapLog :
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q +
            normalizedPrimeLog XNat r + 2 * normalizedPrimeLog XNat s <= 1 := by
      rw [sectionSixFirstLowCentralSmall_normalizedFullProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero hrData.1.ne_zero hsData.1.ne_zero]
      apply (Real.logb_le_iff_le_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpData.1.pos hqData.1.pos)
            hrData.1.pos) hsData.1.pos) hsData.1.pos)).2
      norm_num only [Real.rpow_one]
      have hcapReal : (((p * q * r * s * s : Nat) : Real) <= XNat) := by
        exact_mod_cast hfullCapNat
      simpa [sectionSixFirstLowCentralSmallTripleProduct,
        X, XNat, p, q, r, s, Nat.mul_assoc] using hcapReal
    have hcleanData :
        (((p * r : Nat) : Real) < X ^ sectionSixThetaOne epsilon ∨
            X ^ sectionSixThetaTwo epsilon < ((p * r : Nat) : Real)) ∧
          (((p * s : Nat) : Real) < X ^ sectionSixThetaOne epsilon ∨
            X ^ sectionSixThetaTwo epsilon < ((p * s : Nat) : Real)) ∧
          (((q * r : Nat) : Real) < X ^ sectionSixThetaOne epsilon ∨
            X ^ sectionSixThetaTwo epsilon < ((q * r : Nat) : Real)) ∧
          (((q * s : Nat) : Real) < X ^ sectionSixThetaOne epsilon ∨
            X ^ sectionSixThetaTwo epsilon < ((q * s : Nat) : Real)) ∧
          (((r * s : Nat) : Real) < X ^ sectionSixThetaOne epsilon ∨
            X ^ sectionSixThetaTwo epsilon < ((r * s : Nat) : Real)) := by
      simpa [sectionSixFirstLowCentralSmallCleanQuadrupleMem,
        sectionSixZTwo, sectionSixZThree, X, XNat, p, q, r, s] using hquad.2
    have hprNot :=
      (sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff hX
        hpData.1 hrData.1).2 hcleanData.1
    have hpsNot :=
      (sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff hX
        hpData.1 hsData.1).2 hcleanData.2.1
    have hqrNot :=
      (sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff hX
        hqData.1 hrData.1).2 hcleanData.2.2.1
    have hqsNot :=
      (sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff hX
        hqData.1 hsData.1).2 hcleanData.2.2.2.1
    have hrsNot :=
      (sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff hX
        hrData.1 hsData.1).2 hcleanData.2.2.2.2
    refine ⟨hpBroad, hqBroad, hrBroad, hsBroad, ?_⟩
    simp only [sectionSixFirstLowCentralSmallQuadrupleRegion, Set.mem_setOf_eq]
    exact ⟨hsLog, hsrLog, hrqLog, hqpLog, hpLog.2, hproductLowerLog,
      hsquareLog, hfullCapLog, hprNot, hpsNot, hqrNot, hqsNot, hrsNot⟩
  · rintro ⟨hpBroad, hqBroad, hrBroad, hsBroad, hregion⟩
    have hpDataBroad := mem_sievePrimeInterval.mp hpBroad
    have hqDataBroad := mem_sievePrimeInterval.mp hqBroad
    have hrDataBroad := mem_sievePrimeInterval.mp hrBroad
    have hsDataBroad := mem_sievePrimeInterval.mp hsBroad
    have hregionData :
        sectionSixThetaGap epsilon < normalizedPrimeLog XNat s ∧
          normalizedPrimeLog XNat s <= normalizedPrimeLog XNat r ∧
          normalizedPrimeLog XNat r <= normalizedPrimeLog XNat q ∧
          normalizedPrimeLog XNat q <= normalizedPrimeLog XNat p ∧
          normalizedPrimeLog XNat p <= sectionSixThetaOne epsilon ∧
          sectionSixThetaTwo epsilon <
            normalizedPrimeLog XNat p + normalizedPrimeLog XNat q ∧
          normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q <
            1 - sectionSixThetaOne epsilon ∧
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q +
              normalizedPrimeLog XNat r + 2 * normalizedPrimeLog XNat s <= 1 ∧
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat r ∉
            Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat s ∉
            Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
          normalizedPrimeLog XNat q + normalizedPrimeLog XNat r ∉
            Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
          normalizedPrimeLog XNat q + normalizedPrimeLog XNat s ∉
            Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
          normalizedPrimeLog XNat r + normalizedPrimeLog XNat s ∉
            Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) := by
      simpa [sectionSixFirstLowCentralSmallQuadrupleRegion,
        XNat, p, q, r, s] using hregion
    rcases hregionData with
      ⟨hsLowerLog, hsrLog, hrqLog, hqpLog, hpUpperLog,
        hpqLowerLog, hpqqLog, hfullCapLog,
        hprNot, hpsNot, hqrNot, hqsNot, hrsNot⟩
    have hsPos : (0 : Real) < s := by exact_mod_cast hsDataBroad.1.pos
    have hrPos : (0 : Real) < r := by exact_mod_cast hrDataBroad.1.pos
    have hqPos : (0 : Real) < q := by exact_mod_cast hqDataBroad.1.pos
    have hpPos : (0 : Real) < p := by exact_mod_cast hpDataBroad.1.pos
    have hsr : s <= r := by
      exact_mod_cast (Real.logb_le_logb hX hsPos hrPos).1 hsrLog
    have hrq : r <= q := by
      exact_mod_cast (Real.logb_le_logb hX hrPos hqPos).1 hrqLog
    have hqp : q <= p := by
      exact_mod_cast (Real.logb_le_logb hX hqPos hpPos).1 hqpLog
    have hpRange : X ^ sectionSixThetaGap epsilon < (p : Real) ∧
        (p : Real) <= X ^ sectionSixThetaOne epsilon := by
      simpa [X, XNat, p] using hpDataBroad.2
    have hsLower : X ^ sectionSixThetaGap epsilon < (s : Real) :=
      (Real.lt_logb_iff_rpow_lt hX hsPos).1 hsLowerLog
    have hrLower : X ^ sectionSixThetaGap epsilon < (r : Real) :=
      hsLower.trans_le (by exact_mod_cast hsr)
    have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) :=
      hrLower.trans_le (by exact_mod_cast hrq)
    have hqLogLower : sectionSixThetaGap epsilon <
        normalizedPrimeLog XNat q := by
      change sectionSixThetaGap epsilon < Real.logb X (q : Real)
      exact (Real.lt_logb_iff_rpow_lt hX hqPos).2 hqLower
    have hpqUpperLog : normalizedPrimeLog XNat p +
        normalizedPrimeLog XNat q < 1 - sectionSixThetaTwo epsilon := by
      simp only [sectionSixThetaGap, sectionSixThetaOne,
        sectionSixThetaTwo] at hqLogLower hpqqLog ⊢
      linarith
    have hproductLower : sectionSixZThree epsilon X <
        (sectionSixFirstPairProduct index.1.1 : Real) := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpDataBroad.1.ne_zero hqDataBroad.1.ne_zero] at hpqLowerLog
      have hraw := (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos hpDataBroad.1.pos hqDataBroad.1.pos)).1
          hpqLowerLog
      simpa [sectionSixZThree, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hproductUpper :
        (sectionSixFirstPairProduct index.1.1 : Real) <
          sectionSixZFive epsilon X := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpDataBroad.1.ne_zero hqDataBroad.1.ne_zero] at hpqUpperLog
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpDataBroad.1.pos hqDataBroad.1.pos)).1
          hpqUpperLog
      simpa [sectionSixZFive, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hsquare : (sectionSixFirstPairSquareProduct index.1.1 : Real) <
        sectionSixZSix epsilon X := by
      rw [sectionSixFirst_normalizedPairSquareProduct_eq
        hpDataBroad.1.ne_zero hqDataBroad.1.ne_zero] at hpqqLog
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpDataBroad.1.pos hqDataBroad.1.pos)
            hqDataBroad.1.pos)).1 hpqqLog
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
    have hpairCap : p * q * q <= XNat := by
      have hcapReal : ((p * q * q : Nat) : Real) <= (XNat : Real) := by
        simpa [sectionSixFirstPairSquareProduct, X, XNat, p, q] using
          (hsquare.trans hzSixLtX).le
      exact_mod_cast hcapReal
    have hfullCap : p * q * r * s * s <= XNat := by
      rw [sectionSixFirstLowCentralSmall_normalizedFullProduct_eq
        hpDataBroad.1.ne_zero hqDataBroad.1.ne_zero
        hrDataBroad.1.ne_zero hsDataBroad.1.ne_zero] at hfullCapLog
      have hraw := (Real.logb_le_iff_le_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpDataBroad.1.pos
            hqDataBroad.1.pos) hrDataBroad.1.pos) hsDataBroad.1.pos)
              hsDataBroad.1.pos)).1 hfullCapLog
      norm_num only [Real.rpow_one] at hraw
      have hcapReal : (((p * q * r * s * s : Nat) : Real) <= XNat) := by
        simpa only [X, XNat] using hraw
      exact_mod_cast hcapReal
    have hlow : index.1.1 ∈
        sectionSixFirstLowStrictIndices epsilon length := by
      apply mem_sectionSixFirstSecondRepeatedIndices.mpr
      constructor
      · apply mem_sievePrimeInterval.mpr
        simpa [sectionSixZOne, sectionSixZTwo,
          X, XNat, p] using And.intro hpDataBroad.1 hpRange
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hqDataBroad.1, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, q] using hqLower
        · exact (sectionSixFirst_direct_pairThreshold_iff
            hpDataBroad.1 hqDataBroad.1).2
              ⟨hqp, by simpa only [XNat, p, q] using hpairCap⟩
    have hpair : index.1.1 ∈
        sectionSixFirstPairPieceIndices epsilon length .lowCentralSmall := by
      apply Finset.mem_filter.mpr
      constructor
      · simp [sectionSixFirstStrictIndices, hlow]
      · simpa [sectionSixFirstPairMem, X, XNat] using
          And.intro hlow
            (And.intro hproductLower (And.intro hproductUpper hsquare))
    have htriple : index.1 ∈
        sectionSixFirstLowCentralSmallTripleIndices epsilon length := by
      apply mem_sectionSixFirstLowCentralSmallTripleIndices.mpr
      refine ⟨hpair, mem_sievePrimeInterval.mpr ⟨hrDataBroad.1, ?_, ?_⟩⟩
      · simpa [sectionSixZOne, X, XNat, r] using hrLower
      · exact_mod_cast hrq
    have hraw : index ∈
        sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length := by
      apply mem_sectionSixFirstLowCentralSmallRawQuadrupleIndices.mpr
      refine ⟨htriple, mem_sievePrimeInterval.mpr ⟨hsDataBroad.1, ?_, ?_⟩⟩
      · simpa [sectionSixZOne, X, XNat, s] using hsLower
      · unfold sectionSixFirstLowCentralSmallTripleReducedThreshold
        rw [le_min_iff]
        refine ⟨by exact_mod_cast hsr, ?_⟩
        apply (sectionSixFirstLowCentralSmall_le_tripleTerminalThreshold_iff
          hpDataBroad.1 hqDataBroad.1 hrDataBroad.1 hsDataBroad.1).2
        simpa [sectionSixFirstLowCentralSmallTripleProduct,
          sectionSixFirstPairProduct,
          XNat, p, q, r, s, Nat.mul_assoc] using hfullCap
    have hclean : sectionSixFirstLowCentralSmallCleanQuadrupleMem
        epsilon length index := by
      unfold sectionSixFirstLowCentralSmallCleanQuadrupleMem
      dsimp only
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [sectionSixZTwo, sectionSixZThree, X, XNat, p, r] using
          (sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff hX
            hpDataBroad.1 hrDataBroad.1).1 hprNot
      · simpa [sectionSixZTwo, sectionSixZThree, X, XNat, p, s] using
          (sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff hX
            hpDataBroad.1 hsDataBroad.1).1 hpsNot
      · simpa [sectionSixZTwo, sectionSixZThree, X, XNat, q, r] using
          (sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff hX
            hqDataBroad.1 hrDataBroad.1).1 hqrNot
      · simpa [sectionSixZTwo, sectionSixZThree, X, XNat, q, s] using
          (sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff hX
            hqDataBroad.1 hsDataBroad.1).1 hqsNot
      · simpa [sectionSixZTwo, sectionSixZThree, X, XNat, r, s] using
          (sectionSixFirstLowCentralSmall_product_not_mem_Icc_iff hX
            hrDataBroad.1 hsDataBroad.1).1 hrsNot
    exact mem_sectionSixFirstLowCentralSmallQuadrupleIndices.mpr ⟨hraw, hclean⟩

/-- The exact clean nested carrier is the normalized fourfold carrier, with no
symmetry or multiplicity factor. -/
theorem
    sectionSixFirstLowCentralSmallQuadrupleIndices_map_eq_normalizedPrimeLogFourfoldIndices
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstLowCentralSmallQuadrupleIndices epsilon length).map
        sectionSixFirstLowCentralSmallQuadrupleNestedEquiv.toEmbedding =
      normalizedPrimeLogFourfoldIndices
        (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)
        (10 ^ length)
        (sectionSixFirstLowCentralSmallQuadrupleRegion epsilon) := by
  classical
  ext quadruple
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstLowCentralSmallQuadruple_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro hquadruple
    let index : SectionSixFirstLowCentralSmallQuadrupleIndex :=
      sectionSixFirstLowCentralSmallQuadrupleNestedEquiv.symm quadruple
    have hinverse : sectionSixFirstLowCentralSmallQuadrupleNestedEquiv index =
        quadruple :=
      sectionSixFirstLowCentralSmallQuadrupleNestedEquiv.apply_symm_apply
        quadruple
    refine ⟨index, (sectionSixFirstLowCentralSmallQuadruple_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    simpa only [hinverse] using hquadruple

end

end PrimesRestrictedDigits
