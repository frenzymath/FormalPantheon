import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogTriple
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowCarrierData
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeContinuationBuchstab
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeLedger
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Normalized carrier for the low central-large below term

This file maps the exact dependent continuation index `((p,q),r)` directly to the
left-associated analytic coordinate order `((u,v),w)`. The image equality has coefficient one
and retains every weak finite endpoint.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.10).
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem
    sectionSixFirstLowCentralLargeContinuationNatTriple_mem_iff
    {a b : Real} {X : Nat} {region : Set ((Real × Real) × Real)}
    (index : SectionSixFirstPairContinuationIndex) :
    sectionSixFirstLowCentralLargeContinuationNatTriple index ∈
        normalizedPrimeLogTripleIndices a b X region ↔
      index.1.1 ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b) ∧
        index.1.2 ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b) ∧
        index.2 ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b) ∧
        ((normalizedPrimeLog X index.1.1,
          normalizedPrimeLog X index.1.2),
          normalizedPrimeLog X index.2) ∈ region := by
  classical
  simp only [normalizedPrimeLogTripleIndices,
    sectionSixFirstLowCentralLargeContinuationNatTriple,
    Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  tauto

theorem sectionSixFirst_normalizedTripleSquareProduct_eq
    {X p q r : Nat} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    normalizedPrimeLog X p + normalizedPrimeLog X q +
        2 * normalizedPrimeLog X r =
      Real.logb (X : Real) ((p * q * r * r : Nat) : Real) := by
  change Real.logb (X : Real) (p : Real) +
      Real.logb (X : Real) (q : Real) +
        2 * Real.logb (X : Real) (r : Real) =
    Real.logb (X : Real) ((p * q * r * r : Nat) : Real)
  norm_num only [Nat.cast_mul]
  rw [Real.logb_mul, Real.logb_mul, Real.logb_mul]
  · ring
  · exact_mod_cast hp
  · exact_mod_cast hq
  · exact_mod_cast mul_ne_zero hp hq
  · exact_mod_cast hr
  · exact_mod_cast mul_ne_zero (mul_ne_zero hp hq) hr
  · exact_mod_cast hr

private theorem sectionSixFirstLowCentralLargeBelow_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstPairContinuationIndex) :
    index ∈ sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length .below ↔
      sectionSixFirstLowCentralLargeContinuationNatTriple index ∈
        normalizedPrimeLogTripleIndices
          (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
          (sectionSixFirstLowCentralLargeBelowRegion epsilon) := by
  classical
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
  have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  rw [sectionSixFirstLowCentralLargeContinuationNatTriple_mem_iff]
  constructor
  · intro hindex
    have hpiece :=
      mem_sectionSixFirstLowCentralLargeContinuationPieceIndices.mp hindex
    have hcontinuation :=
      mem_sectionSixFirstLowCentralLargeContinuationIndices.mp hpiece.1
    have hpqFiltered := Finset.mem_filter.mp hcontinuation.1
    have hpqPiece :
        index.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
          sectionSixZThree epsilon X <
              (sectionSixFirstPairProduct index.1 : Real) ∧
            (sectionSixFirstPairProduct index.1 : Real) <
                sectionSixZFive epsilon X ∧
              sectionSixZSix epsilon X <=
                (sectionSixFirstPairSquareProduct index.1 : Real) := by
      simpa [sectionSixFirstPairMem, X, XNat] using hpqFiltered.2
    have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpqPiece.1
    have hpData := mem_sievePrimeInterval.mp hpqData.1
    have hqData := mem_sievePrimeInterval.mp hpqData.2
    have hrData := mem_sievePrimeInterval.mp hcontinuation.2
    have hpairThreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hpData.1 hqData.1).1
        hqData.2.2
    have hstrict := sectionSixFirstLowCentralLargeBelow_strict_order
      epsilon hepsilon hepsilonSmall hlength hindex
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
      · have hqp : (q : Real) <= p := by
          exact_mod_cast hpairThreshold.1
        exact hqp.trans (mem_sievePrimeInterval.mp hpBroad).2.2
    have hrBroad :
        r ∈ sievePrimeInterval (X ^ sectionSixThetaGap epsilon)
          (X ^ (1 / 2 : Real)) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨by simpa [r] using hrData.1, ?_, ?_⟩
      · have hqLower := (mem_sievePrimeInterval.mp hqBroad).2.1
        exact hqLower.trans (by exact_mod_cast hstrict.1)
      · have hrp : (r : Real) < p := by exact_mod_cast hstrict.2
        exact hrp.le.trans (mem_sievePrimeInterval.mp hpBroad).2.2
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
        (by exact_mod_cast hpairThreshold.1)
    have hproductEq := sectionSixFirst_normalizedPairProduct_eq (X := XNat)
      hpData.1.ne_zero hqData.1.ne_zero
    have hsquareEq := sectionSixFirst_normalizedPairSquareProduct_eq
      (X := XNat) hpData.1.ne_zero hqData.1.ne_zero
    have hproductLower : sectionSixThetaTwo epsilon <
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q := by
      rw [add_comm, hproductEq]
      apply (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).2
      simpa [sectionSixZThree, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hpqPiece.2.1
    have hproductUpper :
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q <
          1 - sectionSixThetaTwo epsilon := by
      rw [add_comm, hproductEq]
      apply (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).2
      simpa [sectionSixZFive, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hpqPiece.2.2.1
    have hsquareLower : 1 - sectionSixThetaOne epsilon <=
        normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q := by
      rw [hsquareEq]
      apply (Real.le_logb_iff_rpow_le hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).2
      simpa [sectionSixZSix, sectionSixFirstPairSquareProduct,
        X, XNat, p, q, Nat.cast_mul] using hpqPiece.2.2.2
    have hsquareUpper :
        normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q <= 1 := by
      rw [hsquareEq]
      apply (Real.logb_le_iff_le_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).2
      norm_num only [Real.rpow_one]
      have hcapReal : (((p * q * q : Nat) : Real) <= X) := by
        have hcapNat : p * q * q <= XNat := by
          simpa only [p, q, XNat] using hpairThreshold.2
        change (((p * q * q : Nat) : Real) <= (XNat : Real))
        exact_mod_cast hcapNat
      simpa only [XNat, p, q] using hcapReal
    have hqrLog :
        normalizedPrimeLog XNat q < normalizedPrimeLog XNat r := by
      change Real.logb X (q : Real) < Real.logb X (r : Real)
      exact Real.logb_lt_logb hX (by exact_mod_cast hqData.1.pos)
        (by exact_mod_cast hstrict.1)
    have htripleCap :
        normalizedPrimeLog XNat p + normalizedPrimeLog XNat q +
            2 * normalizedPrimeLog XNat r <= 1 := by
      rw [sectionSixFirst_normalizedTripleSquareProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero hrData.1.ne_zero]
      apply (Real.logb_le_iff_le_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos (Nat.mul_pos hpData.1.pos hqData.1.pos)
            hrData.1.pos) hrData.1.pos)).2
      norm_num only [Real.rpow_one]
      have hcap := (sectionSixFirstPair_le_terminalThreshold_iff
        hpData.1 hqData.1 hrData.1).1 hrData.2.2
      have hcapReal : (((p * q * r * r : Nat) : Real) <= X) := by
        have hcapNat : p * q * r * r <= XNat := by
          simpa only [p, q, r, XNat, sectionSixFirstPairProduct] using hcap
        change (((p * q * r * r : Nat) : Real) <= (XNat : Real))
        exact_mod_cast hcapNat
      simpa only [XNat, p, q, r, sectionSixFirstPairProduct] using hcapReal
    have hbelowLog :
        normalizedPrimeLog XNat q + normalizedPrimeLog XNat r <
          sectionSixThetaOne epsilon := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hqData.1.ne_zero hrData.1.ne_zero]
      apply (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hqData.1.pos hrData.1.pos)).2
      simpa [sectionSixZTwo, X, XNat, q, r, Nat.cast_mul,
        sectionSixFirstLowCentralLargeContinuationMem] using hpiece.2
    refine ⟨by simpa only [X, XNat, p] using hpBroad,
      by simpa only [X, XNat, q] using hqBroad,
      by simpa only [X, XNat, r] using hrBroad, ?_⟩
    have hsquareLower' : 1 <=
        normalizedPrimeLog XNat p + 2 * normalizedPrimeLog XNat q +
          sectionSixThetaOne epsilon := by
      linarith
    simpa [sectionSixFirstLowCentralLargeBelowRegion, XNat, p, q, r] using
      ⟨hqLogLower, hlogOrder, hpLog.2, hproductLower, hproductUpper,
        hsquareLower', hsquareUpper, hqrLog, htripleCap, hbelowLog⟩
  · rintro ⟨hpBroad, hqBroad, hrBroad, hregion⟩
    have hpData := mem_sievePrimeInterval.mp hpBroad
    have hqData := mem_sievePrimeInterval.mp hqBroad
    have hrData := mem_sievePrimeInterval.mp hrBroad
    rcases hregion with
      ⟨hqLogLower, hlogOrder, hpLogUpper, hproductLower,
        hproductUpper, hsquareLower, hsquareUpper, hqrLog,
        htripleCap, hbelowLog⟩
    have hpLowLog : normalizedPrimeLog XNat p ∈
        Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon) := by
      have hpBroadLog :=
        (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1
          (sectionSixThetaGap epsilon) (1 / 2 : Real)).2
          (by simpa [X, XNat, p] using hpData.2)
      exact ⟨hpBroadLog.1, by simpa only [XNat, p] using hpLogUpper⟩
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
    have hpairCap : p * q * q <= XNat := by
      rw [sectionSixFirst_normalizedPairSquareProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero] at hsquareUpper
      have hraw := (Real.logb_le_iff_le_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).1
        hsquareUpper
      norm_num only [Real.rpow_one] at hraw
      have hraw' : (((p * q * q : Nat) : Real) <= (XNat : Real)) := by
        simpa only [p, q, X, XNat] using hraw
      exact_mod_cast hraw'
    have hlow : index.1 ∈ sectionSixFirstLowStrictIndices
        epsilon length := by
      apply mem_sectionSixFirstSecondRepeatedIndices.mpr
      constructor
      · apply mem_sievePrimeInterval.mpr
        simpa [sectionSixZOne, sectionSixZTwo, X, XNat, p] using
          And.intro hpData.1 hpLowRange
      · apply mem_sievePrimeInterval.mpr
        refine ⟨hqData.1, ?_, ?_⟩
        · simpa [sectionSixZOne, X, XNat, q] using hqData.2.1
        · exact (sectionSixFirst_direct_pairThreshold_iff
            hpData.1 hqData.1).2 ⟨hqp, by simpa only [XNat] using hpairCap⟩
    have hproductEq := sectionSixFirst_normalizedPairProduct_eq (X := XNat)
      hpData.1.ne_zero hqData.1.ne_zero
    have hsquareEq := sectionSixFirst_normalizedPairSquareProduct_eq
      (X := XNat) hpData.1.ne_zero hqData.1.ne_zero
    have hproductLowerRaw : sectionSixZThree epsilon X <
        (sectionSixFirstPairProduct index.1 : Real) := by
      rw [add_comm, hproductEq] at hproductLower
      have hraw := (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).1 hproductLower
      simpa [sectionSixZThree, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hproductUpperRaw : (sectionSixFirstPairProduct index.1 : Real) <
        sectionSixZFive epsilon X := by
      rw [add_comm, hproductEq] at hproductUpper
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).1 hproductUpper
      simpa [sectionSixZFive, sectionSixFirstPairProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hsquareLowerRaw : sectionSixZSix epsilon X <=
        (sectionSixFirstPairSquareProduct index.1 : Real) := by
      rw [hsquareEq] at hsquareLower
      have hraw := (Real.le_logb_iff_rpow_le hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos hpData.1.pos hqData.1.pos) hqData.1.pos)).1
        hsquareLower
      simpa [sectionSixZSix, sectionSixFirstPairSquareProduct,
        X, XNat, p, q, Nat.cast_mul] using hraw
    have hpqPiece : index.1 ∈ sectionSixFirstPairPieceIndices
        epsilon length .lowCentralLarge := by
      apply Finset.mem_filter.mpr
      constructor
      · simp [sectionSixFirstStrictIndices, hlow]
      · change index.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
          sectionSixZThree epsilon (((10 ^ length : Nat) : Real)) <
              (sectionSixFirstPairProduct index.1 : Real) ∧
            (sectionSixFirstPairProduct index.1 : Real) <
                sectionSixZFive epsilon (((10 ^ length : Nat) : Real)) ∧
              sectionSixZSix epsilon (((10 ^ length : Nat) : Real)) <=
                (sectionSixFirstPairSquareProduct index.1 : Real)
        exact ⟨hlow, by simpa only [X, XNat] using hproductLowerRaw,
          by simpa only [X, XNat] using hproductUpperRaw,
          by simpa only [X, XNat] using hsquareLowerRaw⟩
    have hqr : q < r := by
      change Real.logb X (q : Real) < Real.logb X (r : Real) at hqrLog
      exact_mod_cast (Real.logb_lt_logb_iff hX
        (by exact_mod_cast hqData.1.pos)
        (by exact_mod_cast hrData.1.pos)).1 hqrLog
    have htripleRaw : p * q * r * r <= XNat := by
      rw [sectionSixFirst_normalizedTripleSquareProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero hrData.1.ne_zero] at htripleCap
      have hraw := (Real.logb_le_iff_le_rpow hX (by
        exact_mod_cast Nat.mul_pos
          (Nat.mul_pos (Nat.mul_pos hpData.1.pos hqData.1.pos)
            hrData.1.pos) hrData.1.pos)).1 htripleCap
      norm_num only [Real.rpow_one] at hraw
      have hraw' : (((p * q * r * r : Nat) : Real) <= (XNat : Real)) := by
        simpa only [p, q, r, X, XNat] using hraw
      exact_mod_cast hraw'
    have hrContinuation : r ∈ sievePrimeInterval (q : Real)
        (sectionSixFirstPairTerminalThreshold length index.1) := by
      apply mem_sievePrimeInterval.mpr
      refine ⟨hrData.1, by exact_mod_cast hqr, ?_⟩
      apply (sectionSixFirstPair_le_terminalThreshold_iff
        hpData.1 hqData.1 hrData.1).2
      simpa only [p, q, r, sectionSixFirstPairProduct] using htripleRaw
    have hbelowRaw : ((q * r : Nat) : Real) < sectionSixZTwo epsilon X := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hqData.1.ne_zero hrData.1.ne_zero] at hbelowLog
      have hraw := (Real.logb_lt_iff_lt_rpow hX (by
        exact_mod_cast Nat.mul_pos hqData.1.pos hrData.1.pos)).1 hbelowLog
      simpa [sectionSixZTwo, X, XNat, q, r, Nat.cast_mul] using hraw
    apply mem_sectionSixFirstLowCentralLargeContinuationPieceIndices.mpr
    constructor
    · apply mem_sectionSixFirstLowCentralLargeContinuationIndices.mpr
      exact ⟨hpqPiece, by simpa only [q, r] using hrContinuation⟩
    · simpa [sectionSixFirstLowCentralLargeContinuationMem, X, XNat, q, r]
        using hbelowRaw

theorem image_sectionSixFirstLowCentralLargeBelowContinuationIndices
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length .below).image
        sectionSixFirstLowCentralLargeContinuationNatTriple =
      normalizedPrimeLogTripleIndices
        (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
        (sectionSixFirstLowCentralLargeBelowRegion epsilon) := by
  classical
  ext triple
  rw [Finset.mem_image]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstLowCentralLargeBelow_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro htriple
    let index : SectionSixFirstPairContinuationIndex :=
      ⟨⟨triple.1.1, triple.1.2⟩, triple.2⟩
    have hinverse :
        sectionSixFirstLowCentralLargeContinuationNatTriple index = triple := by
      rcases triple with ⟨⟨p, q⟩, r⟩
      rfl
    refine ⟨index, (sectionSixFirstLowCentralLargeBelow_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    rw [hinverse]
    exact htriple

end

end PrimesRestrictedDigits
