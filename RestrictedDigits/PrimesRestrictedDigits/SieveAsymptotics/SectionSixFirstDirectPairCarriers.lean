import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogPair
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairRegions
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstPairSums

/-!
# Normalized carriers for the first direct pair pieces

This file maps the dependent strict index `(p,q)` to the analytic coordinate order `(q,p)` and
proves the exact finite carrier identities used by the first three direct Buchstab integrals.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 140--141 and 145, Eqs. (6.7), (6.14), and
(6.15).
-/

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstNatPair
    (index : SectionSixFirstStrictIndex) : Nat × Nat :=
  (index.2, index.1)

theorem sectionSixFirstNatPair_injective :
    Function.Injective sectionSixFirstNatPair := by
  rintro ⟨p, q⟩ ⟨r, s⟩ h
  have hq : q = s := congrArg Prod.fst h
  have hp : p = r := congrArg Prod.snd h
  subst r
  subst s
  rfl

theorem sectionSixFirst_direct_hXNat
    {length : Nat} (hlength : 1 <= length) :
    1 < 10 ^ length :=
  Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)

theorem sectionSixFirst_direct_pairThreshold_iff
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

theorem sectionSixFirst_normalizedPairProduct_eq
    {X p q : Nat} (hp : p ≠ 0) (hq : q ≠ 0) :
    normalizedPrimeLog X q + normalizedPrimeLog X p =
      Real.logb (X : Real) ((p * q : Nat) : Real) := by
  change Real.logb (X : Real) (q : Real) +
      Real.logb (X : Real) (p : Real) =
    Real.logb (X : Real) ((p * q : Nat) : Real)
  rw [Nat.cast_mul, Real.logb_mul]
  · ring
  · exact_mod_cast hp
  · exact_mod_cast hq

theorem sectionSixFirst_normalizedPairSquareProduct_eq
    {X p q : Nat} (hp : p ≠ 0) (hq : q ≠ 0) :
    normalizedPrimeLog X p + 2 * normalizedPrimeLog X q =
      Real.logb (X : Real) ((p * q * q : Nat) : Real) := by
  change Real.logb (X : Real) (p : Real) +
      2 * Real.logb (X : Real) (q : Real) =
    Real.logb (X : Real) ((p * q * q : Nat) : Real)
  norm_num only [Nat.cast_mul]
  rw [Real.logb_mul, Real.logb_mul]
  · ring
  · exact_mod_cast hp
  · exact_mod_cast hq
  · exact_mod_cast mul_ne_zero hp hq
  · exact_mod_cast hq

theorem sectionSixFirstNatPair_mem_normalizedPrimeLogPairIndices_iff
    {a b : Real} {X : Nat} {region : Set (Real × Real)}
    (index : SectionSixFirstStrictIndex) :
    sectionSixFirstNatPair index ∈
        normalizedPrimeLogPairIndices a b X region ↔
      index.2 ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b) ∧
        index.1 ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b) ∧
        (normalizedPrimeLog X index.2,
          normalizedPrimeLog X index.1) ∈ region := by
  classical
  simp only [normalizedPrimeLogPairIndices, sectionSixFirstNatPair,
    Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  tauto

private theorem sectionSixFirstLowFar_mem_iff
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex) :
    index ∈ sectionSixFirstPairPieceIndices epsilon length .lowFar ↔
      sectionSixFirstNatPair index ∈
        normalizedPrimeLogPairIndices (sectionSixThetaGap epsilon) (1 / 2)
          (10 ^ length) (sectionSixFirstLowFarRegion epsilon) := by
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
          sectionSixZSix epsilon X <
            (sectionSixFirstPairProduct index : Real) := by
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
    have hfarLog :
        1 - sectionSixThetaOne epsilon <
          normalizedPrimeLog XNat p + normalizedPrimeLog XNat q := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero]
      apply (Real.lt_logb_iff_rpow_lt hX (by
        exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).2
      simpa [sectionSixZSix, sectionSixFirstPairProduct, X, XNat, p, q,
        Nat.cast_mul] using hpiece.2
    refine ⟨by simpa [X, XNat, q] using hqBroad,
      by simpa [X, XNat, p] using hpBroad, ?_⟩
    simpa [sectionSixFirstLowFarRegion, XNat, p, q] using
      ⟨hqLogLower, hlogOrder, hpLog.2, hcapLog, hfarLog⟩
  · rintro ⟨hqBroad, hpBroad, hregion⟩
    have hqData := mem_sievePrimeInterval.mp hqBroad
    have hpData := mem_sievePrimeInterval.mp hpBroad
    rcases hregion with
      ⟨hqLogLower, hlogOrder, hpLogUpper, hcapLog, hfarLog⟩
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
      have hlogOrder' : Real.log (q : Real) <= Real.log (p : Real) := by
        exact (div_le_div_iff_of_pos_right hlogX).1 hlogOrder
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
    have hfar : sectionSixZSix epsilon X <
        (sectionSixFirstPairProduct index : Real) := by
      rw [add_comm, sectionSixFirst_normalizedPairProduct_eq
        hpData.1.ne_zero hqData.1.ne_zero] at hfarLog
      have hfarReal :=
        (Real.lt_logb_iff_rpow_lt hX (by
          exact_mod_cast Nat.mul_pos hpData.1.pos hqData.1.pos)).1 hfarLog
      simpa [sectionSixZSix, sectionSixFirstPairProduct, X, XNat, p, q,
        Nat.cast_mul] using hfarReal
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
    simpa [sectionSixFirstPairPieceIndices, sectionSixFirstStrictIndices,
      sectionSixFirstPairMem, X, XNat, hlow] using hfar

theorem image_sectionSixFirstLowFarPairPieceIndices
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (sectionSixFirstPairPieceIndices epsilon length .lowFar).image
        sectionSixFirstNatPair =
      normalizedPrimeLogPairIndices (sectionSixThetaGap epsilon) (1 / 2)
        (10 ^ length) (sectionSixFirstLowFarRegion epsilon) := by
  classical
  ext pair
  rw [Finset.mem_image]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (sectionSixFirstLowFar_mem_iff
      hepsilon hepsilonSmall hlength index).1 hindex
  · intro hpair
    let index : SectionSixFirstStrictIndex := ⟨pair.2, pair.1⟩
    have hinverse : sectionSixFirstNatPair index = pair := by
      rcases pair with ⟨q, p⟩
      rfl
    refine ⟨index, (sectionSixFirstLowFar_mem_iff
      hepsilon hepsilonSmall hlength index).2 ?_, hinverse⟩
    rw [hinverse]
    exact hpair

end

end PrimesRestrictedDigits
