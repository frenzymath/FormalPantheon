import PrimesRestrictedDigits.BasicEstimates.PrimeDistribution
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairHighCarriers

/-!
# Finite bridges for the first direct pair pieces

This file reindexes the three strict pair pieces treated directly by the Buchstab estimate and
identifies their raw main and remainder sums. The log-square remainder estimate is
piece-generic and is also reused by the low central-large terminal estimate.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 140--141 and 145, Eqs. (6.7), (6.14), and
(6.15).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def sectionSixFirstPairBuchstabMainSum
    (epsilon : Real) (length : Nat)
    (piece : SectionSixFirstPairPiece) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length piece,
    buchstabFunction
        (Real.log (X / (sectionSixFirstPairProduct index : Real)) /
          Real.log (index.2 : Real)) /
      ((index.1 : Real) * (index.2 : Real) *
        Real.log (index.2 : Real))

noncomputable def sectionSixFirstPairRoughErrorSum
    (epsilon : Real) (length : Nat)
    (piece : SectionSixFirstPairPiece) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length piece,
    1 / ((index.1 : Real) * (index.2 : Real) *
      Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2)

def IsSectionSixFirstDirectPairPiece
    (piece : SectionSixFirstPairPiece) : Prop :=
  piece = .lowFar ∨ piece = .highFar ∨ piece = .highCentralLarge

private theorem sectionSixFirstDirectPair_indexData
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {piece : SectionSixFirstPairPiece}
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length piece) :
    index.1.Prime ∧ index.2.Prime ∧
      ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon < index.1 ∧
      ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon < index.2 ∧
      index.2 <= index.1 ∧ index.1 * index.2 * index.2 <= 10 ^ length := by
  classical
  have hstrict : index ∈ sectionSixFirstStrictIndices epsilon length :=
    (Finset.mem_filter.mp hindex).1
  rw [sectionSixFirstStrictIndices, Finset.mem_union] at hstrict
  rcases hstrict with hlow | hhigh
  · have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hlow
    have hpData := mem_sievePrimeInterval.mp hdata.1
    have hqData := mem_sievePrimeInterval.mp hdata.2
    have hthreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hpData.1 hqData.1).1
        hqData.2.2
    exact ⟨hpData.1, hqData.1,
      by simpa [sectionSixZOne] using hpData.2.1,
      by simpa [sectionSixZOne] using hqData.2.1,
      hthreshold.1, hthreshold.2⟩
  · have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hhigh
    have hpData := mem_sievePrimeInterval.mp hdata.1
    have hqData := mem_sievePrimeInterval.mp hdata.2
    have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
      exact_mod_cast sectionSixFirst_direct_hXNat hlength
    have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
    have hthreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hpData.1 hqData.1).1
        hqData.2.2
    exact ⟨hpData.1, hqData.1,
      by simpa [sectionSixZOne] using
        (horder.1.trans horder.2.1 |>.trans hpData.2.1),
      by simpa [sectionSixZOne] using hqData.2.1,
      hthreshold.1, hthreshold.2⟩

private theorem sectionSixFirstDirectPair_roughSummand_le
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {piece : SectionSixFirstPairPiece}
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length piece) :
    let X : Real := ((10 ^ length : Nat) : Real)
    1 / ((index.1 : Real) * (index.2 : Real) *
        Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2) <=
      (Real.log (index.1 : Real) / (index.1 : Real)) *
          (Real.log (index.2 : Real) / (index.2 : Real)) /
        (sectionSixThetaGap epsilon ^ 4 * Real.log X ^ 4) := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let p : Nat := index.1
  let q : Nat := index.2
  let Y : Real := X / ((p * q : Nat) : Real)
  have hdata := sectionSixFirstDirectPair_indexData
    hepsilon hepsilonSmall hlength hindex
  have hpPrime : p.Prime := by simpa only [p] using hdata.1
  have hqPrime : q.Prime := by simpa only [q] using hdata.2.1
  have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hqPrime.pos
  have hpNe : (p : Real) ≠ 0 := hpPos.ne'
  have hqNe : (q : Real) ≠ 0 := hqPos.ne'
  have hXNat : 1 < XNat := by
    simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hgap : 0 < gap := by
    simpa only [gap] using (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hscale : 0 < gap * Real.log X := mul_pos hgap hlogX
  have hpLower : X ^ gap < (p : Real) := by
    simpa only [X, XNat, gap, p] using hdata.2.2.1
  have hqLower : X ^ gap < (q : Real) := by
    simpa only [X, XNat, gap, q] using hdata.2.2.2.1
  have hpLogb : gap < Real.logb X (p : Real) :=
    (Real.lt_logb_iff_rpow_lt hX hpPos).2 hpLower
  have hqLogb : gap < Real.logb X (q : Real) :=
    (Real.lt_logb_iff_rpow_lt hX hqPos).2 hqLower
  have hpLog : gap * Real.log X < Real.log (p : Real) := by
    simpa only [Real.logb] using (lt_div_iff₀ hlogX).1 hpLogb
  have hqLog : gap * Real.log X < Real.log (q : Real) := by
    simpa only [Real.logb] using (lt_div_iff₀ hlogX).1 hqLogb
  have hcapReal : (p : Real) * q * q <= X := by
    have hcap := hdata.2.2.2.2.2
    simpa only [X, XNat, p, q, Nat.cast_mul] using
      (show (((index.1 * index.2 * index.2 : Nat) : Real) <=
          ((10 ^ length : Nat) : Real)) by exact_mod_cast hcap)
  have hqY : (q : Real) <= Y := by
    dsimp only [Y]
    norm_num only [Nat.cast_mul]
    apply (le_div_iff₀ (mul_pos hpPos hqPos)).2
    nlinarith
  have hYLog : gap * Real.log X <= Real.log Y := by
    exact hqLog.le.trans (Real.log_le_log hqPos hqY)
  have hAB : (gap * Real.log X) ^ 2 <=
      Real.log (p : Real) * Real.log (q : Real) := by
    rw [pow_two]
    exact mul_le_mul hpLog.le hqLog.le hscale.le
      (hscale.le.trans hpLog.le)
  have hYY : (gap * Real.log X) ^ 2 <= Real.log Y ^ 2 := by
    exact (sq_le_sq₀ hscale.le (hscale.le.trans hYLog)).2 hYLog
  have hproduct : (gap * Real.log X) ^ 4 <=
      (Real.log (p : Real) * Real.log (q : Real)) * Real.log Y ^ 2 := by
    calc
      (gap * Real.log X) ^ 4 =
          (gap * Real.log X) ^ 2 * (gap * Real.log X) ^ 2 := by ring
      _ <= (Real.log (p : Real) * Real.log (q : Real)) *
          Real.log Y ^ 2 :=
        mul_le_mul hAB hYY (sq_nonneg _)
          (mul_nonneg (hscale.le.trans hpLog.le)
            (hscale.le.trans hqLog.le))
  have hcore : 1 / Real.log Y ^ 2 <=
      (Real.log (p : Real) * Real.log (q : Real)) /
        (gap * Real.log X) ^ 4 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos (hscale.trans_le hYLog))
      (pow_pos hscale 4)).2
    simpa only [one_mul] using hproduct
  dsimp only [X, XNat, gap, p, q, Y]
  simp only [sectionSixFirstPairProduct]
  calc
    1 / ((index.1 : Real) * (index.2 : Real) *
        Real.log (((10 ^ length : Nat) : Real) /
          ((index.1 * index.2 : Nat) : Real)) ^ 2) =
      (1 / ((index.1 : Real) * (index.2 : Real))) *
        (1 / Real.log (((10 ^ length : Nat) : Real) /
          ((index.1 * index.2 : Nat) : Real)) ^ 2) := by ring
    _ <= (1 / ((index.1 : Real) * (index.2 : Real))) *
        ((Real.log (index.1 : Real) * Real.log (index.2 : Real)) /
          (sectionSixThetaGap epsilon *
            Real.log ((10 ^ length : Nat) : Real)) ^ 4) := by
      exact mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = (Real.log (index.1 : Real) / (index.1 : Real)) *
          (Real.log (index.2 : Real) / (index.2 : Real)) /
        (sectionSixThetaGap epsilon ^ 4 *
          Real.log ((10 ^ length : Nat) : Real) ^ 4) := by
      field_simp [hpNe, hqNe, hgap.ne', hlogX.ne']

private theorem sectionSixFirstPairBuchstabSummand_eq
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex)
    (hp : index.1.Prime) (hq : index.2.Prime) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    buchstabFunction
          (Real.log (X / (sectionSixFirstPairProduct index : Real)) /
            Real.log (index.2 : Real)) /
        ((index.1 : Real) * (index.2 : Real) *
          Real.log (index.2 : Real)) =
      normalizedPrimeLogWeight XNat index.2 *
          normalizedPrimeLogWeight XNat index.1 *
          sectionSixFirstPairBuchstabKernel
            (normalizedPrimeLog XNat index.2,
              normalizedPrimeLog XNat index.1) /
        Real.log X := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1
  let q : Nat := index.2
  have hXNat : 1 < XNat := by
    simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hX0 : X ≠ 0 := (zero_lt_one.trans hX).ne'
  have hp0 : (p : Real) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : Real) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hlogp : Real.log (p : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hlogq : Real.log (q : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
  have hlogProduct :
      Real.log (X / ((p * q : Nat) : Real)) =
        Real.log X - Real.log (p : Real) - Real.log (q : Real) := by
    rw [Real.log_div hX0 (by exact_mod_cast mul_ne_zero hp.ne_zero hq.ne_zero),
      Nat.cast_mul,
      Real.log_mul hp0 hq0]
    ring
  have hargument :
      Real.log (X / ((p * q : Nat) : Real)) / Real.log (q : Real) =
        (1 - normalizedPrimeLog XNat p - normalizedPrimeLog XNat q) /
          normalizedPrimeLog XNat q := by
    rw [hlogProduct]
    unfold normalizedPrimeLog
    dsimp only [X, XNat]
    field_simp [hlogX, hlogq]
  dsimp only
  simp only [sectionSixFirstPairProduct, p, q] at hargument ⊢
  rw [hargument]
  unfold normalizedPrimeLogWeight sectionSixFirstPairBuchstabKernel
    normalizedPrimeLog
  have hlogX' : Real.log ((10 ^ length : Nat) : Real) ≠ 0 := by
    simpa only [X, XNat] using hlogX
  have hlogp' : Real.log (index.1 : Real) ≠ 0 := by
    simpa only [p] using hlogp
  have hlogq' : Real.log (index.2 : Real) ≠ 0 := by
    simpa only [q] using hlogq
  dsimp only [X, XNat, p, q]
  field_simp [hlogX', hlogp', hlogq', hp0, hq0]

private theorem sectionSixFirstPairBuchstabMainSum_eq_normalized
    {epsilon : Real} {length : Nat} (hlength : 1 <= length)
    {piece : SectionSixFirstPairPiece} {region : Set (Real × Real)}
    (himage :
      (sectionSixFirstPairPieceIndices epsilon length piece).image
          sectionSixFirstNatPair =
        normalizedPrimeLogPairIndices (sectionSixThetaGap epsilon) (1 / 2)
          (10 ^ length) region) :
    sectionSixFirstPairBuchstabMainSum epsilon length piece =
      normalizedPrimeLogPairSum (sectionSixThetaGap epsilon) (1 / 2)
          (10 ^ length) region sectionSixFirstPairBuchstabKernel /
        Real.log ((10 ^ length : Nat) : Real) := by
  classical
  let indices := sectionSixFirstPairPieceIndices epsilon length piece
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hpoint : ∀ index ∈ indices,
      buchstabFunction
            (Real.log (X / (sectionSixFirstPairProduct index : Real)) /
              Real.log (index.2 : Real)) /
          ((index.1 : Real) * (index.2 : Real) *
            Real.log (index.2 : Real)) =
        normalizedPrimeLogWeight XNat index.2 *
            normalizedPrimeLogWeight XNat index.1 *
            sectionSixFirstPairBuchstabKernel
              (normalizedPrimeLog XNat index.2,
                normalizedPrimeLog XNat index.1) /
          Real.log X := by
    intro index hindex
    have hindex' : index ∈
        sectionSixFirstPairPieceIndices epsilon length piece := by
      simpa only [indices] using hindex
    unfold sectionSixFirstPairPieceIndices at hindex'
    have hstrict : index ∈ sectionSixFirstStrictIndices epsilon length :=
      (Finset.mem_filter.mp hindex').1
    rw [sectionSixFirstStrictIndices, Finset.mem_union] at hstrict
    rcases hstrict with hlow | hhigh
    · have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hlow
      exact sectionSixFirstPairBuchstabSummand_eq hlength index
        (mem_sievePrimeInterval.mp hdata.1).1
        (mem_sievePrimeInterval.mp hdata.2).1
    · have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hhigh
      exact sectionSixFirstPairBuchstabSummand_eq hlength index
        (mem_sievePrimeInterval.mp hdata.1).1
        (mem_sievePrimeInterval.mp hdata.2).1
  unfold sectionSixFirstPairBuchstabMainSum normalizedPrimeLogPairSum
  dsimp only [X, XNat, indices]
  rw [← himage, Finset.sum_image sectionSixFirstNatPair_injective.injOn,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro index hindex
  exact hpoint index hindex

theorem sectionSixFirstLowFarBuchstabMainSum_eq
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstPairBuchstabMainSum epsilon length .lowFar =
      normalizedPrimeLogPairSum (sectionSixThetaGap epsilon) (1 / 2)
          (10 ^ length) (sectionSixFirstLowFarRegion epsilon)
          sectionSixFirstPairBuchstabKernel /
        Real.log ((10 ^ length : Nat) : Real) := by
  apply sectionSixFirstPairBuchstabMainSum_eq_normalized hlength
  exact image_sectionSixFirstLowFarPairPieceIndices
    epsilon hepsilon hepsilonSmall hlength

theorem sectionSixFirstHighFarBuchstabMainSum_eq
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstPairBuchstabMainSum epsilon length .highFar =
      normalizedPrimeLogPairSum (sectionSixThetaGap epsilon) (1 / 2)
          (10 ^ length) (sectionSixFirstHighFarRegion epsilon)
          sectionSixFirstPairBuchstabKernel /
        Real.log ((10 ^ length : Nat) : Real) := by
  apply sectionSixFirstPairBuchstabMainSum_eq_normalized hlength
  exact image_sectionSixFirstHighFarPairPieceIndices
    epsilon hepsilon hepsilonSmall hlength

theorem sectionSixFirstHighCentralLargeBuchstabMainSum_eq
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstPairBuchstabMainSum epsilon length
        .highCentralLarge =
      normalizedPrimeLogPairSum (sectionSixThetaGap epsilon) (1 / 2)
          (10 ^ length) (sectionSixFirstHighCentralLargeRegion epsilon)
          sectionSixFirstPairBuchstabKernel /
        Real.log ((10 ^ length : Nat) : Real) := by
  apply sectionSixFirstPairBuchstabMainSum_eq_normalized hlength
  exact image_sectionSixFirstHighCentralLargePairPieceIndices
    epsilon hepsilon hepsilonSmall hlength

theorem sectionSixFirstPairRoughErrorSum_le
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (piece : SectionSixFirstPairPiece) :
    sectionSixFirstPairRoughErrorSum epsilon length piece <=
      (2 * Real.log 4) ^ 2 /
        (sectionSixThetaGap epsilon ^ 4 *
          Real.log ((10 ^ length : Nat) : Real) ^ 2) := by
  classical
  let indices := sectionSixFirstPairPieceIndices epsilon length piece
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let primeWeight : Nat -> Real := fun p => Real.log (p : Real) / (p : Real)
  let denominator : Real := gap ^ 4 * Real.log X ^ 4
  have hXNat : 3 <= XNat := by
    dsimp only [XNat]
    exact (by norm_num : (3 : Nat) <= 10).trans (Nat.le_pow (by omega))
  have hgap : 0 < gap := by
    simpa only [gap] using (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat.trans' (by norm_num : (1 : Nat) < 3)
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have hpoint : ∀ index ∈ indices,
      1 / ((index.1 : Real) * (index.2 : Real) *
          Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2) <=
        primeWeight index.1 * primeWeight index.2 / denominator := by
    intro index hindex
    simpa only [indices, X, XNat, gap, primeWeight, denominator] using
      sectionSixFirstDirectPair_roughSummand_le
        hepsilon hepsilonSmall hlength hindex
  have hsubset : indices.image sectionSixFirstNatPair ⊆
      (Nat.primesLE XNat).product (Nat.primesLE XNat) := by
    intro pair hpair
    rcases Finset.mem_image.mp hpair with ⟨index, hindex, rfl⟩
    have hdata := sectionSixFirstDirectPair_indexData
      hepsilon hepsilonSmall hlength (by simpa only [indices] using hindex)
    have hpLe : index.1 <= XNat := by
      apply (show index.1 <= index.1 * index.2 * index.2 by
        calc
          index.1 <= index.1 * index.2 :=
            Nat.le_mul_of_pos_right index.1 hdata.2.1.pos
          _ <= index.1 * index.2 * index.2 :=
            Nat.le_mul_of_pos_right _ hdata.2.1.pos).trans
      simpa only [XNat] using hdata.2.2.2.2.2
    have hqLe : index.2 <= XNat := hdata.2.2.2.2.1.trans hpLe
    rw [Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨Nat.mem_primesLE.mpr ⟨hqLe, hdata.2.1⟩,
      Nat.mem_primesLE.mpr ⟨hpLe, hdata.1⟩⟩
  have hweightNonneg : ∀ p ∈ Nat.primesLE XNat, 0 <= primeWeight p := by
    intro p hp
    have hpPrime := (Nat.mem_primesLE.mp hp).2
    dsimp only [primeWeight]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
      (by positivity)
  have hprimeSum := sum_prime_log_div_le_two_mul_log_four_mul_log XNat hXNat
  unfold sectionSixFirstPairRoughErrorSum
  change (∑ index ∈ indices,
      1 / ((index.1 : Real) * (index.2 : Real) *
        Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2)) <= _
  calc
    _ <= ∑ index ∈ indices,
        primeWeight index.1 * primeWeight index.2 / denominator := by
      exact Finset.sum_le_sum fun index hindex => hpoint index hindex
    _ = (∑ pair ∈ indices.image sectionSixFirstNatPair,
          primeWeight pair.1 * primeWeight pair.2) / denominator := by
      rw [← Finset.sum_div,
        Finset.sum_image sectionSixFirstNatPair_injective.injOn]
      apply congrArg (fun value : Real => value / denominator)
      apply Finset.sum_congr rfl
      intro index hindex
      dsimp only [sectionSixFirstNatPair]
      ring
    _ <= (∑ pair ∈ (Nat.primesLE XNat).product (Nat.primesLE XNat),
          primeWeight pair.1 * primeWeight pair.2) / denominator := by
      apply div_le_div_of_nonneg_right _ hdenominator.le
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro pair hpair _
      rw [Finset.product_eq_sprod, Finset.mem_product] at hpair
      exact mul_nonneg (hweightNonneg pair.1 hpair.1)
        (hweightNonneg pair.2 hpair.2)
    _ = ((∑ p ∈ Nat.primesLE XNat, primeWeight p) ^ 2) / denominator := by
      congr 1
      rw [Finset.product_eq_sprod]
      calc
        (∑ pair ∈ Nat.primesLE XNat ×ˢ Nat.primesLE XNat,
            primeWeight pair.1 * primeWeight pair.2) =
            ∑ p ∈ Nat.primesLE XNat, ∑ q ∈ Nat.primesLE XNat,
              primeWeight p * primeWeight q := Finset.sum_product _ _ _
        _ = _ := by rw [← Finset.sum_mul_sum]; ring
    _ <= (2 * Real.log 4 * Real.log X) ^ 2 / denominator := by
      apply div_le_div_of_nonneg_right _ hdenominator.le
      exact pow_le_pow_left₀ (by positivity) hprimeSum 2
    _ = (2 * Real.log 4) ^ 2 /
        (sectionSixThetaGap epsilon ^ 4 * Real.log X ^ 2) := by
      dsimp only [denominator, gap]
      field_simp [hgap.ne', hlogX.ne']

theorem sectionSixFirstDirectPairRoughErrorSum_le
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {piece : SectionSixFirstPairPiece}
    (_hpiece : IsSectionSixFirstDirectPairPiece piece) :
    sectionSixFirstPairRoughErrorSum epsilon length piece <=
      (2 * Real.log 4) ^ 2 /
        (sectionSixThetaGap epsilon ^ 4 *
          Real.log ((10 ^ length : Nat) : Real) ^ 2) :=
  sectionSixFirstPairRoughErrorSum_le
    epsilon hepsilon hepsilonSmall hlength piece

end

end PrimesRestrictedDigits
