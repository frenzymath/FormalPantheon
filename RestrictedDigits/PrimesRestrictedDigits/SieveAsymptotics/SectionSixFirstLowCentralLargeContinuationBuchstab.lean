import PrimesRestrictedDigits.BasicEstimates.PrimeDistribution
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeLedger
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Buchstab sums for the low central-large continuations

This file owns the generic raw main and error sums for all three continuation pieces. The
cubic prime-weight bound is shared by the below and above pieces.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eqs. (6.10)--(6.11).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

local instance sectionSixFirstLowCentralLargeContinuationPairMemDecidable
    (epsilon : Real) (length : Nat) (piece : SectionSixFirstPairPiece)
    (index : SectionSixFirstStrictIndex) :
    Decidable (sectionSixFirstPairMem epsilon length piece index) :=
  Classical.propDecidable _

def sectionSixFirstLowCentralLargeContinuationNatTriple
    (index : SectionSixFirstPairContinuationIndex) :
    (Nat × Nat) × Nat :=
  ((index.1.1, index.1.2), index.2)

theorem sectionSixFirstLowCentralLargeContinuationNatTriple_injective :
    Function.Injective
      sectionSixFirstLowCentralLargeContinuationNatTriple := by
  rintro ⟨⟨p, q⟩, r⟩ ⟨⟨p', q'⟩, r'⟩ h
  simp only [sectionSixFirstLowCentralLargeContinuationNatTriple,
    Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
  rfl

noncomputable def
    sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
    (epsilon : Real) (length : Nat)
    (piece : SectionSixFirstLowCentralLargeContinuationPiece) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstLowCentralLargeContinuationPieceIndices
      epsilon length piece,
    buchstabFunction
      (Real.log (X /
        ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) /
          Real.log (index.2 : Real)) /
      ((index.1.1 : Real) * (index.1.2 : Real) *
        (index.2 : Real) * Real.log (index.2 : Real))

noncomputable def
    sectionSixFirstLowCentralLargeContinuationRoughErrorSum
    (epsilon : Real) (length : Nat)
    (piece : SectionSixFirstLowCentralLargeContinuationPiece) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstLowCentralLargeContinuationPieceIndices
      epsilon length piece,
    1 / ((index.1.1 : Real) * (index.1.2 : Real) *
      (index.2 : Real) *
      Real.log (X /
        ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) ^ 2)

theorem sectionSixFirstLowCentralLargeContinuation_indexData
    {epsilon : Real} {length : Nat}
    {piece : SectionSixFirstLowCentralLargeContinuationPiece}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length piece) :
    let X : Real := ((10 ^ length : Nat) : Real)
    index.1.1.Prime ∧ index.1.2.Prime ∧ index.2.Prime ∧
      X ^ sectionSixThetaGap epsilon < (index.1.1 : Real) ∧
      X ^ sectionSixThetaGap epsilon < (index.1.2 : Real) ∧
      X ^ sectionSixThetaGap epsilon < (index.2 : Real) ∧
      index.1.1 * index.1.2 * index.2 * index.2 <= 10 ^ length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hpiece :=
    mem_sectionSixFirstLowCentralLargeContinuationPieceIndices.mp hindex
  have hcontinuation :=
    mem_sectionSixFirstLowCentralLargeContinuationIndices.mp hpiece.1
  have hrData := mem_sievePrimeInterval.mp hcontinuation.2
  have hpqFiltered := Finset.mem_filter.mp hcontinuation.1
  have hpqPiece :
      index.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
        sectionSixZThree epsilon X <
            (sectionSixFirstPairProduct index.1 : Real) ∧
          (sectionSixFirstPairProduct index.1 : Real) <
              sectionSixZFive epsilon X ∧
            sectionSixZSix epsilon X <=
              (sectionSixFirstPairSquareProduct index.1 : Real) := by
    simpa [sectionSixFirstPairMem, X] using hpqFiltered.2
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpqPiece.1
  have hpData := mem_sievePrimeInterval.mp hpqData.1
  have hqData := mem_sievePrimeInterval.mp hpqData.2
  have hcap := (sectionSixFirstPair_le_terminalThreshold_iff
    hpData.1 hqData.1 hrData.1).1 hrData.2.2
  have hrLower : X ^ sectionSixThetaGap epsilon < (index.2 : Real) := by
    have hqLower : X ^ sectionSixThetaGap epsilon < (index.1.2 : Real) := by
      simpa [sectionSixZOne, X] using hqData.2.1
    have hqr : (index.1.2 : Real) < index.2 := by
      exact_mod_cast hrData.2.1
    exact hqLower.trans hqr
  exact ⟨hpData.1, hqData.1, hrData.1,
    by simpa [sectionSixZOne, X] using hpData.2.1,
    by simpa [sectionSixZOne, X] using hqData.2.1,
    hrLower, by simpa [sectionSixFirstPairProduct, Nat.mul_assoc] using hcap⟩

/-- Every continuation index lies in the uniform parameter range used by the
one-sided Buchstab estimate.  The prime threshold excludes the terminal
zero-carrier anomaly, so no additional lower bound on `z1` is required. -/
theorem sectionSixFirstLowCentralLargeContinuation_buchstabParameter_bounds
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {piece : SectionSixFirstLowCentralLargeContinuationPiece}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length piece) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let Y : Real := X /
      ((index.1.1 * index.1.2 * index.2 : Nat) : Real)
    let t : Real := Real.log Y / Real.log (index.2 : Real)
    0 < Y ∧ 2 <= (index.2 : Real) ∧ 1 <= t ∧ t <= 400 := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1.1
  let q : Nat := index.1.2
  let r : Nat := index.2
  let Y : Real := X / ((p * q * r : Nat) : Real)
  let t : Real := Real.log Y / Real.log (r : Real)
  have hdata := sectionSixFirstLowCentralLargeContinuation_indexData hindex
  have hp : p.Prime := by simpa only [p] using hdata.1
  have hq : q.Prime := by simpa only [q] using hdata.2.1
  have hr : r.Prime := by simpa only [r] using hdata.2.2.1
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hq.pos
  have hrPos : (0 : Real) < r := by exact_mod_cast hr.pos
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hcap : p * q * r * r <= XNat := by
    simpa only [XNat, p, q, r] using hdata.2.2.2.2.2.2
  have hrY : (r : Real) <= Y := by
    dsimp only [Y]
    norm_num only [Nat.cast_mul]
    apply (le_div_iff₀ (mul_pos (mul_pos hpPos hqPos) hrPos)).2
    have hcapReal : (((p * q * r * r : Nat) : Real)) <= X := by
      dsimp only [X]
      exact_mod_cast hcap
    norm_num only [Nat.cast_mul] at hcapReal
    nlinarith
  have hY : 0 < Y := hrPos.trans_le hrY
  have hrTwo : (2 : Real) <= r := by exact_mod_cast hr.two_le
  have hlogr : 0 < Real.log (r : Real) := Real.log_pos (by linarith)
  have htOne : 1 <= t := by
    dsimp only [t]
    apply (le_div_iff₀ hlogr).2
    simpa only [one_mul] using Real.log_le_log hrPos hrY
  have hdenOne : (1 : Real) <= ((p * q * r : Nat) : Real) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero)
  have hYX : Y <= X := by
    dsimp only [Y]
    exact div_le_self (le_of_lt (zero_lt_one.trans hX)) hdenOne
  have hrLower : X ^ sectionSixThetaGap epsilon < (r : Real) := by
    simpa only [X, XNat, r] using hdata.2.2.2.2.2.1
  have hrLogb : sectionSixThetaGap epsilon < Real.logb X (r : Real) :=
    (Real.lt_logb_iff_rpow_lt hX hrPos).2 hrLower
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hrLogLower : sectionSixThetaGap epsilon * Real.log X <=
      Real.log (r : Real) :=
    ((lt_div_iff₀ hlogX).1
      (by simpa only [Real.logb] using hrLogb)).le
  have hgap400 : 1 <= 400 * sectionSixThetaGap epsilon := by
    rw [sectionSixThetaGap_eq]
    linarith
  have htFourHundred : t <= 400 := by
    dsimp only [t]
    apply (div_le_iff₀ hlogr).2
    have hlogYX := Real.log_le_log hY hYX
    have hlogXBound : Real.log X <= 400 * Real.log (r : Real) := by
      calc
        Real.log X <=
            (400 * sectionSixThetaGap epsilon) * Real.log X :=
          le_mul_of_one_le_left hlogX.le hgap400
        _ <= 400 * Real.log (r : Real) := by nlinarith
    exact hlogYX.trans hlogXBound
  simpa only [X, XNat, Y, p, q, r, t] using
    And.intro hY (And.intro hrTwo (And.intro htOne htFourHundred))

private theorem
    sectionSixFirstLowCentralLargeContinuation_roughSummand_le
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {piece : SectionSixFirstLowCentralLargeContinuationPiece}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length piece) :
    let X : Real := ((10 ^ length : Nat) : Real)
    1 / ((index.1.1 : Real) * (index.1.2 : Real) *
        (index.2 : Real) *
        Real.log (X /
          ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) ^ 2) <=
      (Real.log (index.1.1 : Real) / (index.1.1 : Real)) *
        (Real.log (index.1.2 : Real) / (index.1.2 : Real)) *
        (Real.log (index.2 : Real) / (index.2 : Real)) /
          (sectionSixThetaGap epsilon ^ 5 * Real.log X ^ 5) := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let p : Nat := index.1.1
  let q : Nat := index.1.2
  let r : Nat := index.2
  let Y : Real := X / ((p * q * r : Nat) : Real)
  have hdata := sectionSixFirstLowCentralLargeContinuation_indexData hindex
  have hp : p.Prime := by simpa only [p] using hdata.1
  have hq : q.Prime := by simpa only [q] using hdata.2.1
  have hr : r.Prime := by simpa only [r] using hdata.2.2.1
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hq.pos
  have hrPos : (0 : Real) < r := by exact_mod_cast hr.pos
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hgap : 0 < gap := by
    simpa only [gap] using (sectionSix_parameter_bounds
      hepsilon hepsilonSmall).1
  have hscale : 0 < gap * Real.log X := mul_pos hgap hlogX
  have hparameter :=
    sectionSixFirstLowCentralLargeContinuation_buchstabParameter_bounds
      hepsilon hepsilonSmall hlength hindex
  have hY : 0 < Y := by simpa only [X, XNat, Y, p, q, r] using hparameter.1
  have hlogr : 0 < Real.log (r : Real) :=
    Real.log_pos (by exact_mod_cast hr.one_lt)
  have hlogY : Real.log (r : Real) <= Real.log Y := by
    have htOne := hparameter.2.2.1
    have hlog := (le_div_iff₀ hlogr).1 htOne
    simpa only [one_mul, X, XNat, Y, p, q, r] using hlog
  have hlogYPos : 0 < Real.log Y := hlogr.trans_le hlogY
  have hpLower : X ^ gap < (p : Real) := by
    simpa only [X, XNat, gap, p] using hdata.2.2.2.1
  have hqLower : X ^ gap < (q : Real) := by
    simpa only [X, XNat, gap, q] using hdata.2.2.2.2.1
  have hrLower : X ^ gap < (r : Real) := by
    simpa only [X, XNat, gap, r] using hdata.2.2.2.2.2.1
  have logLower {s : Nat} (hsPos : (0 : Real) < s)
      (hsLower : X ^ gap < (s : Real)) :
      gap * Real.log X <= Real.log (s : Real) := by
    have hsLogb : gap < Real.logb X (s : Real) :=
      (Real.lt_logb_iff_rpow_lt hX hsPos).2 hsLower
    exact ((lt_div_iff₀ hlogX).1
      (by simpa only [Real.logb] using hsLogb)).le
  have hpLog := logLower hpPos hpLower
  have hqLog := logLower hqPos hqLower
  have hrLog := logLower hrPos hrLower
  have hYLog : gap * Real.log X <= Real.log Y := hrLog.trans hlogY
  have hpLogNonneg : 0 <= Real.log (p : Real) := hscale.le.trans hpLog
  have hqLogNonneg : 0 <= Real.log (q : Real) := hscale.le.trans hqLog
  have hrLogNonneg : 0 <= Real.log (r : Real) := hscale.le.trans hrLog
  have hlogsTwo : (gap * Real.log X) ^ 2 <=
      Real.log (p : Real) * Real.log (q : Real) := by
    rw [pow_two]
    exact mul_le_mul hpLog hqLog hscale.le hpLogNonneg
  have hlogsThree : (gap * Real.log X) ^ 3 <=
      Real.log (p : Real) * Real.log (q : Real) *
        Real.log (r : Real) := by
    rw [pow_succ]
    exact mul_le_mul hlogsTwo hrLog hscale.le
      (mul_nonneg hpLogNonneg hqLogNonneg)
  have hYTwo : (gap * Real.log X) ^ 2 <= Real.log Y ^ 2 :=
    (sq_le_sq₀ hscale.le (hscale.le.trans hYLog)).2 hYLog
  have hproduct : (gap * Real.log X) ^ 5 <=
      (Real.log (p : Real) * Real.log (q : Real) *
        Real.log (r : Real)) * Real.log Y ^ 2 := by
    calc
      (gap * Real.log X) ^ 5 =
          (gap * Real.log X) ^ 3 * (gap * Real.log X) ^ 2 := by ring
      _ <= (Real.log (p : Real) * Real.log (q : Real) *
          Real.log (r : Real)) * Real.log Y ^ 2 :=
        mul_le_mul hlogsThree hYTwo (sq_nonneg _)
          (mul_nonneg (mul_nonneg hpLogNonneg hqLogNonneg) hrLogNonneg)
  have hcore : 1 / Real.log Y ^ 2 <=
      (Real.log (p : Real) * Real.log (q : Real) *
        Real.log (r : Real)) / (gap * Real.log X) ^ 5 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hlogYPos)
      (pow_pos hscale 5)).2
    simpa only [one_mul] using hproduct
  dsimp only [X, XNat, gap, p, q, r, Y]
  calc
    1 / ((index.1.1 : Real) * (index.1.2 : Real) *
        (index.2 : Real) *
        Real.log (((10 ^ length : Nat) : Real) /
          ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) ^ 2) =
      (1 / ((index.1.1 : Real) * (index.1.2 : Real) *
        (index.2 : Real))) *
        (1 / Real.log (((10 ^ length : Nat) : Real) /
          ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) ^ 2) := by ring
    _ <= (1 / ((index.1.1 : Real) * (index.1.2 : Real) *
          (index.2 : Real))) *
        ((Real.log (index.1.1 : Real) * Real.log (index.1.2 : Real) *
          Real.log (index.2 : Real)) /
            (sectionSixThetaGap epsilon *
              Real.log ((10 ^ length : Nat) : Real)) ^ 5) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = (Real.log (index.1.1 : Real) / (index.1.1 : Real)) *
        (Real.log (index.1.2 : Real) / (index.1.2 : Real)) *
        (Real.log (index.2 : Real) / (index.2 : Real)) /
          (sectionSixThetaGap epsilon ^ 5 *
            Real.log ((10 ^ length : Nat) : Real) ^ 5) := by
      field_simp [hp.ne_zero, hq.ne_zero, hr.ne_zero, hgap.ne', hlogX.ne']

theorem sectionSixFirstLowCentralLargeContinuationRoughErrorSum_le
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    (piece : SectionSixFirstLowCentralLargeContinuationPiece) :
    sectionSixFirstLowCentralLargeContinuationRoughErrorSum
        epsilon length piece <=
      (2 * Real.log 4) ^ 3 /
        (sectionSixThetaGap epsilon ^ 5 *
          Real.log ((10 ^ length : Nat) : Real) ^ 2) := by
  classical
  let indices := sectionSixFirstLowCentralLargeContinuationPieceIndices
    epsilon length piece
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let primeWeight : Nat -> Real := fun p => Real.log (p : Real) / (p : Real)
  let denominator : Real := gap ^ 5 * Real.log X ^ 5
  let primes := Nat.primesLE XNat
  have hXNat : 3 <= XNat := by
    dsimp only [XNat]
    exact (by norm_num : (3 : Nat) <= 10).trans (Nat.le_pow (by omega))
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat.trans' (by norm_num : (1 : Nat) < 3)
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hgap : 0 < gap := by
    simpa only [gap] using
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have hpoint : ∀ index ∈ indices,
      1 / ((index.1.1 : Real) * (index.1.2 : Real) *
          (index.2 : Real) *
          Real.log (X /
            ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) ^ 2) <=
        primeWeight index.1.1 * primeWeight index.1.2 *
          primeWeight index.2 / denominator := by
    intro index hindex
    simpa only [indices, X, XNat, gap, primeWeight, denominator] using
      sectionSixFirstLowCentralLargeContinuation_roughSummand_le
        hepsilon hepsilonSmall hlength hindex
  have hsubset :
      indices.image sectionSixFirstLowCentralLargeContinuationNatTriple ⊆
        (primes.product primes).product primes := by
    intro triple htriple
    rcases Finset.mem_image.mp htriple with ⟨index, hindex, rfl⟩
    have hdata := sectionSixFirstLowCentralLargeContinuation_indexData
      (by simpa only [indices] using hindex)
    let p := index.1.1
    let q := index.1.2
    let r := index.2
    have hcap : p * q * r * r <= XNat := by
      simpa only [p, q, r, XNat] using hdata.2.2.2.2.2.2
    have hcapPos : 0 < p * q * r * r :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdata.1.pos hdata.2.1.pos)
        hdata.2.2.1.pos) hdata.2.2.1.pos
    have hpDvd : p ∣ p * q * r * r := by
      refine ⟨q * r * r, ?_⟩
      simp only [Nat.mul_assoc]
    have hqDvd : q ∣ p * q * r * r := by
      refine ⟨p * r * r, ?_⟩
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have hrDvd : r ∣ p * q * r * r := by
      refine ⟨p * q * r, ?_⟩
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have hpLe : p <= XNat := (Nat.le_of_dvd hcapPos hpDvd).trans hcap
    have hqLe : q <= XNat := (Nat.le_of_dvd hcapPos hqDvd).trans hcap
    have hrLe : r <= XNat := (Nat.le_of_dvd hcapPos hrDvd).trans hcap
    rw [Finset.product_eq_sprod, Finset.mem_product,
      Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨⟨Nat.mem_primesLE.mpr ⟨hpLe, hdata.1⟩,
      Nat.mem_primesLE.mpr ⟨hqLe, hdata.2.1⟩⟩,
      Nat.mem_primesLE.mpr ⟨hrLe, hdata.2.2.1⟩⟩
  have hweightNonneg : ∀ p ∈ primes, 0 <= primeWeight p := by
    intro p hp
    have hpPrime := (Nat.mem_primesLE.mp hp).2
    dsimp only [primeWeight]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
      (by positivity)
  have hprimeSum := sum_prime_log_div_le_two_mul_log_four_mul_log XNat hXNat
  unfold sectionSixFirstLowCentralLargeContinuationRoughErrorSum
  change (∑ index ∈ indices,
      1 / ((index.1.1 : Real) * (index.1.2 : Real) *
        (index.2 : Real) *
        Real.log (X /
          ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) ^ 2)) <= _
  calc
    _ <= ∑ index ∈ indices,
        primeWeight index.1.1 * primeWeight index.1.2 *
          primeWeight index.2 / denominator :=
      Finset.sum_le_sum fun index hindex => hpoint index hindex
    _ = (∑ triple ∈
          indices.image sectionSixFirstLowCentralLargeContinuationNatTriple,
          primeWeight triple.1.1 * primeWeight triple.1.2 *
            primeWeight triple.2) / denominator := by
      rw [← Finset.sum_div,
        Finset.sum_image
          sectionSixFirstLowCentralLargeContinuationNatTriple_injective.injOn]
      apply congrArg (fun value : Real => value / denominator)
      apply Finset.sum_congr rfl
      intro index _hindex
      rfl
    _ <= (∑ triple ∈ (primes.product primes).product primes,
          primeWeight triple.1.1 * primeWeight triple.1.2 *
            primeWeight triple.2) / denominator := by
      apply div_le_div_of_nonneg_right _ hdenominator.le
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro triple htriple _
      rw [Finset.product_eq_sprod, Finset.mem_product,
        Finset.product_eq_sprod, Finset.mem_product] at htriple
      exact mul_nonneg
        (mul_nonneg (hweightNonneg triple.1.1 htriple.1.1)
          (hweightNonneg triple.1.2 htriple.1.2))
        (hweightNonneg triple.2 htriple.2)
    _ = ((∑ p ∈ primes, primeWeight p) ^ 3) / denominator := by
      congr 1
      rw [Finset.product_eq_sprod, Finset.sum_product]
      calc
        (∑ pair ∈ primes ×ˢ primes,
            ∑ r ∈ primes,
              primeWeight pair.1 * primeWeight pair.2 * primeWeight r) =
            ∑ p ∈ primes, ∑ q ∈ primes, ∑ r ∈ primes,
              primeWeight p * primeWeight q * primeWeight r := by
          rw [Finset.sum_product]
        _ = _ := by
          simp_rw [← Finset.mul_sum]
          simp_rw [← Finset.sum_mul]
          rw [← Finset.sum_mul_sum]
          ring
    _ <= (2 * Real.log 4 * Real.log X) ^ 3 / denominator := by
      apply div_le_div_of_nonneg_right _ hdenominator.le
      exact pow_le_pow_left₀ (by positivity) hprimeSum 3
    _ = (2 * Real.log 4) ^ 3 /
        (sectionSixThetaGap epsilon ^ 5 * Real.log X ^ 2) := by
      dsimp only [denominator, gap]
      field_simp [hgap.ne', hlogX.ne']

end

end PrimesRestrictedDigits
