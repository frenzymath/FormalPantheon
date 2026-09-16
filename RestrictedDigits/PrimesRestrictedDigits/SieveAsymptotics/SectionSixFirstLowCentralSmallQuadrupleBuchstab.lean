import PrimesRestrictedDigits.BasicEstimates.BuchstabFunction
import PrimesRestrictedDigits.BasicEstimates.PrimeDistribution
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralSmallIndices
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Buchstab sums for the low central-small strict quadruple term

This file owns the raw Buchstab main and rough-error sums for the `Q` term and the
fourth-power prime-mass bound for the error.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12) and region `R3`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def sectionSixFirstLowCentralSmallQuadrupleNatTuple
    (index : SectionSixFirstLowCentralSmallQuadrupleIndex) :
    ((Nat × Nat) × Nat) × Nat :=
  (((index.1.1.1, index.1.1.2), index.1.2), index.2)

private theorem sectionSixFirstLowCentralSmallQuadrupleNatTuple_injective :
    Function.Injective sectionSixFirstLowCentralSmallQuadrupleNatTuple := by
  rintro ⟨⟨⟨p, q⟩, r⟩, s⟩ ⟨⟨⟨p', q'⟩, r'⟩, s'⟩ h
  simp only [sectionSixFirstLowCentralSmallQuadrupleNatTuple,
    Prod.mk.injEq] at h
  rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
  rfl

noncomputable def sectionSixFirstLowCentralSmallQuadrupleBuchstabMainSum
    (epsilon : Real) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstLowCentralSmallQuadrupleIndices epsilon length,
    buchstabFunction
        (Real.log (X /
          ((sectionSixFirstLowCentralSmallTripleProduct index.1 * index.2 :
            Nat) : Real)) / Real.log (index.2 : Real)) /
      ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
        (index.1.2 : Real) * (index.2 : Real) * Real.log (index.2 : Real))

noncomputable def sectionSixFirstLowCentralSmallQuadrupleRoughErrorSum
    (epsilon : Real) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstLowCentralSmallQuadrupleIndices epsilon length,
    1 / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
      (index.1.2 : Real) * (index.2 : Real) *
      Real.log (X /
        ((sectionSixFirstLowCentralSmallTripleProduct index.1 * index.2 :
          Nat) : Real)) ^ 2)

private theorem sectionSixFirstLowCentralSmallQuadruple_indexData
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallQuadrupleIndices
      epsilon length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    index.1.1.1.Prime ∧ index.1.1.2.Prime ∧ index.1.2.Prime ∧
      index.2.Prime ∧
      X ^ sectionSixThetaGap epsilon < (index.1.1.1 : Real) ∧
      X ^ sectionSixThetaGap epsilon < (index.1.1.2 : Real) ∧
      X ^ sectionSixThetaGap epsilon < (index.1.2 : Real) ∧
      X ^ sectionSixThetaGap epsilon < (index.2 : Real) ∧
      index.1.1.1 * index.1.1.2 * index.1.2 * index.2 * index.2 <=
        10 ^ length := by
  classical
  let X : Real := ((10 ^ length : Nat) : Real)
  have hquad := mem_sectionSixFirstLowCentralSmallQuadrupleIndices.mp hindex
  have hraw :=
    mem_sectionSixFirstLowCentralSmallRawQuadrupleIndices.mp hquad.1
  have htriple :=
    mem_sectionSixFirstLowCentralSmallTripleIndices.mp hraw.1
  have hsData := mem_sievePrimeInterval.mp hraw.2
  have hrData := mem_sievePrimeInterval.mp htriple.2
  have hpairFiltered := Finset.mem_filter.mp htriple.1
  have hpiece :
      index.1.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
        sectionSixZThree epsilon X <
            (sectionSixFirstPairProduct index.1.1 : Real) ∧
          (sectionSixFirstPairProduct index.1.1 : Real) <
              sectionSixZFive epsilon X ∧
            (sectionSixFirstPairSquareProduct index.1.1 : Real) <
              sectionSixZSix epsilon X := by
    simpa only [sectionSixFirstPairMem, X] using hpairFiltered.2
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
  have hpData := mem_sievePrimeInterval.mp hpqData.1
  have hqData := mem_sievePrimeInterval.mp hpqData.2
  have hpLower : X ^ sectionSixThetaGap epsilon <
      (index.1.1.1 : Real) := by
    simpa only [sectionSixZOne, X] using hpData.2.1
  have hsTerminal :
      (index.2 : Real) <=
        sectionSixFirstLowCentralSmallTripleTerminalThreshold length index.1 :=
    hsData.2.2.trans (min_le_right _ _)
  have hcap :=
    (sectionSixFirstLowCentralSmall_le_tripleTerminalThreshold_iff
      hpData.1 hqData.1 hrData.1 hsData.1).mp hsTerminal
  exact ⟨hpData.1, hqData.1, hrData.1, hsData.1, hpLower,
    by simpa only [sectionSixZOne, X] using hqData.2.1,
    by simpa only [sectionSixZOne, X] using hrData.2.1,
    by simpa only [sectionSixZOne, X] using hsData.2.1, hcap⟩

private theorem sectionSixFirstLowCentralSmallQuadruple_roughSummand_le
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallQuadrupleIndices
      epsilon length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    1 / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
        (index.1.2 : Real) * (index.2 : Real) *
        Real.log (X /
          ((index.1.1.1 * index.1.1.2 * index.1.2 * index.2 : Nat) :
            Real)) ^ 2) <=
      (Real.log (index.1.1.1 : Real) / (index.1.1.1 : Real)) *
        (Real.log (index.1.1.2 : Real) / (index.1.1.2 : Real)) *
        (Real.log (index.1.2 : Real) / (index.1.2 : Real)) *
        (Real.log (index.2 : Real) / (index.2 : Real)) /
          (sectionSixThetaGap epsilon ^ 6 * Real.log X ^ 6) := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let p : Nat := index.1.1.1
  let q : Nat := index.1.1.2
  let r : Nat := index.1.2
  let s : Nat := index.2
  let Y : Real := X / ((p * q * r * s : Nat) : Real)
  rcases sectionSixFirstLowCentralSmallQuadruple_indexData
      hindex with
    ⟨hp, hq, hr, hs, hpLower, hqLower, hrLower, hsLower, hcap⟩
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hq.pos
  have hrPos : (0 : Real) < r := by exact_mod_cast hr.pos
  have hsPos : (0 : Real) < s := by exact_mod_cast hs.pos
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hgap : 0 < gap := by
    simpa only [gap] using
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hscale : 0 < gap * Real.log X := mul_pos hgap hlogX
  have hsY : (s : Real) <= Y := by
    dsimp only [Y]
    norm_num only [Nat.cast_mul]
    apply (le_div_iff₀ (mul_pos (mul_pos (mul_pos hpPos hqPos) hrPos)
      hsPos)).2
    have hcapReal : (((p * q * r * s * s : Nat) : Real)) <= X := by
      dsimp only [X, XNat]
      exact_mod_cast hcap
    norm_num only [Nat.cast_mul] at hcapReal
    nlinarith
  have hY : 0 < Y := hsPos.trans_le hsY
  have hlogsY : Real.log (s : Real) <= Real.log Y :=
    Real.log_le_log hsPos hsY
  have hlogs : 0 < Real.log (s : Real) :=
    Real.log_pos (by exact_mod_cast hs.one_lt)
  have hlogYPos : 0 < Real.log Y := hlogs.trans_le hlogsY
  have logLower {a : Nat} (haPos : (0 : Real) < a)
      (haLower : X ^ gap < (a : Real)) :
      gap * Real.log X <= Real.log (a : Real) := by
    have haLogb : gap < Real.logb X (a : Real) :=
      (Real.lt_logb_iff_rpow_lt hX haPos).2 haLower
    exact ((lt_div_iff₀ hlogX).1
      (by simpa only [Real.logb] using haLogb)).le
  have hpLog := logLower hpPos (by simpa only [X, XNat, gap, p] using hpLower)
  have hqLog := logLower hqPos (by simpa only [X, XNat, gap, q] using hqLower)
  have hrLog := logLower hrPos (by simpa only [X, XNat, gap, r] using hrLower)
  have hsLog := logLower hsPos (by simpa only [X, XNat, gap, s] using hsLower)
  have hYLog : gap * Real.log X <= Real.log Y := hsLog.trans hlogsY
  have hpLogNonneg : 0 <= Real.log (p : Real) := hscale.le.trans hpLog
  have hqLogNonneg : 0 <= Real.log (q : Real) := hscale.le.trans hqLog
  have hrLogNonneg : 0 <= Real.log (r : Real) := hscale.le.trans hrLog
  have hsLogNonneg : 0 <= Real.log (s : Real) := hscale.le.trans hsLog
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
  have hlogsFour : (gap * Real.log X) ^ 4 <=
      Real.log (p : Real) * Real.log (q : Real) *
        Real.log (r : Real) * Real.log (s : Real) := by
    rw [pow_succ]
    exact mul_le_mul hlogsThree hsLog hscale.le
      (mul_nonneg (mul_nonneg hpLogNonneg hqLogNonneg) hrLogNonneg)
  have hYTwo : (gap * Real.log X) ^ 2 <= Real.log Y ^ 2 :=
    (sq_le_sq₀ hscale.le (hscale.le.trans hYLog)).2 hYLog
  have hproduct : (gap * Real.log X) ^ 6 <=
      (Real.log (p : Real) * Real.log (q : Real) *
        Real.log (r : Real) * Real.log (s : Real)) * Real.log Y ^ 2 := by
    calc
      (gap * Real.log X) ^ 6 =
          (gap * Real.log X) ^ 4 * (gap * Real.log X) ^ 2 := by ring
      _ <= (Real.log (p : Real) * Real.log (q : Real) *
          Real.log (r : Real) * Real.log (s : Real)) * Real.log Y ^ 2 :=
        mul_le_mul hlogsFour hYTwo (sq_nonneg _)
          (mul_nonneg
            (mul_nonneg (mul_nonneg hpLogNonneg hqLogNonneg) hrLogNonneg)
            hsLogNonneg)
  have hcore : 1 / Real.log Y ^ 2 <=
      (Real.log (p : Real) * Real.log (q : Real) *
        Real.log (r : Real) * Real.log (s : Real)) /
          (gap * Real.log X) ^ 6 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hlogYPos)
      (pow_pos hscale 6)).2
    simpa only [one_mul] using hproduct
  dsimp only [X, XNat, gap, p, q, r, s, Y]
  calc
    1 / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
        (index.1.2 : Real) * (index.2 : Real) *
        Real.log (((10 ^ length : Nat) : Real) /
          ((index.1.1.1 * index.1.1.2 * index.1.2 * index.2 : Nat) :
            Real)) ^ 2) =
      (1 / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
        (index.1.2 : Real) * (index.2 : Real))) *
        (1 / Real.log (((10 ^ length : Nat) : Real) /
          ((index.1.1.1 * index.1.1.2 * index.1.2 * index.2 : Nat) :
            Real)) ^ 2) := by ring
    _ <= (1 / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
          (index.1.2 : Real) * (index.2 : Real))) *
        ((Real.log (index.1.1.1 : Real) *
          Real.log (index.1.1.2 : Real) * Real.log (index.1.2 : Real) *
          Real.log (index.2 : Real)) /
            (sectionSixThetaGap epsilon *
              Real.log ((10 ^ length : Nat) : Real)) ^ 6) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = (Real.log (index.1.1.1 : Real) / (index.1.1.1 : Real)) *
        (Real.log (index.1.1.2 : Real) / (index.1.1.2 : Real)) *
        (Real.log (index.1.2 : Real) / (index.1.2 : Real)) *
        (Real.log (index.2 : Real) / (index.2 : Real)) /
          (sectionSixThetaGap epsilon ^ 6 *
            Real.log ((10 ^ length : Nat) : Real) ^ 6) := by
      field_simp [hp.ne_zero, hq.ne_zero, hr.ne_zero, hs.ne_zero,
        hgap.ne', hlogX.ne']

theorem sectionSixFirstLowCentralSmallQuadrupleRoughErrorSum_le
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowCentralSmallQuadrupleRoughErrorSum epsilon length <=
      (2 * Real.log 4) ^ 4 /
        (sectionSixThetaGap epsilon ^ 6 *
          Real.log ((10 ^ length : Nat) : Real) ^ 2) := by
  classical
  let indices := sectionSixFirstLowCentralSmallQuadrupleIndices epsilon length
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let primeWeight : Nat -> Real := fun p => Real.log (p : Real) / (p : Real)
  let denominator : Real := gap ^ 6 * Real.log X ^ 6
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
      1 / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
          (index.1.2 : Real) * (index.2 : Real) *
          Real.log (X /
            ((index.1.1.1 * index.1.1.2 * index.1.2 * index.2 : Nat) :
              Real)) ^ 2) <=
        primeWeight index.1.1.1 * primeWeight index.1.1.2 *
          primeWeight index.1.2 * primeWeight index.2 / denominator := by
    intro index hindex
    simpa only [indices, X, XNat, gap, primeWeight, denominator] using
      sectionSixFirstLowCentralSmallQuadruple_roughSummand_le
        hepsilon hepsilonSmall hlength hindex
  have hsubset :
      indices.image sectionSixFirstLowCentralSmallQuadrupleNatTuple ⊆
        (((primes.product primes).product primes).product primes) := by
    intro quadruple hquadruple
    rcases Finset.mem_image.mp hquadruple with ⟨index, hindex, rfl⟩
    rcases sectionSixFirstLowCentralSmallQuadruple_indexData
        (by simpa only [indices] using hindex) with
      ⟨hp, hq, hr, hs, _hpLower, _hqLower, _hrLower, _hsLower, hcap⟩
    let p := index.1.1.1
    let q := index.1.1.2
    let r := index.1.2
    let s := index.2
    have hcapPos : 0 < p * q * r * s * s :=
      Nat.mul_pos
        (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos) hs.pos)
        hs.pos
    have hpDvd : p ∣ p * q * r * s * s := by
      refine ⟨q * r * s * s, ?_⟩
      simp only [Nat.mul_assoc]
    have hqDvd : q ∣ p * q * r * s * s := by
      refine ⟨p * r * s * s, ?_⟩
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have hrDvd : r ∣ p * q * r * s * s := by
      refine ⟨p * q * s * s, ?_⟩
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have hsDvd : s ∣ p * q * r * s * s := by
      refine ⟨p * q * r * s, ?_⟩
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have hpLe : p <= XNat :=
      (Nat.le_of_dvd hcapPos hpDvd).trans hcap
    have hqLe : q <= XNat :=
      (Nat.le_of_dvd hcapPos hqDvd).trans hcap
    have hrLe : r <= XNat :=
      (Nat.le_of_dvd hcapPos hrDvd).trans hcap
    have hsLe : s <= XNat :=
      (Nat.le_of_dvd hcapPos hsDvd).trans hcap
    rw [Finset.product_eq_sprod, Finset.mem_product,
      Finset.product_eq_sprod, Finset.mem_product,
      Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨⟨⟨Nat.mem_primesLE.mpr ⟨hpLe, hp⟩,
      Nat.mem_primesLE.mpr ⟨hqLe, hq⟩⟩,
      Nat.mem_primesLE.mpr ⟨hrLe, hr⟩⟩,
      Nat.mem_primesLE.mpr ⟨hsLe, hs⟩⟩
  have hweightNonneg : ∀ p ∈ primes, 0 <= primeWeight p := by
    intro p hp
    have hpPrime := (Nat.mem_primesLE.mp hp).2
    dsimp only [primeWeight]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
      (by positivity)
  have hprimeSum := sum_prime_log_div_le_two_mul_log_four_mul_log XNat hXNat
  unfold sectionSixFirstLowCentralSmallQuadrupleRoughErrorSum
  simp only [sectionSixFirstLowCentralSmallTripleProduct,
    sectionSixFirstPairProduct]
  change (∑ index ∈ indices,
      1 / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
        (index.1.2 : Real) * (index.2 : Real) *
        Real.log (X /
          ((index.1.1.1 * index.1.1.2 * index.1.2 * index.2 : Nat) :
            Real)) ^ 2)) <= _
  calc
    _ <= ∑ index ∈ indices,
        primeWeight index.1.1.1 * primeWeight index.1.1.2 *
          primeWeight index.1.2 * primeWeight index.2 / denominator :=
      Finset.sum_le_sum fun index hindex => hpoint index hindex
    _ = (∑ quadruple ∈
          indices.image sectionSixFirstLowCentralSmallQuadrupleNatTuple,
          primeWeight quadruple.1.1.1 * primeWeight quadruple.1.1.2 *
            primeWeight quadruple.1.2 * primeWeight quadruple.2) /
          denominator := by
      rw [← Finset.sum_div,
        Finset.sum_image
          sectionSixFirstLowCentralSmallQuadrupleNatTuple_injective.injOn]
      apply congrArg (fun value : Real => value / denominator)
      apply Finset.sum_congr rfl
      intro index _hindex
      rfl
    _ <= (∑ quadruple ∈
          (((primes.product primes).product primes).product primes),
          primeWeight quadruple.1.1.1 * primeWeight quadruple.1.1.2 *
            primeWeight quadruple.1.2 * primeWeight quadruple.2) /
          denominator := by
      apply div_le_div_of_nonneg_right _ hdenominator.le
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro quadruple hquadruple _
      rw [Finset.product_eq_sprod, Finset.mem_product,
        Finset.product_eq_sprod, Finset.mem_product,
        Finset.product_eq_sprod, Finset.mem_product] at hquadruple
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (hweightNonneg quadruple.1.1.1 hquadruple.1.1.1)
            (hweightNonneg quadruple.1.1.2 hquadruple.1.1.2))
          (hweightNonneg quadruple.1.2 hquadruple.1.2))
        (hweightNonneg quadruple.2 hquadruple.2)
    _ = ((∑ p ∈ primes, primeWeight p) ^ 4) / denominator := by
      congr 1
      rw [Finset.product_eq_sprod, Finset.sum_product,
        Finset.product_eq_sprod, Finset.sum_product,
        Finset.product_eq_sprod, Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      simp_rw [← Finset.sum_mul]
      have hcube :
          (∑ p ∈ primes, ∑ q ∈ primes, ∑ r ∈ primes,
              primeWeight p * primeWeight q * primeWeight r) =
            (∑ p ∈ primes, primeWeight p) ^ 3 := by
        simp_rw [← Finset.mul_sum]
        simp_rw [← Finset.sum_mul]
        rw [← Finset.sum_mul_sum]
        ring
      rw [hcube]
      ring
    _ <= (2 * Real.log 4 * Real.log X) ^ 4 / denominator := by
      apply div_le_div_of_nonneg_right _ hdenominator.le
      exact pow_le_pow_left₀ (by positivity) hprimeSum 4
    _ = (2 * Real.log 4) ^ 4 /
        (sectionSixThetaGap epsilon ^ 6 * Real.log X ^ 2) := by
      dsimp only [denominator, gap]
      field_simp [hgap.ne', hlogX.ne']

end

end PrimesRestrictedDigits
