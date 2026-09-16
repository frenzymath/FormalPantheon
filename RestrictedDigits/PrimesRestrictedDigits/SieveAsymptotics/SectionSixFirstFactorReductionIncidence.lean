import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstFactorReductionCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixIncidenceAggregation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport

/-!
# Far factor-reduction incidence

For a fixed split below `sqrt X`, ordered prime-pair uniqueness sends every far factor tail
injectively into the weak small-product complement of the Type II near carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--140, Eq. (6.4).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirst_mem_outer_imp_full
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length p : Nat} (hlength : 1 <= length)
    (hp : p ∈ sectionSixFirstFactorOuterPrimes epsilon length) :
    p ∈ sievePrimeInterval
      (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
      (sectionSixZFour ((10 ^ length : Nat) : Real)) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  rw [sectionSixFirstFactorOuterPrimes, Finset.mem_union] at hp
  rcases hp with hp | hp
  · have h := mem_sievePrimeInterval.mp hp
    apply mem_sievePrimeInterval.mpr
    exact ⟨h.1, h.2.1,
      h.2.2.trans (horder.2.1.trans horder.2.2.1).le⟩
  · have h := mem_sievePrimeInterval.mp hp
    apply mem_sievePrimeInterval.mpr
    exact ⟨h.1, (horder.1.trans horder.2.1).trans h.2.1, h.2.2⟩

private theorem sectionSixFirst_four_le_quot_of_mem_outer
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length p : Nat} (hlength : 2 <= length)
    (hp : p ∈ sectionSixFirstFactorOuterPrimes epsilon length) :
    (4 : Real) <= ((10 ^ length : Nat) : Real) / (p : Real) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hlengthOne : 1 <= length := by omega
  have hpFull := sectionSixFirst_mem_outer_imp_full hepsilon hepsilonSmall
    hlengthOne hp
  have hpData := mem_sievePrimeInterval.mp hpFull
  have hpPos : (0 : Real) < (p : Real) := by exact_mod_cast hpData.1.pos
  have hX : 0 <= X := by positivity
  have hHundred : (100 : Real) <= X := by
    dsimp only [X]
    exact_mod_cast
      (pow_le_pow_right₀ (by norm_num : (1 : Nat) <= 10) hlength :
        (10 : Nat) ^ 2 <= 10 ^ length)
  have hTenSqrt : (10 : Real) <= Real.sqrt X := by
    rw [Real.le_sqrt (by norm_num) hX]
    norm_num
    exact hHundred
  have hpSqrt : (p : Real) <= Real.sqrt X := by
    simpa only [sectionSixZFour] using hpData.2.2
  have hsqrtDiv : Real.sqrt X <= X / (p : Real) := by
    apply (le_div_iff₀ hpPos).2
    calc
      Real.sqrt X * (p : Real) <= Real.sqrt X * Real.sqrt X :=
        mul_le_mul_of_nonneg_left hpSqrt (Real.sqrt_nonneg X)
      _ = X := by rw [Real.mul_self_sqrt hX]
  linarith

/-- Every represented far tail value lies in the weak small-product
complement, including equality at either weak cutoff. -/
theorem sectionSixFirstFactorRepresentedTail_subset_outsideNear
    {epsilon tau : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (C : Finset Nat) {length p : Nat} (hlength : 2 <= length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hwidth : majorArcM2LogLogDelta (10 ^ length) ^ 2 <= 2 * tau)
    (hp : p ∈ sectionSixFirstFactorFarPrimes epsilon tau length) :
    sectionSixFirstFactorRepresentedTail C length p ⊆
      C \ typeIINearXCarrier (10 ^ length)
        (majorArcM2LogLogDelta (10 ^ length)) := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let deltaX : Real := majorArcM2LogLogDelta XNat
  have hpFar := Finset.mem_filter.mp hp
  have hpOuter : p ∈ sectionSixFirstFactorOuterPrimes epsilon length := by
    simpa only [sectionSixFirstFactorFarPrimes, X, XNat] using hpFar.1
  have hpFull := sectionSixFirst_mem_outer_imp_full hepsilon hepsilonSmall
    (by omega : 1 <= length) hpOuter
  have hpPrime := (mem_sievePrimeInterval.mp hpFull).1
  have hquot := sectionSixFirst_four_le_quot_of_mem_outer hepsilon
    hepsilonSmall hlength hpOuter
  have hX : 1 < X := by
    dsimp only [X, XNat]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  intro n hn
  rw [sectionSixFirstFactorRepresentedTail, Finset.mem_image] at hn
  rcases hn with ⟨m, hmTail, rfl⟩
  have hm := (mem_sectionSixFirstFactorTail_iff hpPrime hC hquot).mp hmTail
  rw [Finset.mem_sdiff]
  refine ⟨hm.1, ?_⟩
  intro hnear
  have hnearData := mem_typeIINearXCarrier.mp hnear
  have hmCast : (m : Real) <= (p : Real) := by exact_mod_cast hm.2.2.2
  have hpSplit : (p : Real) <= X ^ (1 / 2 - tau) := by
    simpa only [sectionSixFirstFactorFarPrimes, X, XNat] using hpFar.2
  have hprodSplit : ((m * p : Nat) : Real) <= X ^ (1 - 2 * tau) := by
    calc
      ((m * p : Nat) : Real) = (m : Real) * (p : Real) := by norm_num
      _ <= (p : Real) * (p : Real) :=
        mul_le_mul_of_nonneg_right hmCast (Nat.cast_nonneg p)
      _ <= X ^ (1 / 2 - tau) * X ^ (1 / 2 - tau) :=
        mul_le_mul hpSplit hpSplit (Nat.cast_nonneg p)
          (Real.rpow_nonneg (zero_lt_one.trans hX).le _)
      _ = X ^ ((1 / 2 - tau) + (1 / 2 - tau)) := by
        rw [Real.rpow_add (zero_lt_one.trans hX)]
      _ = X ^ (1 - 2 * tau) := by ring_nf
  have hexponent : 1 - 2 * tau <= 1 - deltaX ^ 2 := by
    dsimp only [deltaX, XNat]
    linarith
  have hprodNear : ((m * p : Nat) : Real) <= X ^ (1 - deltaX ^ 2) :=
    hprodSplit.trans (Real.rpow_le_rpow_of_exponent_le hX.le hexponent)
  exact (not_lt_of_ge hprodNear) hnearData.2

/-- Ordered prime-pair factorization makes each represented far fiber have
cardinality at most one, including the repeated factor case. -/
theorem sectionSixFirstFactorFarProductFiber_le_one
    {epsilon tau : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (C : Finset Nat) {length : Nat} (hlength : 2 <= length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (n : Nat) :
    ((sectionSixFirstFactorFarPrimes epsilon tau length).filter fun p =>
      n ∈ sectionSixFirstFactorRepresentedTail C length p).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  have hpData := Finset.mem_filter.mp hp
  have hqData := Finset.mem_filter.mp hq
  have hpFar := Finset.mem_filter.mp hpData.1
  have hqFar := Finset.mem_filter.mp hqData.1
  have hpOuter : p ∈ sectionSixFirstFactorOuterPrimes epsilon length := by
    simpa only [sectionSixFirstFactorFarPrimes] using hpFar.1
  have hqOuter : q ∈ sectionSixFirstFactorOuterPrimes epsilon length := by
    simpa only [sectionSixFirstFactorFarPrimes] using hqFar.1
  have hpFull := sectionSixFirst_mem_outer_imp_full hepsilon hepsilonSmall
    (by omega : 1 <= length) hpOuter
  have hqFull := sectionSixFirst_mem_outer_imp_full hepsilon hepsilonSmall
    (by omega : 1 <= length) hqOuter
  have hpPrime := (mem_sievePrimeInterval.mp hpFull).1
  have hqPrime := (mem_sievePrimeInterval.mp hqFull).1
  have hpQuot := sectionSixFirst_four_le_quot_of_mem_outer hepsilon
    hepsilonSmall hlength hpOuter
  have hqQuot := sectionSixFirst_four_le_quot_of_mem_outer hepsilon
    hepsilonSmall hlength hqOuter
  rw [sectionSixFirstFactorRepresentedTail, Finset.mem_image] at hpData hqData
  rcases hpData.2 with ⟨mp, hmpTail, hmpProduct⟩
  rcases hqData.2 with ⟨mq, hmqTail, hmqProduct⟩
  have hmp := (mem_sectionSixFirstFactorTail_iff hpPrime hC hpQuot).mp hmpTail
  have hmq := (mem_sectionSixFirstFactorTail_iff hqPrime hC hqQuot).mp hmqTail
  have hproduct : mp * p = mq * q := hmpProduct.trans hmqProduct.symm
  have hpDvd : p ∣ mq * q := by
    rw [← hproduct]
    exact Nat.dvd_mul_left p mp
  rcases hpPrime.dvd_mul.mp hpDvd with hpMq | hpQ
  · have hpEqMq : p = mq :=
      (Nat.prime_dvd_prime_iff_eq hpPrime hmq.2.1).mp hpMq
    have hmpEqQ : mp = q := by
      apply Nat.mul_right_cancel hpPrime.pos
      calc
        mp * p = mq * q := hproduct
        _ = p * q := by rw [hpEqMq]
        _ = q * p := Nat.mul_comm _ _
    exact le_antisymm
      (hpEqMq.trans_le hmq.2.2.2)
      (hmpEqQ ▸ hmp.2.2.2)
  · exact (Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp hpQ

/-- The total far tail is dominated by the common weak small-product
complement with no multiplicity loss. -/
theorem sectionSixFirstFactorFarTailSum_le_outsideNear
    {epsilon tau : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (C : Finset Nat) {length : Nat} (hlength : 2 <= length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hwidth : majorArcM2LogLogDelta (10 ^ length) ^ 2 <= 2 * tau) :
    sectionSixFirstFactorTailSum C length
        (sectionSixFirstFactorFarPrimes epsilon tau length) <=
      ((C \ typeIINearXCarrier (10 ^ length)
        (majorArcM2LogLogDelta (10 ^ length))).card : Real) := by
  let states := sectionSixFirstFactorFarPrimes epsilon tau length
  let outside := C \ typeIINearXCarrier (10 ^ length)
    (majorArcM2LogLogDelta (10 ^ length))
  calc
    sectionSixFirstFactorTailSum C length states =
        ∑ p ∈ states,
          ((sectionSixFirstFactorRepresentedTail C length p).card : Real) := by
      unfold sectionSixFirstFactorTailSum
      apply Finset.sum_congr rfl
      intro p hp
      have hpFar := Finset.mem_filter.mp hp
      have hpOuter : p ∈ sectionSixFirstFactorOuterPrimes epsilon length := by
        simpa only [states, sectionSixFirstFactorFarPrimes] using hpFar.1
      have hpFull := sectionSixFirst_mem_outer_imp_full hepsilon
        hepsilonSmall (by omega : 1 <= length) hpOuter
      rw [card_sectionSixFirstFactorRepresentedTail C length
        (mem_sievePrimeInterval.mp hpFull).1]
    _ <= (1 : Real) * (outside.card : Real) := by
      simpa only [Nat.cast_one] using
        (sum_card_le_of_element_fiber_card_real states outside
          (sectionSixFirstFactorRepresentedTail C length) 1
          (by
            intro p hp
            dsimp only [states, outside]
            exact sectionSixFirstFactorRepresentedTail_subset_outsideNear
              hepsilon hepsilonSmall C hlength hC hwidth hp)
          (by
            intro n hn
            dsimp only [states, outside]
            exact sectionSixFirstFactorFarProductFiber_le_one hepsilon
              hepsilonSmall C hlength hC n))
    _ = ((C \ typeIINearXCarrier (10 ^ length)
        (majorArcM2LogLogDelta (10 ^ length))).card : Real) := by
      simp only [one_mul, outside]

end

end PrimesRestrictedDigits
