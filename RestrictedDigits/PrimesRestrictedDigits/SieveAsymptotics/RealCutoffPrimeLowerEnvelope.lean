import PrimesRestrictedDigits.SieveAsymptotics.FixedLengthPrimeLowerEnvelope
import PrimesRestrictedDigits.SieveAsymptotics.ZeroPrimeBlockPaddedBridge
import PrimesRestrictedDigits.Foundations.CutoffMonotonicity
import PrimesRestrictedDigits.Foundations.DecimalScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Standard real-cutoff lower envelope for restricted primes

One sufficiently long padded block supplies a lower prime count. For excluded zero the full
standard integer count is bounded by a geometric sum of blocks; for other digits the
adjacent-power count sandwich suffices.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 136.
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits

noncomputable section

private theorem decimalInterval_count_and_paddedPrime_bounds
    (digit : Fin 10) {X : Real} {length : Nat}
    (hlength : 1 <= length)
    (hlo : ((10 ^ length : Nat) : Real) <= X)
    (hupp : X < ((10 ^ (length + 1) : Nat) : Real)) :
    restrictedCount digit X <=
        18 * (paddedRestrictedNumbers digit length).card /\
      paddedRestrictedPrimeCount digit length <=
        restrictedPrimeCount digit X := by
  by_cases hdigit : digit.val = 0
  · have hdigitZero : digit = (0 : Fin 10) := Fin.ext hdigit
    subst digit
    constructor
    · have hsum : forall k : Nat,
          (∑ i ∈ Finset.range k, (9 : Nat) ^ (i + 1)) <= 2 * 9 ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            rw [Finset.sum_range_succ, pow_succ]
            nlinarith [ih, Nat.zero_le (9 ^ k)]
      calc
        restrictedCount (0 : Fin 10) X <=
            restrictedCount (0 : Fin 10) ((10 ^ (length + 1) : Nat) : Real) :=
          restrictedCount_le_of_le hupp.le
        _ = ∑ i ∈ Finset.range (length + 1), 9 ^ (i + 1) :=
          restrictedCount_zero_power (length + 1)
        _ <= 2 * 9 ^ (length + 1) := hsum (length + 1)
        _ = 18 * (paddedRestrictedNumbers (0 : Fin 10) length).card := by
          rw [card_paddedRestrictedNumbers, pow_succ]
          ring
    · have hindex : length - 1 ∈ Finset.range length := by
        rw [Finset.mem_range]
        omega
      have hblock : (zeroRestrictedPrimeBlock (length - 1)).card =
          paddedRestrictedPrimeCount (0 : Fin 10) length := by
        rw [zeroRestrictedPrimeBlock_eq_paddedRestrictedPrimes,
          Nat.sub_add_cancel hlength]
        rfl
      calc
        paddedRestrictedPrimeCount (0 : Fin 10) length =
            (zeroRestrictedPrimeBlock (length - 1)).card := hblock.symm
        _ <= ∑ i ∈ Finset.range length, (zeroRestrictedPrimeBlock i).card :=
          Finset.single_le_sum (fun i _ => Nat.zero_le
            (zeroRestrictedPrimeBlock i).card) hindex
        _ <= restrictedPrimeCount (0 : Fin 10) X :=
          (restrictedPrimeCount_zero_cutoff_block_sandwich hlo hupp).1
  · constructor
    · have hcount :=
        (restrictedCount_bounds_of_decimalPower_interval_of_ne_zero
          hdigit hlo hupp).2
      rw [card_paddedRestrictedNumbers]
      rw [pow_succ] at hcount
      nlinarith [Nat.zero_le (9 ^ length)]
    · rw [paddedRestrictedPrimeCount_eq_restrictedPrimeCount_of_ne_zero
        hdigit length]
      exact restrictedPrimeCount_le_of_le hlo

theorem exists_restrictedPrimeCount_lower_envelope_of_integral_sum_lt_one
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (hIntegralSum :
      sectionSixFirstLowFarIntegral epsilon +
          sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
        sectionSixFirstLowCentralLargeBelowIntegral epsilon +
      sectionSixFirstLowCentralLargeAboveIntegral epsilon +
        sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
      sectionSixFirstLowBelowQuadrupleIntegral epsilon +
        sectionSixFirstHighFarIntegral epsilon +
      sectionSixFirstHighCentralLargeIntegral epsilon +
        sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon < 1) :
    exists C : Real, 0 < C /\
      exists X0 : Real, 4 <= X0 /\
        forall digit : Fin 10, forall X : Real, X0 <= X ->
          C * ((restrictedCount digit X : Real) / Real.log X) <=
            (restrictedPrimeCount digit X : Real) := by
  obtain ⟨C0, hC0, length0, hlength0, hprimeAt⟩ :=
    exists_paddedRestrictedPrimeCount_lower_envelope_of_integral_sum_lt_one
      epsilon hepsilon hepsilonSmall hepsilonRosser hIntegralSum
  let X0 : Real := ((10 ^ length0 : Nat) : Real)
  have hX0 : 4 <= X0 := by
    have hpow : 10 <= 10 ^ length0 := by
      simpa only [pow_one] using
        (pow_le_pow_right₀ (by norm_num : (1 : Nat) <= 10) hlength0)
    dsimp only [X0]
    exact_mod_cast (show 4 <= 10 ^ length0 by omega)
  refine ⟨C0 / 18, by positivity, X0, hX0, ?_⟩
  intro digit X hXX0
  have hX4 : 4 <= X := hX0.trans hXX0
  obtain ⟨length, hlo, hupp⟩ := exists_decimalPower_interval hX4
  have hpowers : ((10 ^ length0 : Nat) : Real) <
      ((10 ^ (length + 1) : Nat) : Real) := hXX0.trans_lt hupp
  have hpowersNat : 10 ^ length0 < 10 ^ (length + 1) := by
    exact_mod_cast hpowers
  have hlengthLt : length0 < length + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (10 : Nat))).mp hpowersNat
  have hlengthLe : length0 <= length := by omega
  have hlengthOne : 1 <= length := hlength0.trans hlengthLe
  rcases decimalInterval_count_and_paddedPrime_bounds digit hlengthOne hlo hupp with
    ⟨hcount, hprime⟩
  have hcountReal : (restrictedCount digit X : Real) <=
      18 * ((paddedRestrictedNumbers digit length).card : Real) := by
    exact_mod_cast hcount
  have hprimeReal : (paddedRestrictedPrimeCount digit length : Real) <=
      (restrictedPrimeCount digit X : Real) := by
    exact_mod_cast hprime
  have hYOne : 1 < ((10 ^ length : Nat) : Real) := by
    exact_mod_cast sectionSixFirst_direct_hXNat hlengthOne
  have hlogY : 0 < Real.log ((10 ^ length : Nat) : Real) := Real.log_pos hYOne
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogOrder : Real.log ((10 ^ length : Nat) : Real) <= Real.log X :=
    Real.log_le_log (by linarith) hlo
  calc
    (C0 / 18) * ((restrictedCount digit X : Real) / Real.log X) =
        ((C0 / 18) * (restrictedCount digit X : Real)) / Real.log X := by ring
    _ <= ((C0 / 18) *
        (18 * ((paddedRestrictedNumbers digit length).card : Real))) / Real.log X :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcountReal (by positivity)) hlogX.le
    _ = C0 * ((paddedRestrictedNumbers digit length).card : Real) / Real.log X := by
      ring
    _ <= C0 * ((paddedRestrictedNumbers digit length).card : Real) /
        Real.log ((10 ^ length : Nat) : Real) :=
      div_le_div_of_nonneg_left (by positivity) hlogY hlogOrder
    _ <= (paddedRestrictedPrimeCount digit length : Real) :=
      hprimeAt length hlengthLe digit
    _ <= (restrictedPrimeCount digit X : Real) := hprimeReal

end

end PrimesRestrictedDigits
