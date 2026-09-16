import PrimesRestrictedDigits.SieveAsymptotics.TypeIIReduction
import PrimesRestrictedDigits.SieveDecomposition.FixedLengthPrimeBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed-length upper envelope for restricted primes

This is the elementary upper transfer used before the real-cutoff theorem is assembled. It
combines the Type-II sifted-carrier estimate with the exact small-prime correction for the
padded decimal carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Sections 6 and 9.
-/

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 1200000 in
theorem exists_paddedRestrictedPrimeCount_upper_envelope :
    ∃ C : Real, 0 < C ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length -> ∀ digit : Fin 10,
          let X : Real := ((10 ^ length : Nat) : Real)
          (paddedRestrictedPrimeCount digit length : Real) <=
            C * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log X := by
  obtain ⟨C0, hC0, length0, hlength0, hsift⟩ :=
    exists_paddedRestrictedSiftedCount_eta_upper (1 / 4 : Real) (by norm_num)
  refine ⟨C0 + 20, by linarith, length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  have hlengthOne : 1 <= length := hlength0.trans hlength
  have hX : 1 < X := by
    dsimp [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hXpos : 0 < X := by linarith
  have hlogPos : 0 < Real.log X := Real.log_pos (by linarith)
  have hprime := paddedRestrictedPrimeCount_le_zOne_sifted_add_small
    (epsilon := (1 / 1600 : Real)) (by norm_num) (by norm_num)
    digit hlengthOne
  change paddedRestrictedPrimeCount digit length <=
    (strictSiftedCarrier (paddedRestrictedNumbers digit length)
      (sectionSixZOne (1 / 1600 : Real) X)).card +
      (paddedRestrictedSmallPrimes digit length (sectionSixZFour X)).card at hprime
  have hprimeReal :
      (paddedRestrictedPrimeCount digit length : Real) <=
        ((strictSiftedCarrier (paddedRestrictedNumbers digit length)
          (sectionSixZOne (1 / 1600 : Real) X)).card : Real) +
          ((paddedRestrictedSmallPrimes digit length
            (sectionSixZFour X)).card : Real) := by
    exact_mod_cast hprime
  have hsift' := hsift length hlength digit
  dsimp only [X] at hsift'
  have hcutoff : sectionSixZOne (1 / 1600 : Real) X = X ^ ((1 / 4 : Real) / 4) := by
    simp only [sectionSixZOne, sectionSixThetaGap_eq]
    norm_num
  rw [hcutoff] at hprimeReal
  have hsmallNat := card_paddedRestrictedSmallPrimes_le_floor_add_one digit length
    (z := sectionSixZFour X) (by
      rw [sectionSixZFour]
      positivity)
  have hsmall :
      ((paddedRestrictedSmallPrimes digit length (sectionSixZFour X)).card : Real) <=
        (Nat.floor (sectionSixZFour X) : Real) + 1 := by
    exact_mod_cast hsmallNat
  have hfloor : (Nat.floor (sectionSixZFour X) : Real) <= sectionSixZFour X :=
    Nat.floor_le (by
      rw [sectionSixZFour]
      positivity)
  have hsqrt : sectionSixZFour X <= (4 ^ length : Real) := by
    rw [sectionSixZFour]
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hpowNat : 10 ^ length <= 16 ^ length :=
        Nat.pow_le_pow_left (by norm_num : 10 <= 16) length
      have hpow : X <= (4 ^ length : Real) ^ 2 := by
        dsimp [X]
        calc
          ((10 ^ length : Nat) : Real) <= ((16 ^ length : Nat) : Real) := by
            exact_mod_cast hpowNat
          _ = (4 ^ length : Real) ^ 2 := by
            rw [Nat.cast_pow]
            calc
              (16 : Real) ^ length = (4 ^ 2) ^ length := by norm_num
              _ = 4 ^ (2 * length) := by rw [pow_mul]
              _ = 4 ^ (length * 2) := by congr 1; omega
              _ = (4 ^ length) ^ 2 := by rw [← pow_mul]
      exact hpow
  have hsmallPow :
      ((paddedRestrictedSmallPrimes digit length (sectionSixZFour X)).card : Real) <=
        2 * (4 ^ length : Real) := by
    calc
      ((paddedRestrictedSmallPrimes digit length (sectionSixZFour X)).card : Real) <=
          (Nat.floor (sectionSixZFour X) : Real) + 1 := hsmall
      _ <= sectionSixZFour X + 1 := by linarith
      _ <= (4 ^ length : Real) + 1 := by linarith
      _ <= 2 * (4 ^ length : Real) := by
        have hfour : (1 : Real) <= 4 ^ length := by
          exact_mod_cast Nat.one_le_pow length 4 (by norm_num)
        linarith
  have hlogUpper : Real.log X <= 10 * (length : Real) := by
    dsimp [X]
    rw [Nat.cast_pow, Real.log_pow]
    have hlog10 : Real.log (10 : Real) <= 9 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 10)
      linarith
    have hlen : 0 <= (length : Real) := by positivity
    calc
      (length : Real) * Real.log 10 <= (length : Real) * 9 := by
        exact mul_le_mul_of_nonneg_left hlog10 hlen
      _ <= (length : Real) * 10 :=
        mul_le_mul_of_nonneg_left (by norm_num : (9 : Real) <= 10) hlen
      _ = 10 * (length : Real) := by ring
  have hlenPow : (length : Real) <= (2 ^ length : Real) := by
    have hnat : length <= 2 ^ length := Nat.le_of_lt length.lt_two_pow_self
    exact_mod_cast hnat
  have hsmallLog :
      ((paddedRestrictedSmallPrimes digit length (sectionSixZFour X)).card : Real) *
          Real.log X <= 20 * (9 ^ length : Real) := by
    have hprod :
        ((paddedRestrictedSmallPrimes digit length (sectionSixZFour X)).card : Real) *
            Real.log X <= (2 * (4 ^ length : Real)) *
              (10 * (length : Real)) :=
      mul_le_mul hsmallPow hlogUpper (by positivity) (by positivity)
    have hpow48 : (4 ^ length : Real) * (2 ^ length : Real) = (8 ^ length : Real) := by
      rw [← mul_pow]
      norm_num
    have hpow89 : (8 ^ length : Real) <= (9 ^ length : Real) := by
      exact pow_le_pow_left₀ (by norm_num : (0 : Real) <= 8)
        (by norm_num : (8 : Real) <= 9) length
    calc
      ((paddedRestrictedSmallPrimes digit length (sectionSixZFour X)).card : Real) *
          Real.log X <= (2 * (4 ^ length : Real)) *
            (10 * (length : Real)) := hprod
      _ <= 20 * (4 ^ length : Real) * (2 ^ length : Real) := by
        nlinarith [hlenPow]
      _ = 20 * (8 ^ length : Real) := by
        calc
          20 * (4 ^ length : Real) * (2 ^ length : Real) =
              20 * ((4 ^ length : Real) * (2 ^ length : Real)) := by ring
          _ = 20 * (8 ^ length : Real) := by rw [hpow48]
      _ <= 20 * (9 ^ length : Real) := by nlinarith
  have hsmallDiv :
      ((paddedRestrictedSmallPrimes digit length (sectionSixZFour X)).card : Real) <=
        20 * (9 ^ length : Real) / Real.log X := by
    apply (le_div_iff₀ hlogPos).2
    exact hsmallLog
  have hcard :
      ((paddedRestrictedNumbers digit length).card : Real) = (9 ^ length : Real) := by
    rw [card_paddedRestrictedNumbers]
    norm_num
  have hsiftNorm :
      ((strictSiftedCarrier (paddedRestrictedNumbers digit length)
        (X ^ ((1 / 4 : Real) / 4))).card : Real) <=
        C0 * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X := by
    simpa [X] using hsift'
  rw [hcard] at hsiftNorm
  have hsum :
      (paddedRestrictedPrimeCount digit length : Real) <=
        C0 * (9 ^ length : Real) / Real.log X +
          20 * (9 ^ length : Real) / Real.log X := by
    exact hprimeReal.trans (add_le_add hsiftNorm hsmallDiv)
  rw [hcard]
  calc
    (paddedRestrictedPrimeCount digit length : Real) <=
        C0 * (9 ^ length : Real) / Real.log X +
          20 * (9 ^ length : Real) / Real.log X := hsum
    _ = (C0 + 20) * (9 ^ length : Real) / Real.log X := by ring

end

end PrimesRestrictedDigits
