import PrimesRestrictedDigits.SieveAsymptotics.FixedLengthPrimeUpperEnvelope
import PrimesRestrictedDigits.Foundations.CutoffMonotonicity
import PrimesRestrictedDigits.Foundations.DecimalScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nonzero-digit real-cutoff prime upper envelope

This transfers the fixed-length padded upper estimate to arbitrary real cutoffs for excluded
digits other than zero. The zero-digit block requires a separate layer decomposition and is
intentionally outside this module.

Source: `MAYNARD-PRD-PUBLISHED`, Sections 2 and 6.
-/

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 1200000 in
theorem exists_restrictedPrimeCount_upper_envelope_of_ne_zero :
    ∃ C : Real, 0 < C ∧
      ∃ X0 : Real, 4 <= X0 ∧
        ∀ digit : Fin 10, digit.val ≠ 0 ->
          ∀ X : Real, X0 <= X ->
            (restrictedPrimeCount digit X : Real) <=
              C * (restrictedCount digit X : Real) / Real.log X := by
  obtain ⟨C0, hC0, length0, hlength0, hupper⟩ :=
    exists_paddedRestrictedPrimeCount_upper_envelope
  let X0 : Real := ((10 ^ length0 : Nat) : Real)
  have hX0 : 4 <= X0 := by
    dsimp [X0]
    by_cases hzero : length0 = 0
    · subst length0
      norm_num at hlength0
    · have hpow : 10 <= 10 ^ length0 := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ (by norm_num : (1 : Nat) <= 10) hlength0)
      exact_mod_cast (show 4 <= 10 ^ length0 by omega)
  refine ⟨9 * C0, by positivity, X0, hX0, ?_⟩
  intro digit hdigit X hXX0
  have hX4 : 4 <= X := hX0.trans hXX0
  obtain ⟨k, hlo, hupp⟩ := exists_decimalPower_interval hX4
  have hXY : X <= ((10 ^ (k + 1) : Nat) : Real) := hupp.le
  have hpowEndpoint : ((10 ^ length0 : Nat) : Real) <
      ((10 ^ (k + 1) : Nat) : Real) := by
    exact lt_of_le_of_lt (by simpa [X0] using hXX0) hupp
  have hpowEndpointNat : 10 ^ length0 < 10 ^ (k + 1) := by
    exact_mod_cast hpowEndpoint
  have hlengthEndpoint : length0 < k + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (10 : Nat))).mp
      hpowEndpointNat
  have hlengthEndpointLe : length0 <= k + 1 := hlengthEndpoint.le
  have hendpoint := hupper (k + 1) hlengthEndpointLe digit
  dsimp only at hendpoint
  rw [paddedRestrictedPrimeCount_eq_restrictedPrimeCount_of_ne_zero
    hdigit (k + 1)] at hendpoint
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hY4 : 4 <= ((10 ^ (k + 1) : Nat) : Real) := hX4.trans hXY
  have hlogY : 0 < Real.log ((10 ^ (k + 1) : Nat) : Real) :=
    log_pos_of_four_le hY4
  have hlogOrder : Real.log X <=
      Real.log ((10 ^ (k + 1) : Nat) : Real) := by
    exact Real.log_le_log (by linarith) hXY
  have hprimeMonoNat := restrictedPrimeCount_le_of_le (a := digit) hXY
  have hprimeMono : (restrictedPrimeCount digit X : Real) <=
      (restrictedPrimeCount digit ((10 ^ (k + 1) : Nat) : Real) : Real) := by
    exact_mod_cast hprimeMonoNat
  have hcardY :
      ((paddedRestrictedNumbers digit (k + 1)).card : Real) =
        (9 : Real) ^ (k + 1) := by
    rw [card_paddedRestrictedNumbers]
    norm_num
  rw [hcardY] at hendpoint
  have hcountNat := restrictedCount_bounds_of_decimalPower_interval_of_ne_zero
    hdigit hlo hupp
  have hcountLower : ((9 : Real) ^ k) <=
      (restrictedCount digit X : Real) := by
    exact_mod_cast hcountNat.1
  have hnumBase : C0 * (9 : Real) ^ k <=
      C0 * (restrictedCount digit X : Real) :=
    mul_le_mul_of_nonneg_left hcountLower hC0.le
  have hnum : C0 * (9 : Real) ^ (k + 1) <=
      (9 * C0) * (restrictedCount digit X : Real) := by
    calc
      C0 * (9 : Real) ^ (k + 1) =
          9 * (C0 * (9 : Real) ^ k) := by rw [pow_succ]; ring
      _ <= 9 * (C0 * (restrictedCount digit X : Real)) :=
        mul_le_mul_of_nonneg_left hnumBase (by norm_num)
      _ = (9 * C0) * (restrictedCount digit X : Real) := by ring
  have hdenReplace :
      C0 * (9 : Real) ^ (k + 1) /
          Real.log ((10 ^ (k + 1) : Nat) : Real) <=
        C0 * (9 : Real) ^ (k + 1) / Real.log X :=
    div_le_div_of_nonneg_left (by positivity) hlogX hlogOrder
  have hnumReplace :
      C0 * (9 : Real) ^ (k + 1) / Real.log X <=
        (9 * C0) * (restrictedCount digit X : Real) / Real.log X :=
    div_le_div_of_nonneg_right hnum hlogX.le
  exact hprimeMono.trans ((hendpoint.trans hdenReplace).trans hnumReplace)

end

end PrimesRestrictedDigits
