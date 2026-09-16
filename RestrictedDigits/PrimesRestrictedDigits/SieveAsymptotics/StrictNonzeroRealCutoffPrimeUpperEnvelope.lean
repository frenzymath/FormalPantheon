import PrimesRestrictedDigits.SieveAsymptotics.NonzeroRealCutoffPrimeUpperEnvelope
import PrimesRestrictedDigits.Foundations.RestrictedCountPositivity
import Mathlib.Tactic.Linarith

/-!
# Strict nonzero-digit real-cutoff prime upper envelope

The weak endpoint transfer is made strict by the elementary positivity of the
restricted carrier and logarithmic denominator.  This is a coefficient change,
not a new prime estimate.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_restrictedPrimeCount_strict_upper_envelope_of_ne_zero :
    ∃ C : Real, 0 < C ∧
      ∃ X0 : Real, 4 <= X0 ∧
        ∀ digit : Fin 10, digit.val ≠ 0 ->
          ∀ X : Real, X0 <= X ->
            (restrictedPrimeCount digit X : Real) <
              C * ((restrictedCount digit X : Real) / Real.log X) := by
  obtain ⟨C0, hC0, X0, hX0, hweak⟩ :=
    exists_restrictedPrimeCount_upper_envelope_of_ne_zero
  refine ⟨2 * C0, by positivity, X0, hX0, ?_⟩
  intro digit hdigit X hX
  have hweak' := hweak digit hdigit X hX
  have hlog : 0 < Real.log X := log_pos_of_four_le (hX0.trans hX)
  have hcount : 0 < (restrictedCount digit X : Real) :=
    restrictedCount_pos_of_four_le (hX0.trans hX)
  have hratio : 0 < (restrictedCount digit X : Real) / Real.log X :=
    div_pos hcount hlog
  have hCratio : 0 < C0 *
      ((restrictedCount digit X : Real) / Real.log X) :=
    mul_pos hC0 hratio
  calc
    (restrictedPrimeCount digit X : Real) ≤
        C0 * ((restrictedCount digit X : Real) / Real.log X) := by
      convert hweak' using 1; ring
    _ < (2 * C0) *
        ((restrictedCount digit X : Real) / Real.log X) := by
      nlinarith

end

end PrimesRestrictedDigits
