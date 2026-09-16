import PrimesRestrictedDigits.SieveAsymptotics.StrictNonzeroRealCutoffPrimeUpperEnvelope
import PrimesRestrictedDigits.SieveAsymptotics.ZeroPrimeUpperEnvelope
import PrimesRestrictedDigits.Foundations.RestrictedCountPositivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Uniform strict upper envelope

The excluded-zero and nonzero branches are combined after their independent thresholds and
coefficients have been chosen.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_restrictedPrimeCount_strict_upper_envelope :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 4 <= X0 ∧
      ∀ digit : Fin 10, ∀ X : Real, X0 <= X ->
        (restrictedPrimeCount digit X : Real) <
          C * ((restrictedCount digit X : Real) / Real.log X) := by
  obtain ⟨Cz, hCz, Xz, hXz, hzero⟩ :=
    exists_restrictedPrimeCount_strict_upper_envelope_of_zero
  obtain ⟨Cn, hCn, Xn, hXn, hnonzero⟩ :=
    exists_restrictedPrimeCount_strict_upper_envelope_of_ne_zero
  let C : Real := max Cz Cn
  let X0 : Real := max Xz Xn
  have hC : 0 < C := by
    dsimp [C]
    exact (hCz.trans_le (le_max_left _ _))
  have hX0 : 4 <= X0 := by
    dsimp [X0]
    exact hXz.trans (le_max_left _ _)
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro digit X hX
  by_cases hdigit : digit.val = 0
  · have hdigit0 : digit = (0 : Fin 10) := Fin.ext hdigit
    subst digit
    have hbranch := hzero X (le_max_left Xz Xn |>.trans hX)
    have hratio : 0 <
        (restrictedCount (0 : Fin 10) X : Real) / Real.log X :=
      div_pos (restrictedCount_pos_of_four_le (hX0.trans hX))
        (log_pos_of_four_le (hX0.trans hX))
    have hcoef : Cz *
        ((restrictedCount (0 : Fin 10) X : Real) / Real.log X) <=
        C * ((restrictedCount (0 : Fin 10) X : Real) / Real.log X) := by
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hratio.le
    exact hbranch.trans_le hcoef
  · have hbranch := hnonzero digit hdigit X
      (le_max_right Xz Xn |>.trans hX)
    have hratio : 0 <
        (restrictedCount digit X : Real) / Real.log X :=
      div_pos (restrictedCount_pos_of_four_le (hX0.trans hX))
        (log_pos_of_four_le (hX0.trans hX))
    have hcoef : Cn *
        ((restrictedCount digit X : Real) / Real.log X) <=
        C * ((restrictedCount digit X : Real) / Real.log X) := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hratio.le
    exact hbranch.trans_le hcoef

end

end PrimesRestrictedDigits
