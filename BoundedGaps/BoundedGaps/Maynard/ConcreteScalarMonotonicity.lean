import BoundedGaps.Maynard.ConcreteRadiusLogAsymptotics

namespace BoundedGaps.Maynard

open Filter

/-! Monotonicity facts for the scalar distribution function. -/

theorem eventually_engelsmaMaynardRadius_mono_exponent
    {alpha beta : ℝ} (hαβ : alpha ≤ beta) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaMaynardRadius alpha N ≤ engelsmaMaynardRadius beta N := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  unfold engelsmaMaynardRadius maynardDivisorCutoff
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N - 1 by omega)) hαβ

theorem eventually_engelsmaSquarefreeMean_mono_exponent
    {alpha beta : ℝ} (hαβ : alpha ≤ beta) :
    ∀ᶠ N : ℕ in atTop,
      squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) ≤
        squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius beta N) := by
  filter_upwards [eventually_engelsmaMaynardRadius_mono_exponent hαβ] with
    N hN
  exact squarefreeCoprimeInvTotientMean_mono_cutoff hN

end BoundedGaps.Maynard
