import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed-parameter preparation for the large-delta reduction

These are the elementary parameter and endpoint facts.
-/

open Filter

namespace PrimesRestrictedDigits

theorem fundamentalLargeDelta_parameter_bounds
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    0 < epsilon ^ (4 : Nat) ∧
      epsilon ^ (4 : Nat) <= 50 / 77 - epsilon ∧
      epsilon ^ (4 : Nat) <= epsilon ∧
      epsilon ^ (4 : Nat) + (50 / 77 - epsilon) <= 1 := by
  have hepsilonOne : epsilon <= 1 := by linarith
  have hpow4 : epsilon ^ (4 : Nat) <= epsilon := by
    calc
      epsilon ^ (4 : Nat) = epsilon * epsilon ^ (3 : Nat) := by ring
      _ <= epsilon * 1 := by
        have hp : epsilon ^ (3 : Nat) <= (1 : Real) := by
          have hp' := pow_le_pow_left₀ (by positivity) hepsilonOne 3
          simpa using hp'
        gcongr
      _ = epsilon := by ring
  exact ⟨by positivity, by nlinarith, hpow4, by nlinarith⟩

theorem exists_decimalEndpointThreshold
    (delta0 : Real) (hdelta0 : 0 < delta0) :
    ∃ length0 : Nat, ∀ length : Nat, length0 <= length ->
      1 <= length ∧
        5 <= ((10 ^ length : Nat) : Real) ^ delta0 ∧
        1 <= Real.log ((10 ^ length : Nat) : Real) := by
  have hXfunTendsto :
      Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
        atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hpowTendsto :
      Tendsto
        (fun length : Nat =>
          ((10 ^ length : Nat) : Real) ^ delta0) atTop atTop :=
    (tendsto_rpow_atTop hdelta0).comp hXfunTendsto
  have hlogTendsto :
      Tendsto
        (fun length : Nat =>
          Real.log ((10 ^ length : Nat) : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp hXfunTendsto
  have hendpointEventually : ∀ᶠ length : Nat in atTop,
      1 <= length ∧
        5 <= ((10 ^ length : Nat) : Real) ^ delta0 ∧
        1 <= Real.log ((10 ^ length : Nat) : Real) := by
    filter_upwards [eventually_ge_atTop (1 : Nat),
      hpowTendsto.eventually_ge_atTop (5 : Real),
      hlogTendsto.eventually_ge_atTop (1 : Real)] with length hlen hy hlog
    exact ⟨hlen, hy, hlog⟩
  exact eventually_atTop.mp hendpointEventually

end PrimesRestrictedDigits
