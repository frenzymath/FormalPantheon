import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardStrictRoughCountSqrtLowerParameterized
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum

/-!
# Decimal-length strict square-root rough-count lower envelope

The real-cutoff strict rough-count lower bound can be restricted to the decimal powers used by
the fixed-length Section 6 identity. The threshold is uniform because no digit parameter
occurs in the upstream statement.

Source: `MAYNARD-PRD-PUBLISHED`, Sections 5--6.
-/

namespace PrimesRestrictedDigits

open Filter

theorem exists_maynardStrictRoughCount_decimalLength_lower_of_lt_one
    {c : Real} (hc : 0 < c) (hc1 : c < 1) :
    ∃ length0 : Nat, 1 ≤ length0 ∧ ∀ length : Nat, length0 ≤ length ->
      let X : Real := ((10 ^ length : Nat) : Real)
      c * (X / Real.log X) ≤
        (maynardStrictRoughCount X (Real.sqrt X) : Real) := by
  obtain ⟨Y0, _, hY⟩ :=
    exists_maynardStrictRoughCount_sqrt_lower_of_lt_one hc hc1
  have hscale : Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
      atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  obtain ⟨lengthY, hlengthY⟩ :=
    eventually_atTop.mp (hscale.eventually_ge_atTop Y0)
  let length0 : Nat := max 1 lengthY
  refine ⟨length0, ?_, ?_⟩
  · exact Nat.le_max_left _ _
  · intro length hlength
    have hlengthY' : lengthY ≤ length :=
      (Nat.le_max_right 1 lengthY).trans hlength
    have hX : Y0 ≤ ((10 ^ length : Nat) : Real) :=
      hlengthY length hlengthY'
    have hmain := hY _ hX
    simpa only using hmain

end PrimesRestrictedDigits
