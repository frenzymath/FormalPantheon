import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Complete exponential sums

This file fixes the additive-character convention used for Chen's complete
power sums.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- A complete power sum attached to an additive character on a finite
semiring. -/
noncomputable def powerSum {R : Type*} [Semiring R] [Fintype R]
    (character : AddChar R Complex) (k : Nat) (a : R) : Complex :=
  ∑ x : R, character (a * x ^ k)

/-- The complete `k`th-power exponential sum modulo a nonzero natural `q`. -/
noncomputable def completePowerSum {q : Nat} [NeZero q] (k : Nat) (a : ZMod q) : Complex :=
  powerSum ZMod.stdAddChar k a

/-- Every summand in a complete power sum has complex norm one. -/
theorem norm_stdAddChar (q : Nat) [NeZero q] (x : ZMod q) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- The trivial triangle-inequality bound for a complete power sum. -/
theorem norm_completePowerSum_le {q : Nat} [NeZero q] (k : Nat) (a : ZMod q) :
    ‖completePowerSum k a‖ ≤ q := by
  rw [completePowerSum]
  rw [powerSum]
  calc
    ‖∑ x : ZMod q, ZMod.stdAddChar (a * x ^ k)‖ ≤
        ∑ x : ZMod q, ‖ZMod.stdAddChar (a * x ^ k)‖ := norm_sum_le _ _
    _ = q := by simp

/-- Orthogonality of the standard additive character after a multiplicative
shift. This is the cancellation identity used when Chen splits a complete sum
into residue blocks. -/
theorem sum_stdAddChar_mul {q : Nat} [NeZero q] (a : ZMod q) :
    ∑ x : ZMod q, ZMod.stdAddChar (x * a) = if a = 0 then q else 0 := by
  simpa using AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar q)

end Waring.Analytic
