import Waring.Analytic.WeylFifthDifferences
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Correlations of the standard additive character

This file records the conjugate-correlation identity used to turn a phase
difference into one standard additive character.
-/

namespace Waring.Analytic

open scoped ComplexConjugate

/-- Multiplying a standard additive character by the conjugate of another
value gives the character of their difference. -/
theorem stdAddChar_mul_conj {q : Nat} [NeZero q] (u v : ZMod q) :
    ZMod.stdAddChar u * conj (ZMod.stdAddChar v) =
      ZMod.stdAddChar (u - v) := by
  have hvNorm : ‖ZMod.stdAddChar v‖ = 1 := by norm_num
  calc
    ZMod.stdAddChar u * conj (ZMod.stdAddChar v) =
        ZMod.stdAddChar u * (ZMod.stdAddChar v)⁻¹ := by
      rw [Complex.inv_eq_conj hvNorm]
    _ = ZMod.stdAddChar u * ZMod.stdAddChar (-v) := by
      rw [AddChar.map_neg_eq_inv]
    _ = ZMod.stdAddChar (u - v) := by
      rw [sub_eq_add_neg, ZMod.stdAddChar.map_add_eq_mul]

end Waring.Analytic
