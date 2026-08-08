import Waring.Analytic.ZModCharacterCorrelation

/-!
# The quadratic phase after three fifth-power differences

This file packages Chen's quadratic third-difference phase over `ZMod q` and
computes its positive-shift correlation.
-/

namespace Waring.Analytic

open scoped ComplexConjugate

/-- The standard-character phase contributed by the variable part of three
fifth-power differences. -/
noncomputable def fifthQuadraticChar {q : Nat} [NeZero q] (a : ZMod q)
    (h₁ h₂ h₃ y : Nat) : Complex :=
  ZMod.stdAddChar
    (a * fifthThirdDifferenceVariablePart
      (y : ZMod q) (h₁ : ZMod q) (h₂ : ZMod q) (h₃ : ZMod q))

/-- The difference of two shifted quadratic phases is affine, with the
constant term separated from the term linear in `y`. -/
theorem fifthQuadraticPhase_sub {q : Nat} [NeZero q] (a : ZMod q)
    (h₁ h₂ h₃ y l : Nat) :
    a * fifthThirdDifferenceVariablePart
          ((y + l : Nat) : ZMod q) (h₁ : ZMod q) (h₂ : ZMod q)
            (h₃ : ZMod q) -
        a * fifthThirdDifferenceVariablePart
          (y : ZMod q) (h₁ : ZMod q) (h₂ : ZMod q) (h₃ : ZMod q) =
      a * (60 * (h₁ : ZMod q) * (h₂ : ZMod q) * (h₃ : ZMod q) *
        (l : ZMod q) * ((h₁ : ZMod q) + (h₂ : ZMod q) +
          (h₃ : ZMod q) + (l : ZMod q))) +
      a * (120 * (h₁ : ZMod q) * (h₂ : ZMod q) * (h₃ : ZMod q) *
        (l : ZMod q) * (y : ZMod q)) := by
  have hdifference :=
    forwardDifference_fifthThirdDifferenceVariablePart
      (R := ZMod q) (y : ZMod q) (h₁ : ZMod q) (h₂ : ZMod q)
        (h₃ : ZMod q) (l : ZMod q)
  simp only [forwardDifference] at hdifference
  push_cast at hdifference ⊢
  calc
    a * fifthThirdDifferenceVariablePart
          ((y : ZMod q) + l) (h₁ : ZMod q) h₂ h₃ -
          a * fifthThirdDifferenceVariablePart
            (y : ZMod q) (h₁ : ZMod q) h₂ h₃ =
        a * (fifthThirdDifferenceVariablePart
          ((y : ZMod q) + l) (h₁ : ZMod q) h₂ h₃ -
          fifthThirdDifferenceVariablePart
            (y : ZMod q) (h₁ : ZMod q) h₂ h₃) := by ring
    _ = a * (120 * (h₁ : ZMod q) * h₂ * h₃ * l * y +
        60 * (h₁ : ZMod q) * h₂ * h₃ * l *
          ((h₁ : ZMod q) + h₂ + h₃ + l)) := by
      rw [hdifference]
    _ = a * (60 * (h₁ : ZMod q) * h₂ * h₃ * l *
          ((h₁ : ZMod q) + h₂ + h₃ + l)) +
        a * (120 * (h₁ : ZMod q) * h₂ * h₃ * l * y) := by ring

/-- A shifted quadratic-character correlation is a constant unit factor
times a linear character in the lower endpoint. -/
theorem fifthQuadraticChar_mul_conj {q : Nat} [NeZero q] (a : ZMod q)
    (h₁ h₂ h₃ y l : Nat) :
    fifthQuadraticChar a h₁ h₂ h₃ (y + l) *
        conj (fifthQuadraticChar a h₁ h₂ h₃ y) =
      ZMod.stdAddChar
          (a * (60 * (h₁ : ZMod q) * (h₂ : ZMod q) * (h₃ : ZMod q) *
            (l : ZMod q) * ((h₁ : ZMod q) + (h₂ : ZMod q) +
              (h₃ : ZMod q) + (l : ZMod q)))) *
        ZMod.stdAddChar
          (a * (120 * (h₁ : ZMod q) * (h₂ : ZMod q) * (h₃ : ZMod q) *
            (l : ZMod q) * (y : ZMod q))) := by
  rw [fifthQuadraticChar, fifthQuadraticChar, stdAddChar_mul_conj]
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  exact fifthQuadraticPhase_sub a h₁ h₂ h₃ y l

-- The nonzero modulus stays in this phase identity because it is part of the
-- reviewed character-correlation API even though the polynomial identity is general.
attribute [nolint unusedArguments] fifthQuadraticPhase_sub

end Waring.Analytic
