import Mathlib.Tactic.Ring

/-!
# Finite differences of the fifth-power phase

The fourth forward difference is the linear phase used in Chen's Lemma 9
[CHEN1964-EN, pp. 1555-1557].
-/

namespace Waring.Analytic

/-- Forward difference with step `h`. -/
def forwardDifference {R : Type*} [Sub R] [Add R]
    (h : R) (f : R → R) (x : R) : R :=
  f (x + h) - f x

/-- The first difference of a fifth power, in collected form. -/
theorem forwardDifference_pow_five {R : Type*} [CommRing R] (x h : R) :
    forwardDifference h (fun y : R ↦ y ^ 5) x =
      5 * h * x ^ 4 + 10 * h ^ 2 * x ^ 3 + 10 * h ^ 3 * x ^ 2 +
        5 * h ^ 4 * x + h ^ 5 := by
  rw [forwardDifference]
  ring

/-- The variable-dependent quadratic part after three differences. -/
def fifthThirdDifferenceVariablePart {R : Type*} [CommRing R]
    (x h₁ h₂ h₃ : R) : R :=
  60 * h₁ * h₂ * h₃ * x * (x + h₁ + h₂ + h₃)

/-- Three differences equal their quadratic variable part plus the value at
zero.  This isolates the constant phase that later disappears inside a norm. -/
theorem forwardDifference_three_pow_five_eq_variablePart_add_constant
    {R : Type*} [CommRing R] (x h₁ h₂ h₃ : R) :
    forwardDifference h₃
        (forwardDifference h₂
          (forwardDifference h₁ (fun y : R ↦ y ^ 5))) x =
      fifthThirdDifferenceVariablePart x h₁ h₂ h₃ +
        forwardDifference h₃
          (forwardDifference h₂
            (forwardDifference h₁ (fun y : R ↦ y ^ 5))) 0 := by
  simp only [forwardDifference, fifthThirdDifferenceVariablePart]
  ring

/-- Differencing the quadratic variable part gives the affine fourth
difference. -/
theorem forwardDifference_fifthThirdDifferenceVariablePart
    {R : Type*} [CommRing R] (x h₁ h₂ h₃ h₄ : R) :
    forwardDifference h₄
        (fun y ↦ fifthThirdDifferenceVariablePart y h₁ h₂ h₃) x =
      120 * h₁ * h₂ * h₃ * h₄ * x +
        60 * h₁ * h₂ * h₃ * h₄ * (h₁ + h₂ + h₃ + h₄) := by
  simp only [forwardDifference, fifthThirdDifferenceVariablePart]
  ring

/-- Four forward differences of a fifth power form an affine polynomial with
slope `120*h₁*h₂*h₃*h₄`. -/
theorem forwardDifference_four_pow_five {R : Type*} [CommRing R]
    (x h₁ h₂ h₃ h₄ : R) :
    forwardDifference h₄
        (forwardDifference h₃
          (forwardDifference h₂
            (forwardDifference h₁ (fun y : R ↦ y ^ 5)))) x =
      120 * h₁ * h₂ * h₃ * h₄ * x +
        60 * h₁ * h₂ * h₃ * h₄ * (h₁ + h₂ + h₃ + h₄) := by
  simp only [forwardDifference]
  ring

end Waring.Analytic
