import Waring.Analytic.WeylQuadraticPhase
import Waring.Analytic.WeylThreeStep

/-!
# Three correlations of the fifth-power character phase

This file identifies the three-times-correlated fifth-power phase with the
quadratic phase used in Chen's Lemma 9 [CHEN1964-EN, pp. 1555-1557].
-/

namespace Waring.Analytic

open scoped BigOperators ComplexConjugate

/-- A polynomial phase sampled on the positive integers, with zero-based
index `x` representing the integer `x + 1`. -/
noncomputable def shiftedStdAddCharPhase {q : Nat} [NeZero q]
    (a : ZMod q) (f : ZMod q → ZMod q) (x : Nat) : Complex :=
  ZMod.stdAddChar (a * f ((x + 1 : Nat) : ZMod q))

/-- Positive correlation of a sampled character phase is the sampled forward
difference with the actual shift `h + 1`. -/
theorem positiveShiftCorrelation_shiftedStdAddCharPhase
    {q : Nat} [NeZero q] (a : ZMod q) (f : ZMod q → ZMod q)
    (h x : Nat) :
    positiveShiftCorrelation (shiftedStdAddCharPhase a f) h x =
      shiftedStdAddCharPhase a
        (forwardDifference ((h + 1 : Nat) : ZMod q) f) x := by
  unfold positiveShiftCorrelation shiftedStdAddCharPhase
  rw [stdAddChar_mul_conj]
  congr 1
  simp only [forwardDifference]
  push_cast
  ring_nf

/-- The fifth-power character sequence on the positive interval
`1, ..., P`. -/
noncomputable def fifthPowerChar {q : Nat} [NeZero q]
    (a : ZMod q) (x : Nat) : Complex :=
  shiftedStdAddCharPhase a (fun y : ZMod q ↦ y ^ 5) x

/-- The fifth-power character sequence lies on the complex unit circle. -/
theorem norm_fifthPowerChar_eq_one {q : Nat} [NeZero q]
    (a : ZMod q) (x : Nat) :
    ‖fifthPowerChar a x‖ = 1 := by
  unfold fifthPowerChar shiftedStdAddCharPhase
  norm_num

/-- Three positive correlations are the character of the full third forward
difference, evaluated at the positive base point `y + 1`. -/
theorem three_positiveShiftCorrelation_fifthPowerChar
    {q : Nat} [NeZero q] (a : ZMod q) (h₁ h₂ h₃ y : Nat) :
    positiveShiftCorrelation
        (positiveShiftCorrelation
          (positiveShiftCorrelation (fifthPowerChar a) h₁) h₂) h₃ y =
      shiftedStdAddCharPhase a
        (forwardDifference ((h₃ + 1 : Nat) : ZMod q)
          (forwardDifference ((h₂ + 1 : Nat) : ZMod q)
            (forwardDifference ((h₁ + 1 : Nat) : ZMod q)
              (fun x : ZMod q ↦ x ^ 5)))) y := by
  have hfirst :
      positiveShiftCorrelation (fifthPowerChar a) h₁ =
        shiftedStdAddCharPhase a
          (forwardDifference ((h₁ + 1 : Nat) : ZMod q)
            (fun x : ZMod q ↦ x ^ 5)) := by
    funext x
    exact positiveShiftCorrelation_shiftedStdAddCharPhase a _ h₁ x
  have hsecond :
      positiveShiftCorrelation
          (shiftedStdAddCharPhase a
            (forwardDifference ((h₁ + 1 : Nat) : ZMod q)
              (fun x : ZMod q ↦ x ^ 5))) h₂ =
        shiftedStdAddCharPhase a
          (forwardDifference ((h₂ + 1 : Nat) : ZMod q)
            (forwardDifference ((h₁ + 1 : Nat) : ZMod q)
              (fun x : ZMod q ↦ x ^ 5))) := by
    funext x
    exact positiveShiftCorrelation_shiftedStdAddCharPhase a _ h₂ x
  rw [hfirst, hsecond]
  exact positiveShiftCorrelation_shiftedStdAddCharPhase a _ h₃ y

/-- The full third-difference character is a constant unit factor times its
quadratic variable part. -/
theorem three_positiveShiftCorrelation_fifthPowerChar_eq_mul
    {q : Nat} [NeZero q] (a : ZMod q) (h₁ h₂ h₃ y : Nat) :
    positiveShiftCorrelation
        (positiveShiftCorrelation
          (positiveShiftCorrelation (fifthPowerChar a) h₁) h₂) h₃ y =
      ZMod.stdAddChar
          (a * forwardDifference ((h₃ + 1 : Nat) : ZMod q)
            (forwardDifference ((h₂ + 1 : Nat) : ZMod q)
              (forwardDifference ((h₁ + 1 : Nat) : ZMod q)
                (fun x : ZMod q ↦ x ^ 5))) 0) *
        fifthQuadraticChar a (h₁ + 1) (h₂ + 1) (h₃ + 1) (y + 1) := by
  rw [three_positiveShiftCorrelation_fifthPowerChar]
  unfold shiftedStdAddCharPhase fifthQuadraticChar
  rw [forwardDifference_three_pow_five_eq_variablePart_add_constant]
  rw [mul_add, ZMod.stdAddChar.map_add_eq_mul]
  ring

/-- The constant third-difference phase factors out of the exact remaining
finite sum. -/
theorem thirdPositiveShiftSum_fifthPowerChar_eq_mul
    {q : Nat} [NeZero q] (a : ZMod q) (P h₁ h₂ h₃ : Nat) :
    thirdPositiveShiftSum (fifthPowerChar a) P h₁ h₂ h₃ =
      ZMod.stdAddChar
          (a * forwardDifference ((h₃ + 1 : Nat) : ZMod q)
            (forwardDifference ((h₂ + 1 : Nat) : ZMod q)
              (forwardDifference ((h₁ + 1 : Nat) : ZMod q)
                (fun x : ZMod q ↦ x ^ 5))) 0) *
        ∑ y ∈ Finset.range (P - h₁ - 1 - h₂ - 1 - h₃ - 1),
          fifthQuadraticChar a (h₁ + 1) (h₂ + 1) (h₃ + 1) (y + 1) := by
  unfold thirdPositiveShiftSum
  simp_rw [three_positiveShiftCorrelation_fifthPowerChar_eq_mul]
  rw [Finset.mul_sum]

/-- Taking the norm removes the constant phase, leaving exactly the
restricted quadratic sum for the three actual positive shifts. -/
theorem norm_thirdPositiveShiftSum_fifthPowerChar_eq
    {q : Nat} [NeZero q] (a : ZMod q) (P h₁ h₂ h₃ : Nat) :
    ‖thirdPositiveShiftSum (fifthPowerChar a) P h₁ h₂ h₃‖ =
      ‖∑ y ∈ Finset.range (P - h₁ - 1 - h₂ - 1 - h₃ - 1),
        fifthQuadraticChar a (h₁ + 1) (h₂ + 1) (h₃ + 1) (y + 1)‖ := by
  rw [thirdPositiveShiftSum_fifthPowerChar_eq_mul, norm_mul]
  have hconstant :
      ‖ZMod.stdAddChar
          (a * forwardDifference ((h₃ + 1 : Nat) : ZMod q)
            (forwardDifference ((h₂ + 1 : Nat) : ZMod q)
              (forwardDifference ((h₁ + 1 : Nat) : ZMod q)
                (fun x : ZMod q ↦ x ^ 5))) 0)‖ = 1 := by
    norm_num
  rw [hconstant, one_mul]

end Waring.Analytic
