import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Centered rational decomposition

Euclidean division gives exact integer-plus-rational representatives in a
centered half-open interval. The denominator `100000` specialization is the
arithmetic phase reducer for five-digit endpoint cells.
-/

namespace PrimesRestrictedDigits

def centeredIntegerPart (numerator denominator : ℤ) : ℤ :=
  (numerator + denominator / 2) / denominator

def centeredRationalPart (numerator denominator : ℤ) : ℚ :=
  ((numerator - centeredIntegerPart numerator denominator * denominator : ℤ) : ℚ) /
    (denominator : ℚ)

theorem centeredResidualNumerator_eq_emod_sub_half
    (numerator denominator : ℤ) :
    numerator - centeredIntegerPart numerator denominator * denominator =
      (numerator + denominator / 2) % denominator - denominator / 2 := by
  have hdivision :=
    Int.ediv_mul_add_emod (numerator + denominator / 2) denominator
  simp only [centeredIntegerPart]
  omega

theorem centeredResidualNumerator_bounds (numerator denominator : ℤ)
    (hdenominator : 0 < denominator) (heven : Even denominator) :
    -(denominator / 2) ≤
        numerator - centeredIntegerPart numerator denominator * denominator ∧
      numerator - centeredIntegerPart numerator denominator * denominator <
        denominator / 2 := by
  have hnonzero : denominator ≠ 0 := ne_of_gt hdenominator
  have hremainder_nonnegative :
      0 ≤ (numerator + denominator / 2) % denominator :=
    Int.emod_nonneg _ hnonzero
  have hremainder_lt :
      (numerator + denominator / 2) % denominator < denominator :=
    Int.emod_lt_of_pos _ hdenominator
  have hhalf : denominator / 2 * 2 = denominator :=
    Int.ediv_mul_cancel heven.two_dvd
  rw [centeredResidualNumerator_eq_emod_sub_half]
  omega

theorem centeredRationalPart_decomposition (numerator denominator : ℤ)
    (hdenominator : denominator ≠ 0) :
    (numerator : ℚ) / (denominator : ℚ) =
      (centeredIntegerPart numerator denominator : ℚ) +
        centeredRationalPart numerator denominator := by
  have hdenominator_cast : (denominator : ℚ) ≠ 0 := by
    exact_mod_cast hdenominator
  simp only [centeredRationalPart]
  field_simp [hdenominator_cast]
  push_cast
  ring

theorem abs_centeredRationalPart_le_half (numerator denominator : ℤ)
    (hdenominator : 0 < denominator) (heven : Even denominator) :
    |centeredRationalPart numerator denominator| ≤ (1 : ℚ) / 2 := by
  have hbounds :=
    centeredResidualNumerator_bounds numerator denominator hdenominator heven
  have hhalf : denominator / 2 * 2 = denominator :=
    Int.ediv_mul_cancel heven.two_dvd
  have hdenominator_rat : 0 < (denominator : ℚ) := by
    exact_mod_cast hdenominator
  have hlower :
      -((denominator / 2 : ℤ) : ℚ) ≤
        ((numerator - centeredIntegerPart numerator denominator * denominator : ℤ) : ℚ) := by
    exact_mod_cast hbounds.1
  have hupper :
      ((numerator - centeredIntegerPart numerator denominator * denominator : ℤ) : ℚ) ≤
        ((denominator / 2 : ℤ) : ℚ) := by
    exact_mod_cast hbounds.2.le
  have hhalf_rat :
      ((denominator / 2 : ℤ) : ℚ) = (denominator : ℚ) / 2 := by
    have hhalf_cast := congrArg (fun z : ℤ => (z : ℚ)) hhalf
    norm_num at hhalf_cast ⊢
    linarith
  rw [abs_le]
  constructor
  · simp only [centeredRationalPart]
    rw [le_div_iff₀ hdenominator_rat]
    rw [hhalf_rat] at hlower
    linarith
  · simp only [centeredRationalPart]
    rw [div_le_iff₀ hdenominator_rat]
    rw [hhalf_rat] at hupper
    linarith

theorem centeredIntegerRationalDecomposition_real
    (numerator denominator : ℤ) (hdenominator : 0 < denominator)
    (heven : Even denominator) :
    (numerator : ℝ) / (denominator : ℝ) =
        (centeredIntegerPart numerator denominator : ℝ) +
          (centeredRationalPart numerator denominator : ℝ) ∧
      |(centeredRationalPart numerator denominator : ℝ)| ≤ (1 : ℝ) / 2 := by
  constructor
  · have hdecomp := centeredRationalPart_decomposition numerator denominator
      (ne_of_gt hdenominator)
    exact_mod_cast hdecomp
  · have hbound :=
      abs_centeredRationalPart_le_half numerator denominator hdenominator heven
    have hbound_cast :
        ((|centeredRationalPart numerator denominator| : ℚ) : ℝ) ≤
          (((1 : ℚ) / 2 : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr hbound
    simpa using hbound_cast

theorem centeredIntegerRationalDecomposition_100000 (numerator : ℤ) :
    (numerator : ℝ) / 100000 =
        (centeredIntegerPart numerator 100000 : ℝ) +
          (centeredRationalPart numerator 100000 : ℝ) ∧
      |(centeredRationalPart numerator 100000 : ℝ)| ≤ (1 : ℝ) / 2 := by
  exact centeredIntegerRationalDecomposition_real numerator 100000 (by norm_num)
    (by exact ⟨50000, by norm_num⟩)

end PrimesRestrictedDigits
