import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Centered real phase representatives

Reduce arbitrary normalized phases modulo one while retaining exact sine and
cosine values. The centered representative feeds global Taylor bounds.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

theorem cos_two_pi_mul_eq_fract (y : ℝ) :
    Real.cos (2 * Real.pi * y) =
      Real.cos (2 * Real.pi * Int.fract y) := by
  have hy : y = (Int.floor y : ℝ) + Int.fract y :=
    (Int.floor_add_fract y).symm
  have harg : 2 * Real.pi * y =
      (2 * Real.pi * Int.fract y) + (Int.floor y : ℝ) * (2 * Real.pi) := by
    calc
      2 * Real.pi * y = 2 * Real.pi * ((Int.floor y : ℝ) + Int.fract y) :=
        congrArg (fun z : ℝ => 2 * Real.pi * z) hy
      _ = (2 * Real.pi * Int.fract y) + (Int.floor y : ℝ) * (2 * Real.pi) := by
        ring
  rw [harg]
  exact Real.cos_add_int_mul_two_pi _ _

theorem sin_two_pi_mul_eq_fract (y : ℝ) :
    Real.sin (2 * Real.pi * y) =
      Real.sin (2 * Real.pi * Int.fract y) := by
  have hy : y = (Int.floor y : ℝ) + Int.fract y :=
    (Int.floor_add_fract y).symm
  have harg : 2 * Real.pi * y =
      (2 * Real.pi * Int.fract y) + (Int.floor y : ℝ) * (2 * Real.pi) := by
    calc
      2 * Real.pi * y = 2 * Real.pi * ((Int.floor y : ℝ) + Int.fract y) :=
        congrArg (fun z : ℝ => 2 * Real.pi * z) hy
      _ = (2 * Real.pi * Int.fract y) + (Int.floor y : ℝ) * (2 * Real.pi) := by
        ring
  rw [harg]
  exact Real.sin_add_int_mul_two_pi _ _

theorem two_pi_fract_bound (y : ℝ) :
    |2 * Real.pi * Int.fract y| ≤ 2 * Real.pi := by
  have hnonneg := Int.fract_nonneg y
  have hlt := Int.fract_lt_one y
  rw [abs_of_nonneg]
  · have hmul := mul_le_mul_of_nonneg_left hlt.le
        (by positivity : 0 ≤ 2 * Real.pi)
    simpa using hmul
  · positivity

noncomputable def centeredFract (y : ℝ) : ℝ :=
  Int.fract (y + 1 / 2) - 1 / 2

theorem centeredFract_decomp (y : ℝ) :
    y = (Int.floor (y + 1 / 2) : ℝ) + centeredFract y := by
  rw [centeredFract]
  have h := Int.floor_add_fract (y + 1 / 2)
  linarith

theorem centeredFract_mem (y : ℝ) :
    centeredFract y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  rw [centeredFract]
  constructor
  · have h := Int.fract_nonneg (y + 1 / 2)
    linarith
  · have h := Int.fract_lt_one (y + 1 / 2)
    linarith

theorem cos_two_pi_mul_eq_centeredFract (y : ℝ) :
    Real.cos (2 * Real.pi * y) =
      Real.cos (2 * Real.pi * centeredFract y) := by
  have hy := centeredFract_decomp y
  have harg : 2 * Real.pi * y =
      (2 * Real.pi * centeredFract y) +
        (Int.floor (y + 1 / 2) : ℝ) * (2 * Real.pi) := by
    calc
      2 * Real.pi * y =
          2 * Real.pi * ((Int.floor (y + 1 / 2) : ℝ) + centeredFract y) :=
        congrArg (fun z : ℝ => 2 * Real.pi * z) hy
      _ = (2 * Real.pi * centeredFract y) +
          (Int.floor (y + 1 / 2) : ℝ) * (2 * Real.pi) := by ring
  rw [harg]
  exact Real.cos_add_int_mul_two_pi _ _

theorem sin_two_pi_mul_eq_centeredFract (y : ℝ) :
    Real.sin (2 * Real.pi * y) =
      Real.sin (2 * Real.pi * centeredFract y) := by
  have hy := centeredFract_decomp y
  have harg : 2 * Real.pi * y =
      (2 * Real.pi * centeredFract y) +
        (Int.floor (y + 1 / 2) : ℝ) * (2 * Real.pi) := by
    calc
      2 * Real.pi * y =
          2 * Real.pi * ((Int.floor (y + 1 / 2) : ℝ) + centeredFract y) :=
        congrArg (fun z : ℝ => 2 * Real.pi * z) hy
      _ = (2 * Real.pi * centeredFract y) +
          (Int.floor (y + 1 / 2) : ℝ) * (2 * Real.pi) := by ring
  rw [harg]
  exact Real.sin_add_int_mul_two_pi _ _

theorem two_pi_centeredFract_bound (y : ℝ) :
    |2 * Real.pi * centeredFract y| ≤ 22 / 7 := by
  have hr := centeredFract_mem y
  have hpi : Real.pi ≤ 22 / 7 := by
    nlinarith [Real.pi_lt_d6]
  have habs : |centeredFract y| ≤ (1 / 2 : ℝ) := by
    exact (abs_le).2 hr
  calc
    |2 * Real.pi * centeredFract y| =
        2 * Real.pi * |centeredFract y| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ 2 * Real.pi * (1 / 2 : ℝ) := by
      gcongr
    _ = Real.pi := by ring
    _ ≤ 22 / 7 := hpi

end PrimesRestrictedDigits
