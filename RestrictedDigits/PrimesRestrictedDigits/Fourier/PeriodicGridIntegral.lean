import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Integration over a finite periodic grid

Exact rescaling between adjacent grid cells.
-/

open scoped BigOperators Interval

namespace PrimesRestrictedDigits

/-- Partition `[0, 1]` into `N` equal cells and rescale every cell to `[0, 1]`. -/
theorem intervalIntegral_eq_inv_mul_grid_sum
    (f : Real -> Real) (hf : Continuous f) (N : Nat) (hN : 0 < N) :
    (∫ x in (0 : Real)..1, f x) =
      (N : Real)⁻¹ * ∫ u in (0 : Real)..1,
        ∑ a : Fin N, f (((a.val : Real) + u) / (N : Real)) := by
  have hN0 : (N : Real) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (μ := MeasureTheory.volume)
    (a := fun k : Nat => (k : Real) / (N : Real)) (n := N)
    (fun _ _ => hf.intervalIntegrable _ _)
  have hpartition' :
      (∑ a : Fin N,
        ∫ x in (a.val : Real) / (N : Real)..
          ((a.val + 1 : Nat) : Real) / (N : Real), f x) =
        ∫ x in (0 : Real)..1, f x := by
    calc
      _ = ∑ k ∈ Finset.range N,
          ∫ x in (k : Real) / (N : Real)..
            ((k + 1 : Nat) : Real) / (N : Real), f x :=
        Fin.sum_univ_eq_sum_range
          (fun k => ∫ x in (k : Real) / (N : Real)..
            ((k + 1 : Nat) : Real) / (N : Real), f x) N
      _ = ∫ x in (0 : Real) / (N : Real)..
          (N : Real) / (N : Real), f x := by
        simpa only [Nat.cast_zero] using hpartition
      _ = ∫ x in (0 : Real)..1, f x := by simp [hN0]
  have hcell (a : Fin N) :
      ((N : Real)⁻¹ * ∫ u in (0 : Real)..1,
        f (((a.val : Real) + u) / (N : Real))) =
        ∫ x in (a.val : Real) / (N : Real)..
          ((a.val + 1 : Nat) : Real) / (N : Real), f x := by
    have hchange := intervalIntegral.smul_integral_comp_add_mul
      (f := f) (a := (0 : Real)) (b := 1)
      ((N : Real)⁻¹) ((a.val : Real) / (N : Real))
    have hargument (u : Real) :
        ((a.val : Real) + u) / (N : Real) =
          (a.val : Real) / (N : Real) + (N : Real)⁻¹ * u := by
      simp only [div_eq_mul_inv]
      ring
    have hlower :
        (a.val : Real) / (N : Real) + (N : Real)⁻¹ * 0 =
          (a.val : Real) / (N : Real) := by ring
    have hupper :
        (a.val : Real) / (N : Real) + (N : Real)⁻¹ * 1 =
          ((a.val + 1 : Nat) : Real) / (N : Real) := by
      simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
      ring
    calc
      _ = (N : Real)⁻¹ * ∫ u in (0 : Real)..1,
          f ((a.val : Real) / (N : Real) + (N : Real)⁻¹ * u) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro u _
        change f (((a.val : Real) + u) / (N : Real)) =
          f ((a.val : Real) / (N : Real) + (N : Real)⁻¹ * u)
        rw [hargument]
      _ = ∫ x in (a.val : Real) / (N : Real) + (N : Real)⁻¹ * 0..
          (a.val : Real) / (N : Real) + (N : Real)⁻¹ * 1, f x := by
        simpa only [smul_eq_mul] using hchange
      _ = _ := by rw [hlower, hupper]
  calc
    (∫ x in (0 : Real)..1, f x) =
        ∑ a : Fin N,
          ∫ x in (a.val : Real) / (N : Real)..
            ((a.val + 1 : Nat) : Real) / (N : Real), f x := hpartition'.symm
    _ = ∑ a : Fin N, (N : Real)⁻¹ *
          ∫ u in (0 : Real)..1,
            f (((a.val : Real) + u) / (N : Real)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact (hcell a).symm
    _ = (N : Real)⁻¹ * ∑ a : Fin N,
          ∫ u in (0 : Real)..1,
            f (((a.val : Real) + u) / (N : Real)) := by
      rw [Finset.mul_sum]
    _ = (N : Real)⁻¹ * ∫ u in (0 : Real)..1,
          ∑ a : Fin N, f (((a.val : Real) + u) / (N : Real)) := by
      congr 1
      rw [intervalIntegral.integral_finsetSum]
      intro _ _
      exact (hf.comp (by fun_prop)).intervalIntegrable _ _

end PrimesRestrictedDigits
