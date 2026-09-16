import PrimesRestrictedDigits.Fourier.LInfLocal
import PrimesRestrictedDigits.MajorArcs.Phase
import Mathlib.Tactic.FieldSimp

/-!
# Phase algebra and the capped nearest-integer kernel

The kernel is total at integral phases, where it has the full cap rather than the value zero
produced by a literal reciprocal in Lean.
-/

namespace PrimesRestrictedDigits

open ComplexConjugate

theorem majorArcPhase_add_eq_mul (x y : Real) :
    majorArcPhase (x + y) = majorArcPhase x * majorArcPhase y := by
  rw [majorArcPhase, majorArcPhase, majorArcPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem majorArcPhase_neg_eq_conj (x : Real) :
    majorArcPhase (-x) = conj (majorArcPhase x) := by
  rw [majorArcPhase, majorArcPhase, ← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

@[simp]
theorem norm_majorArcPhase_eq_one (x : Real) :
    ‖majorArcPhase x‖ = 1 := by
  rw [majorArcPhase]
  exact Complex.norm_exp_ofReal_mul_I _

theorem majorArcPhase_nat_mul (x : Real) (n : Nat) :
    majorArcPhase ((n : Real) * x) = majorArcPhase x ^ n := by
  rw [majorArcPhase, majorArcPhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The source kernel `min(L, ||theta||^-1)`, with the mathematically intended
value `L` when the nearest-integer distance is zero. -/
noncomputable def cappedNearestIntegerKernel (L theta : Real) : Real :=
  L / max 1 (L * nearestIntegerDistance theta)

theorem cappedNearestIntegerKernel_nonneg
    {L : Real} (hL : 0 <= L) (theta : Real) :
    0 <= cappedNearestIntegerKernel L theta := by
  exact div_nonneg hL (by positivity [cappedNearestIntegerKernel])

theorem cappedNearestIntegerKernel_le
    {L : Real} (hL : 0 <= L) (theta : Real) :
    cappedNearestIntegerKernel L theta <= L := by
  rw [cappedNearestIntegerKernel]
  exact div_le_self hL (le_max_left _ _)

/-- Away from an integral phase, the capped kernel is at most the reciprocal
nearest-integer distance. -/
theorem cappedNearestIntegerKernel_le_inv
    {L theta : Real} (hL : 0 < L)
    (hdist : 0 < nearestIntegerDistance theta) :
    cappedNearestIntegerKernel L theta <=
      (nearestIntegerDistance theta)⁻¹ := by
  rw [cappedNearestIntegerKernel]
  calc
    L / max 1 (L * nearestIntegerDistance theta) <=
        L / (L * nearestIntegerDistance theta) := by
      exact div_le_div_of_nonneg_left hL.le (mul_pos hL hdist)
        (le_max_right _ _)
    _ = (nearestIntegerDistance theta)⁻¹ := by
      field_simp

theorem cappedNearestIntegerKernel_eq_cap
    {L theta : Real}
    (hsmall : L * nearestIntegerDistance theta <= 1) :
    cappedNearestIntegerKernel L theta = L := by
  rw [cappedNearestIntegerKernel, max_eq_left hsmall]
  simp

@[simp]
theorem cappedNearestIntegerKernel_of_distance_zero
    (L theta : Real) (hzero : nearestIntegerDistance theta = 0) :
    cappedNearestIntegerKernel L theta = L := by
  apply cappedNearestIntegerKernel_eq_cap
  rw [hzero, mul_zero]
  norm_num

theorem cappedNearestIntegerKernel_eq_inv
    {L theta : Real} (hL : 0 < L)
    (hlarge : 1 <= L * nearestIntegerDistance theta) :
    cappedNearestIntegerKernel L theta =
      (nearestIntegerDistance theta)⁻¹ := by
  have hdist : nearestIntegerDistance theta ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hlarge
    norm_num at hlarge
  rw [cappedNearestIntegerKernel, max_eq_right hlarge]
  field_simp

@[simp]
theorem cappedNearestIntegerKernel_neg (L theta : Real) :
    cappedNearestIntegerKernel L (-theta) =
      cappedNearestIntegerKernel L theta := by
  simp [cappedNearestIntegerKernel, nearestIntegerDistance_neg]

end PrimesRestrictedDigits
