import BoundedGaps.Maynard.MaynardS2RestrictedYDiagonal

noncomputable section

/-!
# Distinguished-coordinate support of the S2 Y-transform

The restricted transform vanishes off the arithmetic face `u_m = 1`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance s2YFaceDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem maynardS2RestrictedY_eq_zero_of_coordinate_ne_one
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {m : H} {u : H → ℕ}
    (hum : u m ≠ 1) :
    maynardS2RestrictedYFromCoefficients H D lambda m u = 0 := by
  classical
  unfold maynardS2RestrictedYFromCoefficients
  rw [Finset.sum_eq_zero]
  · exact mul_zero _
  · intro d hd
    rw [if_neg]
    intro hcond
    apply hum
    have hdvd : u m ∣ 1 := by
      simpa [hcond.2] using hcond.1 m
    exact Nat.dvd_one.mp hdvd

noncomputable def maynardS2RestrictedYCoordinateOneDiagonalSum
    (H : Finset ℕ) (R W : ℕ)
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ u ∈ (maynardDivisorTupleSupport H R W).filter (fun u => u m = 1),
    maynardS2RestrictedYFromCoefficients H
        (maynardDivisorTupleSupport H R W) lambda m u ^ 2 /
      ∏ h : H, (maynardS2G (u h) : ℝ)

theorem maynardS2RestrictedYDiagonalSum_eq_coordinateOne
    (H : Finset ℕ) (R W : ℕ)
    (lambda : (H → ℕ) → ℝ) (m : H) :
    maynardS2RestrictedYDiagonalSum H R W lambda m =
      maynardS2RestrictedYCoordinateOneDiagonalSum H R W lambda m := by
  classical
  unfold maynardS2RestrictedYDiagonalSum
    maynardS2RestrictedYCoordinateOneDiagonalSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hum : u m = 1
  · rw [if_pos hum]
  · rw [if_neg hum,
      maynardS2RestrictedY_eq_zero_of_coordinate_ne_one hum]
    simp

end BoundedGaps.Maynard
