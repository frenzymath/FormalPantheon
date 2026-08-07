import BoundedGaps.Maynard.ConcreteS1CrossBound
import BoundedGaps.Maynard.ConcreteS2CoordinateOneEndpointSplit

noncomputable section

/-!
# S2 coordinate-fiber short endpoint

On the exact short-endpoint support, the scalar fiber endpoint is one and the
fiber sum collapses to its `u = 1` term. This exposes the remaining tail as a
direct supported Y-diagonal with a reciprocal `g` mass bound.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem maynardS2CoordinateFiberEndpoint_eq_one_of_short
    {H : Finset ℕ} {R W : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R W r) (hrm : r m = 1)
    (hshort : ¬1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct H m r)) :
    maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct H m r) = 1 := by
  let P := maynardS2OffCoordinateProduct H m r
  have hP : 0 < P := maynardS2OffCoordinateProduct_pos m r hr
  have hPR : P < R := by
    dsimp [P]
    rw [← divisorTupleProduct_eq_offCoordinateProduct m hrm]
    exact hr.1
  have hOne : 1 ≤ maynardS2CoordinateFiberEndpoint R P := by
    unfold maynardS2CoordinateFiberEndpoint
    rw [Nat.le_div_iff_mul_le hP]
    omega
  simpa [P] using Nat.le_antisymm (Nat.le_of_not_gt hshort) hOne

theorem maynardS2CoordinateFiberSupport_eq_singleton_of_short
    {H : Finset ℕ} {R W : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R W r) (hrm : r m = 1)
    (hshort : ¬1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct H m r)) :
    maynardS2CoordinateFiberSupport H R W m r = {1} := by
  have hR : 0 < R :=
    (maynardS2OffCoordinateProduct_pos m r hr).trans
      (maynardS2OffCoordinateProduct_lt m r hr)
  rw [maynardS2CoordinateFiberSupport_eq_endpointFilter m hr hR,
    maynardS2CoordinateFiberEndpoint_eq_one_of_short m r hr hrm hshort]
  simp

theorem maynardS2CoordinateFiberSum_eq_self_of_short
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R W r) (hrm : r m = 1)
    (hshort : ¬1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct H m r)) :
    maynardS2CoordinateFiberSum H R W y m r = y r := by
  rw [maynardS2CoordinateFiberSum_eq_scalarSum m hr hrm,
    maynardS2CoordinateFiberSupport_eq_singleton_of_short m r hr hrm hshort]
  have hupd : Function.update r m 1 = r := by
    rw [← hrm]
    exact Function.update_eq_self m r
  simp [hupd]

noncomputable def engelsmaS2CoordinateFiberShortYDiagonal
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ engelsmaS2CoordinateFiberShortSupport R D m,
    maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
        engelsmaSmallKCandidate r ^ 2 /
      ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)

noncomputable def engelsmaS2CoordinateFiberShortReciprocalGMass
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ engelsmaS2CoordinateFiberShortSupport R D m,
    1 / |∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)|

set_option maxRecDepth 3000 in
theorem engelsmaS2CoordinateFiberShortSquareDiagonal_eq_yDiagonal
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    engelsmaS2CoordinateFiberShortSquareDiagonal R D m =
      engelsmaS2CoordinateFiberShortYDiagonal R D m := by
  unfold engelsmaS2CoordinateFiberShortSquareDiagonal
    engelsmaS2CoordinateFiberShortYDiagonal
  apply Finset.sum_congr rfl
  intro r hrMem
  have hrData := Finset.mem_filter.mp hrMem
  rw [maynardS2CoordinateFiberSum_eq_self_of_short m r
    (isMaynardDivisorTuple_of_mem_support hrData.1)
    hrData.2.1 hrData.2.2]

set_option maxRecDepth 3000 in
theorem abs_engelsmaS2CoordinateFiberShortSquareDiagonal_le_reciprocalGMass
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    |engelsmaS2CoordinateFiberShortSquareDiagonal R D m| ≤
      smallKCandidateBound ^ 2 *
        engelsmaS2CoordinateFiberShortReciprocalGMass R D m := by
  rw [engelsmaS2CoordinateFiberShortSquareDiagonal_eq_yDiagonal]
  unfold engelsmaS2CoordinateFiberShortYDiagonal
    engelsmaS2CoordinateFiberShortReciprocalGMass
  calc
    |∑ r ∈ engelsmaS2CoordinateFiberShortSupport R D m,
        maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
            engelsmaSmallKCandidate r ^ 2 /
          ∏ h : BoundedGaps.engelsmaTuple,
            (maynardS2G (r h) : ℝ)| ≤
      ∑ r ∈ engelsmaS2CoordinateFiberShortSupport R D m,
        |maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
            engelsmaSmallKCandidate r ^ 2 /
          ∏ h : BoundedGaps.engelsmaTuple,
            (maynardS2G (r h) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ engelsmaS2CoordinateFiberShortSupport R D m,
        smallKCandidateBound ^ 2 /
          |∏ h : BoundedGaps.engelsmaTuple,
            (maynardS2G (r h) : ℝ)| := by
      apply Finset.sum_le_sum
      intro r hrMem
      have hy := abs_maynardYValue_le BoundedGaps.engelsmaTuple R
        (primorial D) engelsmaSmallKCandidate smallKCandidateBound_nonneg
        engelsmaSmallKCandidate_abs_le r
      rw [abs_div, abs_pow]
      apply div_le_div_of_nonneg_right
      · exact pow_le_pow_left₀ (abs_nonneg _) hy 2
      · exact abs_nonneg _
    _ = smallKCandidateBound ^ 2 *
        ∑ r ∈ engelsmaS2CoordinateFiberShortSupport R D m,
          1 / |∏ h : BoundedGaps.engelsmaTuple,
            (maynardS2G (r h) : ℝ)| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hrMem
      ring

set_option maxRecDepth 4000 in
theorem abs_engelsmaMaynardS2CoordinateOneFiberSquareDiagonal_sub_goodOuterMoment_le
    {alpha : ℝ} {N : ℕ} (m : BoundedGaps.engelsmaTuple)
    (hR : 1 < engelsmaMaynardRadius alpha N) :
    |engelsmaMaynardS2CoordinateOneFiberSquareDiagonal alpha N m -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
          engelsmaS2CoordinateFiberGoodOuterMoment
            (engelsmaMaynardRadius alpha N)
            (tripleLogCutoff (N - 1)) m| ≤
      engelsmaS2CoordinateFiberGoodSquareError
          (engelsmaMaynardRadius alpha N)
          (tripleLogCutoff (N - 1)) m +
        smallKCandidateBound ^ 2 *
          engelsmaS2CoordinateFiberShortReciprocalGMass
            (engelsmaMaynardRadius alpha N)
            (tripleLogCutoff (N - 1)) m := by
  let R := engelsmaMaynardRadius alpha N
  let D := tripleLogCutoff (N - 1)
  let F := engelsmaMaynardS2CoordinateOneFiberSquareDiagonal alpha N m
  let O := preSieveSingularSeries D ^ 2 *
    engelsmaS2CoordinateFiberGoodOuterMoment R D m
  let T := engelsmaS2CoordinateFiberShortSquareDiagonal R D m
  let E := engelsmaS2CoordinateFiberGoodSquareError R D m
  have hmain : |F - (O + T)| ≤ E := by
    simpa [F, O, T, E, R, D] using
      (abs_engelsmaMaynardS2CoordinateOneFiberSquareDiagonal_sub_goodOuterMoment_add_short_le
        m hR)
  have htail : |T| ≤ smallKCandidateBound ^ 2 *
      engelsmaS2CoordinateFiberShortReciprocalGMass R D m := by
    simpa [T] using
      (abs_engelsmaS2CoordinateFiberShortSquareDiagonal_le_reciprocalGMass
        R D m)
  calc
    |F - O| = |(F - (O + T)) + T| := by congr 1; ring
    _ ≤ |F - (O + T)| + |T| := abs_add_le _ _
    _ ≤ E + smallKCandidateBound ^ 2 *
        engelsmaS2CoordinateFiberShortReciprocalGMass R D m :=
      add_le_add hmain htail

end BoundedGaps.Maynard
