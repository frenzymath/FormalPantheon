import BoundedGaps.Maynard.MaynardS1YDiagonal

noncomputable section

/-!
# Compatible S1 main term as diagonal minus cross correction

This module records the exact finite partition. Bounding the correction is a
separate analytic obligation.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def incompatibleDivisorPairCommonDivisorTupleSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ := by
  classical
  exact
    ∑ d ∈ D,
      ∑ e ∈ D.filter (fun e => ¬IsCrossCoordinateCoprime H d e),
        ∑ u ∈ commonDivisorTupleSupport H d e,
          commonDivisorTupleTerm H d e u * (lambda d * lambda e)

theorem unrestrictedCommonDivisorTupleSum_eq_compatible_add_incompatible
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) :
    unrestrictedDivisorPairCommonDivisorTupleSum H D lambda =
      compatibleDivisorPairCommonDivisorTupleSum H D lambda +
        incompatibleDivisorPairCommonDivisorTupleSum H D lambda := by
  classical
  unfold unrestrictedDivisorPairCommonDivisorTupleSum
    compatibleDivisorPairCommonDivisorTupleSum
    incompatibleDivisorPairCommonDivisorTupleSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  exact (Finset.sum_filter_add_sum_filter_not D
    (fun e => IsCrossCoordinateCoprime H d e)
    (fun e => ∑ u ∈ commonDivisorTupleSupport H d e,
      commonDivisorTupleTerm H d e u * (lambda d * lambda e))).symm

theorem compatibleCommonDivisorTupleSum_eq_unrestricted_sub_incompatible
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) :
    compatibleDivisorPairCommonDivisorTupleSum H D lambda =
      unrestrictedDivisorPairCommonDivisorTupleSum H D lambda -
        incompatibleDivisorPairCommonDivisorTupleSum H D lambda := by
  have h := unrestrictedCommonDivisorTupleSum_eq_compatible_add_incompatible
    H D lambda
  linarith

theorem compatibleCommonDivisorTupleSum_eq_yDiagonal_sub_incompatible
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) :
    compatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) =
      maynardYDiagonalSum H R W y -
        incompatibleDivisorPairCommonDivisorTupleSum H
          (maynardDivisorTupleSupport H R W)
          (maynardCoefficientFromY H R W y) := by
  rw [compatibleCommonDivisorTupleSum_eq_unrestricted_sub_incompatible]
  rw [unrestrictedCommonDivisorTupleSum_eq_maynardYDiagonalSum hy]

theorem compatibleCommonDivisorTupleSum_eq_yValueDiagonal_sub_incompatible
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ) :
    compatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R W) (maynardCoefficient H R W F) =
      maynardYDiagonalSum H R W (maynardYValue H R W F) -
        incompatibleDivisorPairCommonDivisorTupleSum H
          (maynardDivisorTupleSupport H R W) (maynardCoefficient H R W F) := by
  have hcoeff : maynardCoefficient H R W F =
      maynardCoefficientFromY H R W (maynardYValue H R W F) := by
    funext d
    exact maynardCoefficient_eq_fromYValue H R W F d
  rw [hcoeff]
  exact compatibleCommonDivisorTupleSum_eq_yDiagonal_sub_incompatible
    (isSupportedMaynardY_maynardYValue H R W F)

theorem compatibleDivisorPairMainSum_eq_yValueDiagonal_sub_incompatible
    (H : Finset ℕ) (R W N : ℕ) (F : (H → ℝ) → ℝ) :
    compatibleDivisorPairMainSum H (maynardDivisorTupleSupport H R W) W N
        (maynardCoefficient H R W F) =
      (N : ℝ) / W *
        (maynardYDiagonalSum H R W (maynardYValue H R W F) -
          incompatibleDivisorPairCommonDivisorTupleSum H
            (maynardDivisorTupleSupport H R W)
            (maynardCoefficient H R W F)) := by
  rw [compatibleDivisorPairMainSum_eq_commonDivisorTupleSum
    (fun d hd => isMaynardDivisorTuple_of_mem_support hd)]
  rw [compatibleCommonDivisorTupleSum_eq_yValueDiagonal_sub_incompatible]

end BoundedGaps.Maynard
