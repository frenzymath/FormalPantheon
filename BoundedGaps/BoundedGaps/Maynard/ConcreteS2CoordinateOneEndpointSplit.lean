import BoundedGaps.Maynard.ConcreteS2CoordinateOneSquareBridge
import BoundedGaps.Maynard.MaynardS2CoordinateOneGoodFiberSum

noncomputable section

/-!
# Concrete S2 coordinate-one endpoint split

The full concrete coordinate-one fiber-square diagonal is partitioned into
the Abel-valid endpoint region and its exact short-endpoint complement.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def engelsmaS2CoordinateFiberCoordinateOneSupport
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    Finset (BoundedGaps.engelsmaTuple → ℕ) :=
  (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple R
      (primorial D)).filter fun r => r m = 1

def engelsmaS2CoordinateFiberShortSupport
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    Finset (BoundedGaps.engelsmaTuple → ℕ) :=
  (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple R
      (primorial D)).filter fun r =>
    r m = 1 ∧
      ¬1 < maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)

noncomputable def engelsmaS2CoordinateFiberCoordinateOneSquareDiagonal
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ engelsmaS2CoordinateFiberCoordinateOneSupport R D m,
    maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R (primorial D)
        (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
          engelsmaSmallKCandidate) m r ^ 2 /
      ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)

noncomputable def engelsmaS2CoordinateFiberShortSquareDiagonal
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ engelsmaS2CoordinateFiberShortSupport R D m,
    maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R (primorial D)
        (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
          engelsmaSmallKCandidate) m r ^ 2 /
      ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)

theorem engelsmaS2CoordinateFiberCoordinateOneSquareDiagonal_eq_good_add_short
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    engelsmaS2CoordinateFiberCoordinateOneSquareDiagonal R D m =
      engelsmaS2CoordinateFiberGoodSquareDiagonal R D m +
        engelsmaS2CoordinateFiberShortSquareDiagonal R D m := by
  classical
  let S := maynardDivisorTupleSupport BoundedGaps.engelsmaTuple R
    (primorial D)
  let A := S.filter fun r => r m = 1
  let P := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)
  let f := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R (primorial D)
        (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
          engelsmaSmallKCandidate) m r ^ 2 /
      ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)
  have hall : engelsmaS2CoordinateFiberCoordinateOneSupport R D m = A := by
    rfl
  have hgood : engelsmaS2CoordinateFiberGoodSupport R D m =
      A.filter P := by
    ext r
    simp [engelsmaS2CoordinateFiberGoodSupport, A, S, P]
    exact and_assoc.symm
  have hshort : engelsmaS2CoordinateFiberShortSupport R D m =
      A.filter fun r => ¬P r := by
    ext r
    simp [engelsmaS2CoordinateFiberShortSupport, A, S, P]
    exact and_assoc.symm
  unfold engelsmaS2CoordinateFiberCoordinateOneSquareDiagonal
    engelsmaS2CoordinateFiberGoodSquareDiagonal
    engelsmaS2CoordinateFiberShortSquareDiagonal
  rw [hall, hgood, hshort]
  exact (Finset.sum_filter_add_sum_filter_not A P f).symm

set_option maxRecDepth 4000 in
theorem engelsmaMaynardS2CoordinateOneFiberSquareDiagonal_eq_good_add_short
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) :
    engelsmaMaynardS2CoordinateOneFiberSquareDiagonal alpha N m =
      engelsmaS2CoordinateFiberGoodSquareDiagonal
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m +
        engelsmaS2CoordinateFiberShortSquareDiagonal
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m := by
  rw [← engelsmaS2CoordinateFiberCoordinateOneSquareDiagonal_eq_good_add_short]
  rfl

set_option maxRecDepth 4000 in
theorem abs_engelsmaMaynardS2CoordinateOneFiberSquareDiagonal_sub_goodOuterMoment_add_short_le
    {alpha : ℝ} {N : ℕ} (m : BoundedGaps.engelsmaTuple)
    (hR : 1 < engelsmaMaynardRadius alpha N) :
    |engelsmaMaynardS2CoordinateOneFiberSquareDiagonal alpha N m -
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
            engelsmaS2CoordinateFiberGoodOuterMoment
              (engelsmaMaynardRadius alpha N)
              (tripleLogCutoff (N - 1)) m +
          engelsmaS2CoordinateFiberShortSquareDiagonal
              (engelsmaMaynardRadius alpha N)
              (tripleLogCutoff (N - 1)) m)| ≤
      engelsmaS2CoordinateFiberGoodSquareError
        (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m := by
  rw [engelsmaMaynardS2CoordinateOneFiberSquareDiagonal_eq_good_add_short]
  have hgood :=
    abs_engelsmaS2CoordinateFiberGoodSquareDiagonal_sub_outerMoment_le
      (R := engelsmaMaynardRadius alpha N)
      (D := tripleLogCutoff (N - 1)) m hR
  simpa only [add_sub_add_right_eq_sub] using hgood

end BoundedGaps.Maynard
