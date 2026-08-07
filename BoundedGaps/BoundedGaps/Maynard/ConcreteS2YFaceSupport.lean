import BoundedGaps.Maynard.ConcreteS2RestrictedYDiagonal
import BoundedGaps.Maynard.MaynardS2YFaceSupport

noncomputable section

/-!
# Concrete distinguished-coordinate S2 face support
-/

namespace BoundedGaps.Maynard

noncomputable def engelsmaMaynardS2CoordinateOneYDiagonal
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) : ℝ :=
  maynardS2RestrictedYCoordinateOneDiagonalSum
    BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
    (engelsmaMaynardModulus N)
    (maynardCoefficientFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
      engelsmaSmallKCandidate N) h

set_option maxRecDepth 3000 in
theorem engelsmaMaynardS2CoordinateOneYDiagonal_eq_fromYValue
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) :
    engelsmaMaynardS2CoordinateOneYDiagonal alpha N h =
      maynardS2RestrictedYCoordinateOneDiagonalSum
        BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N)
          (maynardCoefficientFromY BoundedGaps.engelsmaTuple
            (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
            (maynardYValue BoundedGaps.engelsmaTuple
              (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
              engelsmaSmallKCandidate)) h := by
  unfold engelsmaMaynardS2CoordinateOneYDiagonal
  congr 1
  funext d
  exact maynardCoefficient_eq_fromYValue _ _ _ _ d

set_option maxRecDepth 3000 in
theorem engelsmaMaynardS2RestrictedYDiagonal_eq_coordinateOne
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) :
    engelsmaMaynardS2RestrictedYDiagonal alpha N h =
      engelsmaMaynardS2CoordinateOneYDiagonal alpha N h := by
  unfold engelsmaMaynardS2RestrictedYDiagonal
    engelsmaMaynardS2CoordinateOneYDiagonal
  exact maynardS2RestrictedYDiagonalSum_eq_coordinateOne
    BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) _ h

theorem engelsmaMaynardS2Main_eq_invTotient_mul_coordinateOne_sub_cross_sum
    (alpha : ℝ) (N : ℕ) :
    engelsmaMaynardS2Main alpha N =
      ∑ h ∈ BoundedGaps.engelsmaTuple.attach,
        engelsmaShiftedPrimeIntervalCount N h *
          ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
            (engelsmaMaynardS2CoordinateOneYDiagonal alpha N h -
              engelsmaMaynardS2RestrictedCrossCorrection alpha N h)) := by
  rw [engelsmaMaynardS2Main_eq_invTotient_mul_yDiagonal_sub_cross_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [engelsmaMaynardS2RestrictedYDiagonal_eq_coordinateOne]

end BoundedGaps.Maynard
