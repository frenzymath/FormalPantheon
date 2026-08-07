import BoundedGaps.Maynard.ConcreteS2RestrictedYSquarePerturbation
import BoundedGaps.Maynard.MaynardS2CoordinateFiberShortEndpoint

noncomputable section

/-!
# Concrete S2 coordinate-one main composition

The exact restricted coordinate-one kernel is compared with the good outer
moment. The four remaining residuals stay separate: restricted-Y square
perturbation, summed Abel error, short endpoint, and incompatible cross term.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable def engelsmaS2CoordinateOneMainResidualEnvelope
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  (∑ r ∈ (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N)).filter (fun r => r m = 1),
    maynardS2CoordinateOneSquarePerturbationEnvelope
      BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
      (tripleLogCutoff (N - 1)) m smallKCandidateBound /
      |∏ h : BoundedGaps.engelsmaTuple,
        (maynardS2G (r h) : ℝ)|) +
    engelsmaS2CoordinateFiberGoodSquareError
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m +
    smallKCandidateBound ^ 2 *
      engelsmaS2CoordinateFiberShortReciprocalGMass
        (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m +
    |engelsmaMaynardS2RestrictedCrossCorrection alpha N m|

noncomputable def engelsmaMaynardS2GoodOuterMain
    (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
    engelsmaShiftedPrimeIntervalCount N m *
      ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
          engelsmaS2CoordinateFiberGoodOuterMoment
            (engelsmaMaynardRadius alpha N)
            (tripleLogCutoff (N - 1)) m))

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1200000 in
theorem abs_engelsmaMaynardS2CoordinateOneKernel_sub_goodOuter_le
    {alpha : ℝ} (N : ℕ) (m : BoundedGaps.engelsmaTuple)
    (hR : 1 < engelsmaMaynardRadius alpha N)
    (hD : 0 < tripleLogCutoff (N - 1))
    (hWL : (engelsmaMaynardModulus N : ℝ) ≤
      1 + Real.log (engelsmaMaynardRadius alpha N)) :
    |(engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
        engelsmaMaynardS2RestrictedCrossCorrection alpha N m) -
      preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
        engelsmaS2CoordinateFiberGoodOuterMoment
          (engelsmaMaynardRadius alpha N)
          (tripleLogCutoff (N - 1)) m| ≤
      engelsmaS2CoordinateOneMainResidualEnvelope alpha N m := by
  let Y := engelsmaMaynardS2CoordinateOneYDiagonal alpha N m
  let F := engelsmaMaynardS2CoordinateOneFiberSquareDiagonal alpha N m
  let C := engelsmaMaynardS2RestrictedCrossCorrection alpha N m
  let O := preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
    engelsmaS2CoordinateFiberGoodOuterMoment
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m
  let P := ∑ r ∈ (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N)).filter (fun r => r m = 1),
    maynardS2CoordinateOneSquarePerturbationEnvelope
      BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
      (tripleLogCutoff (N - 1)) m smallKCandidateBound /
      |∏ h : BoundedGaps.engelsmaTuple,
        (maynardS2G (r h) : ℝ)|
  let E := engelsmaS2CoordinateFiberGoodSquareError
    (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m
  let T := smallKCandidateBound ^ 2 *
    engelsmaS2CoordinateFiberShortReciprocalGMass
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m
  have hYF : |Y - F| ≤ P := by
    simpa [Y, F, P] using
      abs_engelsmaMaynardS2CoordinateOneYDiagonal_sub_fiberSquareDiagonal_le_log
        N m hD hWL
  have hFO : |F - O| ≤ E + T := by
    simpa [F, O, E, T] using
      abs_engelsmaMaynardS2CoordinateOneFiberSquareDiagonal_sub_goodOuterMoment_le
        m hR
  calc
    |(Y - C) - O| = |(Y - F) + (F - O) - C| := by
      congr 1
      ring
    _ ≤ |Y - F| + |F - O| + |C| := by
      calc
        |(Y - F) + (F - O) - C| =
            |(Y - F) + (F - O) + (-C)| := by ring_nf
        _ ≤ |(Y - F) + (F - O)| + |-C| := abs_add_le _ _
        _ = |(Y - F) + (F - O)| + |C| := by rw [abs_neg]
        _ ≤ (|Y - F| + |F - O|) + |C| :=
          add_le_add (abs_add_le _ _) le_rfl
    _ ≤ P + (E + T) + |C| :=
      add_le_add (add_le_add hYF hFO) le_rfl
    _ = engelsmaS2CoordinateOneMainResidualEnvelope alpha N m := by
      simp only [engelsmaS2CoordinateOneMainResidualEnvelope]
      dsimp [P, E, T, C]
      ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem abs_engelsmaMaynardS2Main_sub_goodOuterMain_le
    {alpha : ℝ} (N : ℕ)
    (hR : 1 < engelsmaMaynardRadius alpha N)
    (hD : 0 < tripleLogCutoff (N - 1))
    (hWL : (engelsmaMaynardModulus N : ℝ) ≤
      1 + Real.log (engelsmaMaynardRadius alpha N)) :
    |engelsmaMaynardS2Main alpha N -
        engelsmaMaynardS2GoodOuterMain alpha N| ≤
      ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
        |engelsmaShiftedPrimeIntervalCount N m *
          (Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹| *
          engelsmaS2CoordinateOneMainResidualEnvelope alpha N m := by
  rw [engelsmaMaynardS2Main_eq_invTotient_mul_coordinateOne_sub_cross_sum]
  unfold engelsmaMaynardS2GoodOuterMain
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ m ∈ BoundedGaps.engelsmaTuple.attach,
        (engelsmaShiftedPrimeIntervalCount N m *
            ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
              (engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
                engelsmaMaynardS2RestrictedCrossCorrection alpha N m)) -
          engelsmaShiftedPrimeIntervalCount N m *
            ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
              (preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
                engelsmaS2CoordinateFiberGoodOuterMoment
                  (engelsmaMaynardRadius alpha N)
                  (tripleLogCutoff (N - 1)) m)))| ≤
        ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
          |engelsmaShiftedPrimeIntervalCount N m *
              ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
                (engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
                  engelsmaMaynardS2RestrictedCrossCorrection alpha N m)) -
            engelsmaShiftedPrimeIntervalCount N m *
              ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
                (preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
                  engelsmaS2CoordinateFiberGoodOuterMoment
                    (engelsmaMaynardRadius alpha N)
                    (tripleLogCutoff (N - 1)) m))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
        |engelsmaShiftedPrimeIntervalCount N m *
          (Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹| *
          engelsmaS2CoordinateOneMainResidualEnvelope alpha N m := by
      apply Finset.sum_le_sum
      intro m hm
      have hlocal :=
        abs_engelsmaMaynardS2CoordinateOneKernel_sub_goodOuter_le
          N m hR hD hWL
      rw [show
        engelsmaShiftedPrimeIntervalCount N m *
              ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
                (engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
                  engelsmaMaynardS2RestrictedCrossCorrection alpha N m)) -
            engelsmaShiftedPrimeIntervalCount N m *
              ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
                (preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
                  engelsmaS2CoordinateFiberGoodOuterMoment
                    (engelsmaMaynardRadius alpha N)
                    (tripleLogCutoff (N - 1)) m)) =
          (engelsmaShiftedPrimeIntervalCount N m *
              (Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹) *
            ((engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
                engelsmaMaynardS2RestrictedCrossCorrection alpha N m) -
              preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
                engelsmaS2CoordinateFiberGoodOuterMoment
                  (engelsmaMaynardRadius alpha N)
                  (tripleLogCutoff (N - 1)) m) by ring,
        abs_mul]
      exact mul_le_mul_of_nonneg_left hlocal (abs_nonneg _)

end BoundedGaps.Maynard
