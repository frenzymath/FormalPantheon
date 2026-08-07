import BoundedGaps.Maynard.ConcreteS2YFaceSupport
import BoundedGaps.Maynard.MaynardS2RestrictedYComparison

noncomputable section

/-!
# Concrete S2 coordinate-one square bridge

The pointwise restricted-Y square perturbation is summed over the exact
coordinate-one support. The reciprocal `g` denominator is retained as an
absolute weight, so no nonvanishing or positivity assumption is hidden.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable def maynardS2CoordinateOneSquarePerturbationEnvelope
    (H : Finset ℕ) (R D : ℕ) (m : H) (B : ℝ) : ℝ :=
  2 * (B * preSievedCoordinateInvTotientMass (primorial D) R +
    B * ((Finset.univ.erase m).card : ℝ) *
      (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
        (1 + Real.log R)) *
      (8 / (D : ℝ) +
        (8 * Real.exp 8 / (D : ℝ)) *
          (1 + 8 * Real.exp 8 / (D : ℝ)) ^
            ((Finset.univ.erase m).card - 1))) *
    (B * ((Finset.univ.erase m).card : ℝ) *
      (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
        (1 + Real.log R)) *
      (8 / (D : ℝ) +
        (8 * Real.exp 8 / (D : ℝ)) *
          (1 + 8 * Real.exp 8 / (D : ℝ)) ^
            ((Finset.univ.erase m).card - 1)))

noncomputable def engelsmaMaynardS2CoordinateOneFiberSquareDiagonal
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)).filter
      (fun r => r m = 1),
    (maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
      (maynardYValue BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
        engelsmaSmallKCandidate) m r) ^ 2 /
      ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem abs_engelsmaMaynardS2CoordinateOneYDiagonal_sub_fiberSquareDiagonal_le_log
    {alpha : ℝ} (N : ℕ) (m : BoundedGaps.engelsmaTuple)
    (hD : 0 < tripleLogCutoff (N - 1))
    (hWL : (engelsmaMaynardModulus N : ℝ) ≤
      1 + Real.log (engelsmaMaynardRadius alpha N)) :
    |engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
        engelsmaMaynardS2CoordinateOneFiberSquareDiagonal alpha N m| ≤
      ∑ r ∈ (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)).filter
          (fun r => r m = 1),
        maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N)
          (tripleLogCutoff (N - 1)) m smallKCandidateBound /
          |∏ h : BoundedGaps.engelsmaTuple,
            (maynardS2G (r h) : ℝ)| := by
  let R := engelsmaMaynardRadius alpha N
  let D := tripleLogCutoff (N - 1)
  let W := primorial D
  let S := (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple R W).filter
    (fun r => r m = 1)
  let y := maynardYValue BoundedGaps.engelsmaTuple R W
    engelsmaSmallKCandidate
  let Y : (BoundedGaps.engelsmaTuple → ℕ) → ℝ := fun r =>
    maynardS2RestrictedYFromCoefficients BoundedGaps.engelsmaTuple
      (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple R W)
      (maynardCoefficientFromY BoundedGaps.engelsmaTuple R W y) m r
  let F : (BoundedGaps.engelsmaTuple → ℕ) → ℝ := fun r =>
    maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R W y m r
  have hy : IsSupportedMaynardY BoundedGaps.engelsmaTuple R W y := by
    exact isSupportedMaynardY_maynardYValue _ _ _ _
  have hyBound : ∀ r, |y r| ≤ smallKCandidateBound := by
    intro r
    exact abs_engelsmaMaynardYValue_le alpha N r
  have hD' : 0 < D := by simpa [D] using hD
  have hWL' : (W : ℝ) ≤ 1 + Real.log R := by
    simpa [W, R, D, engelsmaMaynardModulus] using hWL
  have hsum :
      |(∑ r ∈ S, ((Y r) ^ 2 /
          ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ))) -
        (∑ r ∈ S, ((F r) ^ 2 /
          ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)))| ≤
      ∑ r ∈ S,
        maynardS2CoordinateOneSquarePerturbationEnvelope
          BoundedGaps.engelsmaTuple R D m smallKCandidateBound /
          |∏ h : BoundedGaps.engelsmaTuple,
            (maynardS2G (r h) : ℝ)| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ r ∈ S,
          ((Y r) ^ 2 /
              ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ) -
            (F r) ^ 2 /
              ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ))| ≤
          ∑ r ∈ S, |((Y r) ^ 2 /
              ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ) -
            (F r) ^ 2 /
              ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ S,
          maynardS2CoordinateOneSquarePerturbationEnvelope
            BoundedGaps.engelsmaTuple R D m smallKCandidateBound /
            |∏ h : BoundedGaps.engelsmaTuple,
              (maynardS2G (r h) : ℝ)| := by
        apply Finset.sum_le_sum
        intro r hr
        have hrData := Finset.mem_filter.mp hr
        have hrSupport := hrData.1
        have hrMaynard := isMaynardDivisorTuple_of_mem_support hrSupport
        have hpoint :=
          abs_maynardS2RestrictedY_sq_sub_coordinateFiber_sq_le_log
            hy m hD' hWL' hrMaynard hrData.2
              (B := smallKCandidateBound)
              smallKCandidateBound_nonneg hyBound
        have hterm :
            |(Y r) ^ 2 /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ) -
              (F r) ^ 2 /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ)| =
              |Y r ^ 2 - F r ^ 2| /
                |∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ)| := by
          rw [show (Y r) ^ 2 /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ) -
              (F r) ^ 2 /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ) =
              ((Y r) ^ 2 - (F r) ^ 2) /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ) by ring]
          exact abs_div _ _
        rw [hterm]
        apply div_le_div_of_nonneg_right
        · simpa [Y, F, maynardS2CoordinateOneSquarePerturbationEnvelope]
            using hpoint
        · exact abs_nonneg _
  rw [engelsmaMaynardS2CoordinateOneYDiagonal_eq_fromYValue]
  simpa [engelsmaMaynardS2CoordinateOneYDiagonal,
    maynardS2RestrictedYCoordinateOneDiagonalSum, engelsmaMaynardModulus,
    R, D, W, S, Y, F,
    engelsmaMaynardS2CoordinateOneFiberSquareDiagonal, y,
    maynardS2CoordinateOneSquarePerturbationEnvelope] using hsum

end BoundedGaps.Maynard
