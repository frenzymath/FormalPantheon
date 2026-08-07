import BoundedGaps.Maynard.MaynardS2CoordinateFiberIntegralSquare

noncomputable section

/-!
# S2 coordinate-one good-endpoint fiber sum

The pointwise coordinate-fiber square estimate is summed over exactly those
coordinate-one tuples whose scalar fiber endpoint exceeds one. The integral
main sum is then rewritten as the squarefree outer face moment.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped BigOperators

def engelsmaS2CoordinateFiberGoodSupport
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    Finset (BoundedGaps.engelsmaTuple → ℕ) :=
  (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple R
      (primorial D)).filter fun r =>
    r m = 1 ∧
      1 < maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)

noncomputable def engelsmaS2CoordinateFiberGoodSquareDiagonal
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ engelsmaS2CoordinateFiberGoodSupport R D m,
    maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R (primorial D)
        (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
          engelsmaSmallKCandidate) m r ^ 2 /
      ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)

noncomputable def engelsmaS2CoordinateFiberGoodIntegralDiagonal
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ engelsmaS2CoordinateFiberGoodSupport R D m,
    engelsmaS2CoordinateFiberIntegralMain R D m r ^ 2 /
      ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)

noncomputable def engelsmaS2CoordinateFiberGoodOuterMoment
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ engelsmaS2CoordinateFiberGoodSupport R D m,
    maynardS2OuterSquarefreeAF (primorial D)
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) *
      ((Real.log R) *
        (∫ x in (0 : ℝ)..(
          Real.log (maynardS2CoordinateFiberEndpoint R
            (maynardS2OffCoordinateProduct
              BoundedGaps.engelsmaTuple m r)) / Real.log R),
          engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2

noncomputable def engelsmaS2CoordinateFiberGoodSquareError
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ engelsmaS2CoordinateFiberGoodSupport R D m,
    (engelsmaS2CoordinateFiberAbelErrorEnvelope R D m r *
      (2 * |engelsmaS2CoordinateFiberIntegralMain R D m r| +
        engelsmaS2CoordinateFiberAbelErrorEnvelope R D m r)) /
      |∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)|

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem abs_engelsmaS2CoordinateFiberGoodSquareDiagonal_sub_integral_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple) (hR : 1 < R) :
    |engelsmaS2CoordinateFiberGoodSquareDiagonal R D m -
        engelsmaS2CoordinateFiberGoodIntegralDiagonal R D m| ≤
      engelsmaS2CoordinateFiberGoodSquareError R D m := by
  rw [engelsmaS2CoordinateFiberGoodSquareDiagonal,
    engelsmaS2CoordinateFiberGoodIntegralDiagonal,
    engelsmaS2CoordinateFiberGoodSquareError, ← Finset.sum_sub_distrib]
  calc
    |∑ r ∈ engelsmaS2CoordinateFiberGoodSupport R D m,
        (maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R
            (primorial D)
            (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
              engelsmaSmallKCandidate) m r ^ 2 /
              ∏ h : BoundedGaps.engelsmaTuple,
                (maynardS2G (r h) : ℝ) -
          engelsmaS2CoordinateFiberIntegralMain R D m r ^ 2 /
              ∏ h : BoundedGaps.engelsmaTuple,
                (maynardS2G (r h) : ℝ))| ≤
        ∑ r ∈ engelsmaS2CoordinateFiberGoodSupport R D m,
          |maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R
              (primorial D)
              (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
                engelsmaSmallKCandidate) m r ^ 2 /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ) -
            engelsmaS2CoordinateFiberIntegralMain R D m r ^ 2 /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hrMem
      have hrData := Finset.mem_filter.mp hrMem
      have hr := isMaynardDivisorTuple_of_mem_support hrData.1
      have hpoint :=
        abs_maynardS2CoordinateFiberSum_sq_sub_integralMain_sq_le
          m hr hrData.2.1 hrData.2.2 hR
      have hterm :
          |maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R
                (primorial D)
                (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
                  engelsmaSmallKCandidate) m r ^ 2 /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ) -
            engelsmaS2CoordinateFiberIntegralMain R D m r ^ 2 /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ)| =
            |maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R
                  (primorial D)
                  (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
                    engelsmaSmallKCandidate) m r ^ 2 -
                engelsmaS2CoordinateFiberIntegralMain R D m r ^ 2| /
              |∏ h : BoundedGaps.engelsmaTuple,
                (maynardS2G (r h) : ℝ)| := by
        rw [show
          maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R
                (primorial D)
                (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
                  engelsmaSmallKCandidate) m r ^ 2 /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ) -
            engelsmaS2CoordinateFiberIntegralMain R D m r ^ 2 /
                ∏ h : BoundedGaps.engelsmaTuple,
                  (maynardS2G (r h) : ℝ) =
            (maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R
                  (primorial D)
                  (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
                    engelsmaSmallKCandidate) m r ^ 2 -
                engelsmaS2CoordinateFiberIntegralMain R D m r ^ 2) /
              ∏ h : BoundedGaps.engelsmaTuple,
                (maynardS2G (r h) : ℝ) by ring]
        exact abs_div _ _
      rw [hterm]
      exact div_le_div_of_nonneg_right hpoint (abs_nonneg _)

set_option maxRecDepth 4000 in
theorem engelsmaS2CoordinateFiberGoodIntegralDiagonal_eq_outerMoment
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    engelsmaS2CoordinateFiberGoodIntegralDiagonal R D m =
      preSieveSingularSeries D ^ 2 *
        engelsmaS2CoordinateFiberGoodOuterMoment R D m := by
  rw [engelsmaS2CoordinateFiberGoodIntegralDiagonal,
    engelsmaS2CoordinateFiberGoodOuterMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hrMem
  have hrData := Finset.mem_filter.mp hrMem
  simpa [mul_assoc] using
    (engelsmaS2CoordinateFiberIntegralMain_sq_div_gProduct_eq_outerSquarefree
      m r (isMaynardDivisorTuple_of_mem_support hrData.1) hrData.2.1)

set_option maxRecDepth 4000 in
theorem abs_engelsmaS2CoordinateFiberGoodSquareDiagonal_sub_outerMoment_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple) (hR : 1 < R) :
    |engelsmaS2CoordinateFiberGoodSquareDiagonal R D m -
        preSieveSingularSeries D ^ 2 *
          engelsmaS2CoordinateFiberGoodOuterMoment R D m| ≤
      engelsmaS2CoordinateFiberGoodSquareError R D m := by
  rw [← engelsmaS2CoordinateFiberGoodIntegralDiagonal_eq_outerMoment]
  exact abs_engelsmaS2CoordinateFiberGoodSquareDiagonal_sub_integral_le m hR

end BoundedGaps.Maynard
