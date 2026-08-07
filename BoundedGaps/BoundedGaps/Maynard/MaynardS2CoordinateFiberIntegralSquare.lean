import BoundedGaps.Maynard.MaynardS2CoordinateFiberOuterWeight
import BoundedGaps.Maynard.MaynardS2CoordinateFiberUniformAbel

noncomputable section

/-!
# S2 coordinate-fiber integral square

The uniform Abel estimate is packaged as a pointwise integral main term and
then lifted to squares. The main square is normalized by the outer
squarefree arithmetic coefficient from the preceding bridge.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped BigOperators

noncomputable def engelsmaS2CoordinateFiberIntegralMain
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) : ℝ :=
  maynardS2CoordinateFiberSingularSeries D m r * Real.log R *
    (∫ x in (0 : ℝ)..(
      Real.log (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
      Real.log R),
      engelsmaS2CoordinateFiberPolynomialTest R m r x)

noncomputable def engelsmaS2CoordinateFiberAbelErrorEnvelope
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) : ℝ :=
  maynardS2CoordinateFiberUniformCumulativeError
      BoundedGaps.engelsmaTuple D
      (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) m r *
    (|engelsmaS2CoordinateFiberPolynomialTest R m r
        (Real.log (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct
            BoundedGaps.engelsmaTuple m r)) / Real.log R)| +
      ∫ t in Set.Ioc (1 : ℝ)
          (maynardS2CoordinateFiberEndpoint R
            (maynardS2OffCoordinateProduct
              BoundedGaps.engelsmaTuple m r)),
        |deriv (fun z =>
          engelsmaS2CoordinateFiberPolynomialTest R m r
            (Real.log z / Real.log R)) t|)

theorem abs_maynardS2CoordinateFiberSum_sub_integralMain_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hrm : r m = 1)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r))
    (hR : 1 < R) :
    |maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R (primorial D)
          (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
            engelsmaSmallKCandidate) m r -
        engelsmaS2CoordinateFiberIntegralMain R D m r| ≤
      engelsmaS2CoordinateFiberAbelErrorEnvelope R D m r := by
  simpa [engelsmaS2CoordinateFiberIntegralMain,
    engelsmaS2CoordinateFiberAbelErrorEnvelope] using
      (abs_maynardS2CoordinateFiberSum_engelsmaSmallK_sub_integral_le_uniform
        m hr hrm hQ hR)

set_option maxRecDepth 3000 in
theorem abs_maynardS2CoordinateFiberSum_sq_sub_integralMain_sq_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hrm : r m = 1)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r))
    (hR : 1 < R) :
    |maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R (primorial D)
          (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
            engelsmaSmallKCandidate) m r ^ 2 -
        engelsmaS2CoordinateFiberIntegralMain R D m r ^ 2| ≤
      engelsmaS2CoordinateFiberAbelErrorEnvelope R D m r *
        (2 * |engelsmaS2CoordinateFiberIntegralMain R D m r| +
          engelsmaS2CoordinateFiberAbelErrorEnvelope R D m r) := by
  let F := maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R
    (primorial D) (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
      engelsmaSmallKCandidate) m r
  let M := engelsmaS2CoordinateFiberIntegralMain R D m r
  let E := engelsmaS2CoordinateFiberAbelErrorEnvelope R D m r
  have hFM : |F - M| ≤ E := by
    simpa [F, M, E] using
      (abs_maynardS2CoordinateFiberSum_sub_integralMain_le
        m hr hrm hQ hR)
  have hE : 0 ≤ E := (abs_nonneg (F - M)).trans hFM
  have hF : |F| ≤ |M| + E := by
    calc
      |F| = |(F - M) + M| := by congr 1; ring
      _ ≤ |F - M| + |M| := abs_add_le _ _
      _ ≤ E + |M| := add_le_add hFM le_rfl
      _ = |M| + E := by ring
  have hsum : |F + M| ≤ 2 * |M| + E := by
    calc
      |F + M| ≤ |F| + |M| := abs_add_le _ _
      _ ≤ (|M| + E) + |M| := add_le_add hF le_rfl
      _ = 2 * |M| + E := by ring
  calc
    |F ^ 2 - M ^ 2| = |(F - M) * (F + M)| := by congr 1; ring
    _ = |F - M| * |F + M| := abs_mul _ _
    _ ≤ E * (2 * |M| + E) :=
      mul_le_mul hFM hsum (abs_nonneg _) hE

theorem engelsmaS2CoordinateFiberIntegralMain_sq_div_gProduct_eq_outerSquarefree
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ)
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hrm : r m = 1) :
    engelsmaS2CoordinateFiberIntegralMain R D m r ^ 2 /
        ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ) =
      preSieveSingularSeries D ^ 2 *
        maynardS2OuterSquarefreeAF (primorial D)
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) *
        ((Real.log R) *
          (∫ x in (0 : ℝ)..(
            Real.log (maynardS2CoordinateFiberEndpoint R
              (maynardS2OffCoordinateProduct
                BoundedGaps.engelsmaTuple m r)) / Real.log R),
            engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2 := by
  have hweight :=
    maynardS2CoordinateFiberSingularSeries_sq_div_gProduct_eq_outerSquarefree
      m r hr hrm
  rw [engelsmaS2CoordinateFiberIntegralMain]
  calc
    (maynardS2CoordinateFiberSingularSeries D m r * Real.log R *
          (∫ x in (0 : ℝ)..(
            Real.log (maynardS2CoordinateFiberEndpoint R
              (maynardS2OffCoordinateProduct
                BoundedGaps.engelsmaTuple m r)) / Real.log R),
            engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2 /
        ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ) =
      (maynardS2CoordinateFiberSingularSeries D m r ^ 2 /
        ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)) *
        ((Real.log R) *
          (∫ x in (0 : ℝ)..(
            Real.log (maynardS2CoordinateFiberEndpoint R
              (maynardS2OffCoordinateProduct
                BoundedGaps.engelsmaTuple m r)) / Real.log R),
            engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2 := by ring
    _ = _ := by rw [hweight]

end BoundedGaps.Maynard
