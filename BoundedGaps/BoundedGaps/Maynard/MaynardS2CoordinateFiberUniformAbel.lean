import BoundedGaps.Maynard.MaynardS2CoordinateFiberPolynomial
import BoundedGaps.Maynard.MaynardS2CoordinateFiberUniformCumulative

noncomputable section

/-!
# Uniform coordinate-fiber Abel transfer

The endpoint-split cumulative envelope is supplied to the polynomial Abel
interface, yielding the explicit arithmetic-to-integral estimate.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable def maynardS2CoordinateFiberUniformCumulativeError
    (H : Finset ℕ) (D Q : ℕ) (m : H) (r : H → ℕ) : ℝ :=
  max
    (2 * (Real.exp 16 +
      4 * reciprocalTotientCorrectionQuarterConstant) + 2 +
      Real.log 2 * Real.exp
        (primeLogPredecessorDivisorMass
          (primorial D * maynardS2OffCoordinateProduct H m r) /
          Real.log 2) +
      coprimeHarmonicDensity
          (primorial D * maynardS2OffCoordinateProduct H m r) *
        (|Real.eulerMascheroniConstant| +
          primeLogPredecessorDivisorMass
            (primorial D * maynardS2OffCoordinateProduct H m r) +
          Real.log 2))
    (2 * (Real.exp 16 +
      4 * reciprocalTotientCorrectionQuarterConstant) +
      coprimeHarmonicDensity
          (primorial D * maynardS2OffCoordinateProduct H m r) *
        ((primorial D * maynardS2OffCoordinateProduct H m r : ℝ) + 1 +
          2 * Real.log Q + 2 * |Real.eulerMascheroniConstant| +
          2 * primeLogPredecessorDivisorMass
            (primorial D * maynardS2OffCoordinateProduct H m r) +
          Real.log 2))

theorem maynardS2CoordinateFiberUniformCumulativeError_nonneg
    {H : Finset ℕ} {D Q : ℕ} (m : H) (r : H → ℕ)
    (hQ : 0 < Q) :
    0 ≤ maynardS2CoordinateFiberUniformCumulativeError H D Q m r := by
  unfold maynardS2CoordinateFiberUniformCumulativeError
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  have hMass : 0 ≤ primeLogPredecessorDivisorMass
      (primorial D * maynardS2OffCoordinateProduct H m r) := by
    unfold primeLogPredecessorDivisorMass
    positivity
  have hDensity : 0 ≤ coprimeHarmonicDensity
      (primorial D * maynardS2OffCoordinateProduct H m r) := by
    unfold coprimeHarmonicDensity
    positivity
  have hC : 0 ≤ reciprocalTotientCorrectionQuarterConstant := by
    unfold reciprocalTotientCorrectionQuarterConstant
    positivity
  apply le_trans (b :=
    2 * (Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant) +
      coprimeHarmonicDensity
        (primorial D * maynardS2OffCoordinateProduct H m r) *
        ((primorial D * maynardS2OffCoordinateProduct H m r : ℝ) + 1 +
          2 * Real.log Q + 2 * |Real.eulerMascheroniConstant| +
          2 * primeLogPredecessorDivisorMass
            (primorial D * maynardS2OffCoordinateProduct H m r) +
          Real.log 2))
  · apply add_nonneg
    · exact mul_nonneg (by norm_num)
        (add_nonneg (by positivity) (mul_nonneg (by norm_num) hC))
    · apply mul_nonneg hDensity
      have hWnonneg : 0 ≤ (primorial D *
          maynardS2OffCoordinateProduct H m r : ℝ) := by positivity
      have habs : 0 ≤ |Real.eulerMascheroniConstant| := abs_nonneg _
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith [hlogQ, hMass, hWnonneg, habs, hlog2]
  · exact le_max_right _ _

set_option maxRecDepth 3000 in
theorem abs_maynardS2CoordinateFiberSum_engelsmaSmallK_sub_integral_le_uniform
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
        maynardS2CoordinateFiberSingularSeries D m r * Real.log R *
          (∫ x in (0 : ℝ)..(
            Real.log (maynardS2CoordinateFiberEndpoint R
              (maynardS2OffCoordinateProduct
                BoundedGaps.engelsmaTuple m r)) /
            Real.log R),
            engelsmaS2CoordinateFiberPolynomialTest R m r x)| ≤
      maynardS2CoordinateFiberUniformCumulativeError
          BoundedGaps.engelsmaTuple
          D
          (maynardS2CoordinateFiberEndpoint R
            (maynardS2OffCoordinateProduct
              BoundedGaps.engelsmaTuple m r)) m r *
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
                (Real.log z / Real.log R)) t|) := by
  let Q := maynardS2CoordinateFiberEndpoint R
    (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)
  let E := maynardS2CoordinateFiberUniformCumulativeError
    BoundedGaps.engelsmaTuple D Q m r
  have hQpos : 0 < Q := by omega
  have hE : 0 ≤ E := by
    exact maynardS2CoordinateFiberUniformCumulativeError_nonneg m r hQpos
  have happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      |abelCumulative
          (maynardS2CoordinateFiberCoefficient
            BoundedGaps.engelsmaTuple (primorial D) m r) t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤ E := by
    intro t ht
    have h := abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_uniform
      m r hr hQpos ht.1 ht.2
    simpa only [E, maynardS2CoordinateFiberUniformCumulativeError] using h
  have h := abs_maynardS2CoordinateFiberSum_engelsmaSmallK_sub_integral_le
    m hr hrm hQ hR hE happrox
  simpa [E, Q] using h

end BoundedGaps.Maynard
