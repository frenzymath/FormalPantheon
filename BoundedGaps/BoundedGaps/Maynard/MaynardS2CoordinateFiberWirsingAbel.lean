import BoundedGaps.Maynard.MaynardS2CoordinateFiberWirsingLogarithmic
import BoundedGaps.Maynard.MaynardS2CoordinateFiberPolynomial

noncomputable section

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped ArithmeticFunction.Moebius BigOperators

/-!
# Wirsing--Abel estimate for an S2 coordinate fiber

SEM-388 inserts the SEM-387 logarithmic cumulative bound into the exact
calculus-discharged two-scale Abel theorem for the Engelsma polynomial slice.
The integral retains the strict arithmetic endpoint `log Q / log R`; extending
it to the complete face is a later step.
-/

theorem exists_uniform_abs_maynardS2CoordinateFiberSum_engelsmaSmallK_sub_integral_le_wirsing :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
          {r : BoundedGaps.engelsmaTuple → ℕ},
        IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
          (primorial D) r →
        r m = 1 →
        2 ≤ Real.log R →
        1 < maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) →
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
          (11 * maynardS2CoordinateFiberSingularSeries D m r *
            (K + Real.log D +
              (Real.log (Real.log R) + C + 2) + Real.log 2)) *
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
  obtain ⟨K, C, hK, hC, hcum⟩ :=
    exists_uniform_abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_logarithmic
  refine ⟨K, C, hK, hC, ?_⟩
  intro R D m r hr hrm hlogR hQ
  let P : ℕ := maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r
  let Q : ℕ := maynardS2CoordinateFiberEndpoint R P
  let S : ℝ := maynardS2CoordinateFiberSingularSeries D m r
  let B : ℝ := K + Real.log D +
    (Real.log (Real.log R) + C + 2) + Real.log 2
  let E : ℝ := 11 * S * B
  have hP : 0 < P := by
    dsimp [P]
    exact maynardS2OffCoordinateProduct_pos m r hr
  have hPR : P < R := by
    dsimp [P]
    exact maynardS2OffCoordinateProduct_lt m r hr
  have hR : 1 < R := by omega
  have hS : 0 ≤ S := by
    dsimp [S]
    exact (maynardS2CoordinateFiberSingularSeries_pos m r hr).le
  have hlogD : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hloglogR : 0 ≤ Real.log (Real.log R) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      |abelCumulative
          (maynardS2CoordinateFiberCoefficient
            BoundedGaps.engelsmaTuple (primorial D) m r) t -
        S * Real.log t| ≤ E := by
    intro t ht
    have h := hcum m r hr hlogR ht.1
    simpa [E, S, B, Q, P] using h
  have h := abs_maynardS2CoordinateFiberSum_engelsmaSmallK_sub_integral_le
    m hr hrm (by simpa [Q, P] using hQ) hR hE happrox
  simpa [E, S, B, Q, P] using h

end BoundedGaps.Maynard
