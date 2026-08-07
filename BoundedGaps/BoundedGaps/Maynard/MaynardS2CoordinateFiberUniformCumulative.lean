import BoundedGaps.Maynard.MaynardS2CoordinateFiberLargeEndpoint

noncomputable section

/-!
# Uniform S2 coordinate-fiber cumulative estimate

The global and squarefree large-endpoint bounds are combined at the augmented
modulus threshold into one error envelope for the Abel interval.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped ArithmeticFunction.Moebius BigOperators

theorem abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_uniform
    {H : Finset ℕ} {D R Q : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hQ : 0 < Q) {t : ℝ} (ht : 1 ≤ t)
    (htQ : t ≤ Q) :
    |abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
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
              Real.log 2)) := by
  let P := maynardS2OffCoordinateProduct H m r
  let W := primorial D * P
  let Elarge : ℝ :=
    2 * (Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant) + 2 +
      Real.log 2 * Real.exp
        (primeLogPredecessorDivisorMass W / Real.log 2) +
      coprimeHarmonicDensity W *
        (|Real.eulerMascheroniConstant| +
          primeLogPredecessorDivisorMass W + Real.log 2)
  let Eglobal : ℝ :=
    2 * (Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant) +
      coprimeHarmonicDensity W *
        ((W : ℝ) + 1 + 2 * Real.log Q +
          2 * |Real.eulerMascheroniConstant| +
          2 * primeLogPredecessorDivisorMass W + Real.log 2)
  have hW : 0 < W := Nat.mul_pos (primorial_pos D)
    (maynardS2OffCoordinateProduct_pos m r hr)
  have hlarge :
      |abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
      max Elarge Eglobal := by
    by_cases hWQ : W ≤ ⌊t⌋₊
    · have h := abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_large
        m r hr ht (by simpa [W, P] using hWQ)
      have hqOne : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).2 ht
      have hqPos : (0 : ℝ) < ⌊t⌋₊ := by
        exact_mod_cast (Nat.zero_lt_of_lt hqOne)
      have hratio : (W : ℝ) / (⌊t⌋₊ : ℝ) ≤ 1 := by
        apply (div_le_iff₀ hqPos).2
        simpa using hWQ
      have htwo : 2 * (W : ℝ) / (⌊t⌋₊ : ℝ) ≤ 2 := by
        calc
          2 * (W : ℝ) / (⌊t⌋₊ : ℝ) =
              2 * ((W : ℝ) / (⌊t⌋₊ : ℝ)) := by ring
          _ ≤ 2 := by linarith
      have h' :
          |abelCumulative
              (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
            maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
          2 * (Real.exp 16 +
            4 * reciprocalTotientCorrectionQuarterConstant) +
            2 * (W : ℝ) / (⌊t⌋₊ : ℝ) +
            Real.log 2 * Real.exp
              (primeLogPredecessorDivisorMass W / Real.log 2) +
            coprimeHarmonicDensity W *
              (|Real.eulerMascheroniConstant| +
                primeLogPredecessorDivisorMass W + Real.log 2) := by
        convert h using 1
        simp only [W, P, Nat.cast_mul]
        ring
      have hE :
          |abelCumulative
              (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
            maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
          Elarge := by
        dsimp [Elarge]
        calc
          _ ≤ 2 * (Real.exp 16 +
              4 * reciprocalTotientCorrectionQuarterConstant) +
              2 * (W : ℝ) / (⌊t⌋₊ : ℝ) +
              Real.log 2 * Real.exp
                (primeLogPredecessorDivisorMass W / Real.log 2) +
              coprimeHarmonicDensity W *
                (|Real.eulerMascheroniConstant| +
                  primeLogPredecessorDivisorMass W + Real.log 2) := h'
          _ ≤ _ := by linarith [htwo]
      exact hE.trans (le_max_left Elarge Eglobal)
    · have hsmall := abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le
        m r hr hQ ht htQ
      have hsmall' :
          |abelCumulative
              (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
            maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤ Eglobal := by
        simpa [Eglobal, W, P] using hsmall
      exact hsmall'.trans (le_max_right Elarge Eglobal)
  simpa [Elarge, Eglobal, W, P] using hlarge

end BoundedGaps.Maynard
