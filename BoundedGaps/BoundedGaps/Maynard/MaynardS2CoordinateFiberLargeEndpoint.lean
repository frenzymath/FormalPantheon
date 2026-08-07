import BoundedGaps.Maynard.MaynardS2CoordinateFiberHarmonicBridge
import BoundedGaps.Maynard.SquarefreeReciprocalDivisor

noncomputable section

/-!
# Large-endpoint S2 coordinate-fiber estimate

Beyond the augmented modulus, the squarefree coprime-harmonic discrepancy has
the smooth reciprocal-divisor envelope. This replaces the global `W` penalty
by the quotient `W / floor(t)` in the large-endpoint branch.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped ArithmeticFunction.Moebius BigOperators

theorem abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_large
    {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R (primorial D) r)
    {t : ℝ} (ht : 1 ≤ t)
    (hWQ : primorial D * maynardS2OffCoordinateProduct H m r ≤ ⌊t⌋₊) :
    |abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
      2 * (Real.exp 16 +
        4 * reciprocalTotientCorrectionQuarterConstant) +
      2 * ((primorial D * maynardS2OffCoordinateProduct H m r : ℝ) /
        (⌊t⌋₊ : ℝ)) +
      Real.log 2 * Real.exp
        (primeLogPredecessorDivisorMass
          (primorial D * maynardS2OffCoordinateProduct H m r) /
          Real.log 2) +
      coprimeHarmonicDensity
          (primorial D * maynardS2OffCoordinateProduct H m r) *
        (|Real.eulerMascheroniConstant| +
          primeLogPredecessorDivisorMass
            (primorial D * maynardS2OffCoordinateProduct H m r) + Real.log 2) := by
  let P := maynardS2OffCoordinateProduct H m r
  let W := primorial D * P
  let q : ℕ := ⌊t⌋₊
  have hW : 0 < W := Nat.mul_pos (primorial_pos D)
    (maynardS2OffCoordinateProduct_pos m r hr)
  have hSqP := maynardS2OffCoordinateProduct_squarefree m r hr
  have hSq : Squarefree W := by
    dsimp [W]
    exact (Nat.squarefree_mul
      (maynardS2OffCoordinateProduct_coprime m r hr)).mpr
      ⟨squarefree_primorial D, hSqP⟩
  have hqOne : 1 ≤ q := by exact (Nat.one_le_floor_iff t).2 ht
  have hqPos : 0 < q := Nat.zero_lt_of_lt hqOne
  have hWQ' : W ≤ q := by simpa [W, P, q] using hWQ
  have hError := abs_coprimeHarmonicError_le_smooth_envelope hW hSq hWQ'
  have hError' :
      |coprimeHarmonicSum W q - coprimeHarmonicMainTerm W (q : ℝ)| ≤
        2 * (W : ℝ) / q +
          Real.log 2 * Real.exp
            (primeLogPredecessorDivisorMass W / Real.log 2) := by
    simpa [coprimeHarmonicError, q] using hError
  have hFloor := abs_log_natFloor_sub_log_le_log_two_global ht
  have hFloor' : |Real.log (q : ℝ) - Real.log t| ≤ Real.log 2 := by
    simpa [q] using hFloor
  have hDensity : 0 ≤ coprimeHarmonicDensity W := by
    unfold coprimeHarmonicDensity
    positivity
  have hlogq : Real.log (q : ℝ) ≤ Real.log t := by
    apply Real.strictMonoOn_log.monotoneOn
    · have hqPosR : (0 : ℝ) < q := by exact_mod_cast hqPos
      exact hqPosR
    · exact zero_lt_one.trans_le ht
    · exact Nat.floor_le (by linarith)
  have hmainFloor :
      |coprimeHarmonicMainTerm W (q : ℝ) -
          coprimeHarmonicMainTerm W t| ≤
        coprimeHarmonicDensity W * Real.log 2 := by
    unfold coprimeHarmonicMainTerm
    have hdiff :
        coprimeHarmonicDensity W *
            (Real.log (q : ℝ) + Real.eulerMascheroniConstant +
              primeLogPredecessorDivisorMass W) -
          coprimeHarmonicDensity W *
            (Real.log t + Real.eulerMascheroniConstant +
              primeLogPredecessorDivisorMass W) =
        coprimeHarmonicDensity W * (Real.log (q : ℝ) - Real.log t) := by
      ring
    rw [hdiff, abs_mul, abs_of_nonneg hDensity]
    apply mul_le_mul_of_nonneg_left
    · rw [abs_of_nonpos (sub_nonpos.mpr hlogq)]
      have h := (abs_le.mp hFloor')
      linarith
    · exact hDensity
  have hDensityW : coprimeHarmonicDensity W =
      maynardS2CoordinateFiberSingularSeries D m r := by
    simpa [W, P] using
      (coprimeHarmonicDensity_augmented_eq_coordinateFiberSingularSeries m r hr)
  have hMass : 0 ≤ primeLogPredecessorDivisorMass W := by
    unfold primeLogPredecessorDivisorMass
    positivity
  have hlast :
      |coprimeHarmonicMainTerm W t -
          maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
        coprimeHarmonicDensity W *
          (|Real.eulerMascheroniConstant| +
            primeLogPredecessorDivisorMass W) := by
    unfold coprimeHarmonicMainTerm
    rw [hDensityW]
    have hdiff :
        maynardS2CoordinateFiberSingularSeries D m r *
            (Real.log t + Real.eulerMascheroniConstant +
              primeLogPredecessorDivisorMass W) -
          maynardS2CoordinateFiberSingularSeries D m r * Real.log t =
        maynardS2CoordinateFiberSingularSeries D m r *
          (Real.eulerMascheroniConstant +
            primeLogPredecessorDivisorMass W) := by ring
    rw [hdiff, abs_mul, ← hDensityW, abs_of_nonneg hDensity]
    apply mul_le_mul_of_nonneg_left
    · calc
        |Real.eulerMascheroniConstant +
            primeLogPredecessorDivisorMass W| ≤
            |Real.eulerMascheroniConstant| +
              |primeLogPredecessorDivisorMass W| := abs_add_le _ _
        _ = |Real.eulerMascheroniConstant| +
              primeLogPredecessorDivisorMass W := by
          rw [abs_of_nonneg hMass]
    · exact hDensity
  have hfloorCorr := abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_coprimeHarmonicSum_le
    (W := primorial D) m r t
  have htriangle :
      |abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
      |abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        coprimeHarmonicSum W q| +
      |coprimeHarmonicSum W q - coprimeHarmonicMainTerm W (q : ℝ)| +
      |coprimeHarmonicMainTerm W (q : ℝ) -
        coprimeHarmonicMainTerm W t| +
      |coprimeHarmonicMainTerm W t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| := by
    rw [show abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t =
      (abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        coprimeHarmonicSum W q) +
      (coprimeHarmonicSum W q - coprimeHarmonicMainTerm W (q : ℝ)) +
      (coprimeHarmonicMainTerm W (q : ℝ) - coprimeHarmonicMainTerm W t) +
      (coprimeHarmonicMainTerm W t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t) by
          ring]
    calc
      |(abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        coprimeHarmonicSum W q) +
      (coprimeHarmonicSum W q - coprimeHarmonicMainTerm W (q : ℝ)) +
      (coprimeHarmonicMainTerm W (q : ℝ) - coprimeHarmonicMainTerm W t) +
      (coprimeHarmonicMainTerm W t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t)| ≤
        |(abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        coprimeHarmonicSum W q) +
      (coprimeHarmonicSum W q - coprimeHarmonicMainTerm W (q : ℝ)) +
      (coprimeHarmonicMainTerm W (q : ℝ) - coprimeHarmonicMainTerm W t)| +
      |coprimeHarmonicMainTerm W t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| :=
          abs_add_le _ _
      _ ≤ (|(abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        coprimeHarmonicSum W q) +
      (coprimeHarmonicSum W q - coprimeHarmonicMainTerm W (q : ℝ))| +
      |coprimeHarmonicMainTerm W (q : ℝ) - coprimeHarmonicMainTerm W t|) +
      |coprimeHarmonicMainTerm W t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| := by
          exact add_le_add (abs_add_le _ _) (le_refl _)
      _ ≤ _ := by
        exact add_le_add
          (add_le_add (abs_add_le _ _) (le_refl _)) (le_refl _)
  have hsum := add_le_add (add_le_add hfloorCorr hError') hmainFloor
  have hsum' := add_le_add hsum hlast
  calc
    |abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
      2 * (Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant) +
        2 * (W : ℝ) / q +
        Real.log 2 * Real.exp
          (primeLogPredecessorDivisorMass W / Real.log 2) +
        coprimeHarmonicDensity W *
          (|Real.eulerMascheroniConstant| +
            primeLogPredecessorDivisorMass W + Real.log 2) := by
      calc
        _ ≤ |abelCumulative
              (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
            coprimeHarmonicSum W q| +
          |coprimeHarmonicSum W q - coprimeHarmonicMainTerm W (q : ℝ)| +
          |coprimeHarmonicMainTerm W (q : ℝ) - coprimeHarmonicMainTerm W t| +
          |coprimeHarmonicMainTerm W t -
            maynardS2CoordinateFiberSingularSeries D m r * Real.log t| := htriangle
        _ ≤ _ := by
          calc
            _ ≤ 2 * (Real.exp 16 +
                4 * reciprocalTotientCorrectionQuarterConstant) +
              (2 * (W : ℝ) / q +
                Real.log 2 * Real.exp
                  (primeLogPredecessorDivisorMass W / Real.log 2)) +
              coprimeHarmonicDensity W * Real.log 2 +
              coprimeHarmonicDensity W *
                (|Real.eulerMascheroniConstant| +
                  primeLogPredecessorDivisorMass W) := hsum'
            _ = _ := by ring
    _ = _ := by
      simp only [W, P, q, Nat.cast_mul]
      ring

end BoundedGaps.Maynard
