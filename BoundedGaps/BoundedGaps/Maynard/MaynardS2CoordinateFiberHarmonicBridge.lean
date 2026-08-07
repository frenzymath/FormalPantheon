import BoundedGaps.Maynard.MaynardS2CoordinateFiberLocalSeries
import BoundedGaps.Maynard.CoprimeHarmonicGlobalBound

noncomputable section

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped ArithmeticFunction.Moebius BigOperators

theorem coprimeHarmonicDensity_augmented_eq_coordinateFiberSingularSeries
    {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R (primorial D) r) :
    coprimeHarmonicDensity
        (primorial D * maynardS2OffCoordinateProduct H m r) =
      maynardS2CoordinateFiberSingularSeries D m r := by
  let P := maynardS2OffCoordinateProduct H m r
  have hP : 0 < P := maynardS2OffCoordinateProduct_pos m r hr
  have hD : 0 < primorial D := primorial_pos D
  have hcop : Nat.Coprime (primorial D) P :=
    maynardS2OffCoordinateProduct_coprime m r hr
  have htotient : Nat.totient (primorial D * P) =
      Nat.totient (primorial D) * Nat.totient P :=
    Nat.totient_mul hcop
  have hDreal : (primorial D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPreal : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  rw [maynardS2CoordinateFiberSingularSeries_eq_preSieve_mul m r hr]
  rw [preSieveSingularSeries_eq_totient_div]
  unfold coprimeHarmonicDensity
  rw [htotient]
  simp only [Nat.cast_mul]
  dsimp [P]
  field_simp [hDreal, hPreal]

theorem abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le
    {H : Finset ℕ} {D R Q : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (hQ : 0 < Q) {t : ℝ} (ht : 1 ≤ t)
    (htQ : t ≤ Q) :
    |abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
      2 * (Real.exp 16 +
        4 * reciprocalTotientCorrectionQuarterConstant) +
      coprimeHarmonicDensity
          (primorial D * maynardS2OffCoordinateProduct H m r) *
        ((primorial D * maynardS2OffCoordinateProduct H m r : ℝ) + 1 +
          2 * Real.log Q + 2 * |Real.eulerMascheroniConstant| +
          2 * primeLogPredecessorDivisorMass
            (primorial D * maynardS2OffCoordinateProduct H m r) +
          Real.log 2) := by
  let P := maynardS2OffCoordinateProduct H m r
  let W := primorial D * P
  have hW : 0 < W := Nat.mul_pos (primorial_pos D)
    (maynardS2OffCoordinateProduct_pos m r hr)
  have hDensity := coprimeHarmonicDensity_augmented_eq_coordinateFiberSingularSeries
    m r hr
  have hfloor := abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_coprimeHarmonicSum_le
    (W := primorial D) m r t
  have hmain := abs_coprimeHarmonicSum_natFloor_sub_mainTerm_le_global
    hW ht
  have hlogt : Real.log t ≤ Real.log Q := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact zero_lt_one.trans_le ht
    · have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
      exact hQreal
    · exact htQ
  have hDensityNonneg : 0 ≤ coprimeHarmonicDensity W := by
    unfold coprimeHarmonicDensity
    positivity
  have hmainQ :
      coprimeHarmonicDensity W *
          ((W : ℝ) + 1 + 2 * Real.log t +
            2 * |Real.eulerMascheroniConstant| +
            2 * primeLogPredecessorDivisorMass W + Real.log 2) ≤
        coprimeHarmonicDensity W *
          ((W : ℝ) + 1 + 2 * Real.log Q +
            2 * |Real.eulerMascheroniConstant| +
            2 * primeLogPredecessorDivisorMass W + Real.log 2) := by
    apply mul_le_mul_of_nonneg_left
    · linarith
    · exact hDensityNonneg
  have hDensityW : coprimeHarmonicDensity W =
      maynardS2CoordinateFiberSingularSeries D m r := by
    simpa [W, P] using hDensity
  have hMass : 0 ≤ primeLogPredecessorDivisorMass W := by
    unfold primeLogPredecessorDivisorMass
    positivity
  have hfloorW :
      |abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        coprimeHarmonicSum W ⌊t⌋₊| ≤
      2 * (Real.exp 16 +
        4 * reciprocalTotientCorrectionQuarterConstant) := by
    simpa [W, P] using hfloor
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
    rw [hdiff, abs_mul, ← hDensityW, abs_of_nonneg hDensityNonneg]
    apply mul_le_mul_of_nonneg_left
    · calc
        |Real.eulerMascheroniConstant +
            primeLogPredecessorDivisorMass W| ≤
            |Real.eulerMascheroniConstant| +
              |primeLogPredecessorDivisorMass W| := abs_add_le _ _
        _ = |Real.eulerMascheroniConstant| +
              primeLogPredecessorDivisorMass W := by
          rw [abs_of_nonneg hMass]
    · exact hDensityNonneg
  change |abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤ _
  rw [show abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t =
      (abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        coprimeHarmonicSum W ⌊t⌋₊) +
      (coprimeHarmonicSum W ⌊t⌋₊ -
        coprimeHarmonicMainTerm W t) +
      (coprimeHarmonicMainTerm W t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t) by
          unfold coprimeHarmonicMainTerm
          rw [hDensityW]
          ring]
  calc
    |(abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        coprimeHarmonicSum W ⌊t⌋₊) +
      (coprimeHarmonicSum W ⌊t⌋₊ - coprimeHarmonicMainTerm W t) +
      (coprimeHarmonicMainTerm W t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t)| ≤
        |(abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        coprimeHarmonicSum W ⌊t⌋₊) +
      (coprimeHarmonicSum W ⌊t⌋₊ - coprimeHarmonicMainTerm W t)| +
      |coprimeHarmonicMainTerm W t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| := by
      exact abs_add_le _ _
    _ ≤ (|abelCumulative
          (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
        coprimeHarmonicSum W ⌊t⌋₊| +
      |coprimeHarmonicSum W ⌊t⌋₊ - coprimeHarmonicMainTerm W t|) +
      |coprimeHarmonicMainTerm W t -
        maynardS2CoordinateFiberSingularSeries D m r * Real.log t| := by
      exact add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ 2 * (Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant) +
        coprimeHarmonicDensity W *
          ((W : ℝ) + 1 + 2 * Real.log t +
            2 * |Real.eulerMascheroniConstant| +
            2 * primeLogPredecessorDivisorMass W + Real.log 2) := by
      calc
        (|abelCumulative
            (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
          coprimeHarmonicSum W ⌊t⌋₊| +
          |coprimeHarmonicSum W ⌊t⌋₊ - coprimeHarmonicMainTerm W t|) +
            |coprimeHarmonicMainTerm W t -
              maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
          (2 * (Real.exp 16 +
            4 * reciprocalTotientCorrectionQuarterConstant) +
            coprimeHarmonicDensity W *
              ((W : ℝ) + 1 + 2 * Real.log t +
                |Real.eulerMascheroniConstant| +
                primeLogPredecessorDivisorMass W + Real.log 2)) +
            coprimeHarmonicDensity W *
              (|Real.eulerMascheroniConstant| +
                primeLogPredecessorDivisorMass W) :=
          add_le_add (add_le_add hfloorW hmain) hlast
        _ = 2 * (Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant) +
            coprimeHarmonicDensity W *
              ((W : ℝ) + 1 + 2 * Real.log t +
                2 * |Real.eulerMascheroniConstant| +
                2 * primeLogPredecessorDivisorMass W + Real.log 2) := by ring
    _ ≤ _ := by
      have hfinal := add_le_add_left hmainQ
        (2 * (Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant))
      simpa [W, P] using hfinal

end BoundedGaps.Maynard
