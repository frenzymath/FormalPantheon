import BoundedGaps.Maynard.MaynardS2OuterCorrectionMean
import BoundedGaps.Maynard.MaynardS2OuterSingularSeries
import BoundedGaps.Maynard.PrimorialCoprimeHarmonic

noncomputable section

/-!
Composition of the finite S2 outer mean with its scalar primorial main term.
Maynard2013v3, source lines 552--560, uses this outer singular-density
replacement in the prime-weighted main term.
-/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction Real
open scoped BigOperators

theorem abs_maynardS2OuterInfiniteSingularTail_le
    {D : ℕ} (hD : 2 ≤ D) :
    |maynardS2OuterInfiniteSingularTail D| ≤ 1 + 8 / (D : ℝ) := by
  have hTail := abs_maynardS2OuterInfiniteSingularTail_sub_one_le hD
  calc
    |maynardS2OuterInfiniteSingularTail D| =
        |(maynardS2OuterInfiniteSingularTail D - 1) + 1| := by ring_nf
    _ ≤ |maynardS2OuterInfiniteSingularTail D - 1| + |(1 : ℝ)| :=
      abs_add_le _ _
    _ ≤ 8 / (D : ℝ) + 1 := by
      rw [abs_one]
      exact add_le_add hTail le_rfl
    _ = 1 + 8 / (D : ℝ) := by ring

set_option maxHeartbeats 800000 in
theorem abs_maynardS2OuterSquarefreeMean_sub_singularSeries_mul_logMainTerm_le
    {D Q : ℕ} (hD : 2 ≤ D) (hDQ : primorial D ≤ Q) :
    |maynardS2OuterSquarefreeMean (primorial D) Q -
        maynardS2OuterSingularSeries D *
          (Real.log Q + primeLogPredecessorSum D)| ≤
      2 * (Real.exp 16 +
        8 * maynardS2OuterCorrectionQuarterConstant) +
        (1 + 8 / (D : ℝ)) * primorial D := by
  let C := Real.exp 16 + 8 * maynardS2OuterCorrectionQuarterConstant
  let W := primorial D
  let T := maynardS2OuterInfiniteSingularTail D
  let H := coprimeHarmonicSum W Q
  let M := primorialCoprimeHarmonicMainTerm D Q
  have hOuter := abs_maynardS2OuterSquarefreeMean_sub_singularTail_mul_harmonic_le
    hD Q
  have hHarmonic := abs_coprimeHarmonicSum_sub_primorialMainTerm_le hDQ
  have hTail := abs_maynardS2OuterInfiniteSingularTail_le hD
  have hSecond : |T * (H - M)| ≤ (1 + 8 / (D : ℝ)) * W := by
    rw [abs_mul]
    calc
      |T| * |H - M| ≤ (1 + 8 / (D : ℝ)) * |H - M| := by
        exact mul_le_mul_of_nonneg_right hTail (abs_nonneg _)
      _ ≤ (1 + 8 / (D : ℝ)) * W := by
        exact mul_le_mul_of_nonneg_left hHarmonic (by positivity)
  have hDecomp :
      maynardS2OuterSquarefreeMean W Q -
          maynardS2OuterSingularSeries D *
            (Real.log Q + primeLogPredecessorSum D) =
        (maynardS2OuterSquarefreeMean W Q - T * H) + T * (H - M) := by
    simp only [W, T, H, M, maynardS2OuterSingularSeries,
      primorialCoprimeHarmonicMainTerm]
    ring
  rw [hDecomp]
  calc
    |maynardS2OuterSquarefreeMean W Q - T * H + T * (H - M)| ≤
        |maynardS2OuterSquarefreeMean W Q - T * H| + |T * (H - M)| :=
      abs_add_le _ _
    _ ≤ 2 * C + ((1 + 8 / (D : ℝ)) * W) := by
      exact add_le_add hOuter hSecond
    _ = 2 * (Real.exp 16 +
        8 * maynardS2OuterCorrectionQuarterConstant) +
        (1 + 8 / (D : ℝ)) * primorial D := by
      simp only [C, W]

end BoundedGaps.Maynard
