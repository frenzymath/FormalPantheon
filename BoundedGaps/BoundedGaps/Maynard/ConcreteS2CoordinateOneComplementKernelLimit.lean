import BoundedGaps.Maynard.ConcreteS2RestrictedYStrongLimit
import BoundedGaps.Maynard.ConcreteS2RestrictedCrossStrongLimit
import BoundedGaps.Maynard.ConcreteS2CoordinateOneWirsingLimit

noncomputable section

/-!
# Coordinate-one complementary kernel limit

SEM-396 combines the strong restricted-Y perturbation, the strong
incompatible correction, and SEM-395's full-fiber complementary-moment limit.
The resulting exact kernel is normalized by the exponent-106 square scale.
-/

namespace BoundedGaps.Maynard

open Filter

theorem tendsto_normalizedEngelsmaS2CoordinateOneKernel_sub_complementOuterMoment_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      (((engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
          engelsmaMaynardS2RestrictedCrossCorrection alpha N m) -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
          engelsmaS2CoordinateFiberGoodComplementOuterMoment
            (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) ^ 106))
      atTop (nhds 0) := by
  have hY :=
    tendsto_normalizedEngelsmaS2CoordinateOneYDiagonal_sub_fiberSquareDiagonal_zero
      halpha m
  have hfiber :=
    tendsto_normalizedEngelsmaS2CoordinateOneFiberSquareDiagonal_sub_complementOuterMoment_zero
      halpha m
  have hcross :=
    tendsto_engelsmaS2RestrictedCrossCorrection_div_squareScale_zero
      halpha m
  have hsum : Tendsto (fun N : ℕ =>
      ((engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
        engelsmaMaynardS2CoordinateOneFiberSquareDiagonal alpha N m) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) ^ 106) +
      ((engelsmaMaynardS2CoordinateOneFiberSquareDiagonal alpha N m -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
          engelsmaS2CoordinateFiberGoodComplementOuterMoment
            (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) ^ 106) -
      (engelsmaMaynardS2RestrictedCrossCorrection alpha N m /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) ^ 106))
      atTop (nhds 0) := by
    simpa using (hY.add hfiber).sub hcross
  apply hsum.congr'
  filter_upwards [] with N
  ring

end BoundedGaps.Maynard
