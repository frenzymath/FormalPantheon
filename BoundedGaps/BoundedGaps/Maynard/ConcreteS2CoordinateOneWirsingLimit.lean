import BoundedGaps.Maynard.ConcreteScalarEndpointZero
import BoundedGaps.Maynard.ConcreteS2CoordinateFiberGoodWirsingLimit
import BoundedGaps.Maynard.ConcreteS2ReciprocalGShortBoundary

set_option maxRecDepth 9000

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

/-!
# Coordinate-one fiber-square limit

SEM-395 reinserts the exact endpoint-one short fiber into the SEM-394 good
fiber limit. The short diagonal is first raised from its 104-coordinate scale
to the full exponent-106 square scale using the reciprocal-scale limit.

This is the project composition corresponding to Maynard2013v3, Section 5,
Lemma 5.2 and Section 6, equations (6.10)--(6.16). Its main term deliberately
uses the complementary full-face moment; the strict-endpoint loss has already
been paid once on that path.
-/

theorem tendsto_engelsmaS2CoordinateFiberShortSquareDiagonal_div_squareScale_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      engelsmaS2CoordinateFiberShortSquareDiagonal
        (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m /
      (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) ^ 106)
      atTop (nhds 0) := by
  have hshort :=
    tendsto_normalizedEngelsmaS2CoordinateFiberShortSquareDiagonal_zero
      halpha m
  have hinv := tendsto_inv_engelsmaSingularSeries_mul_logRadius_zero halpha
  have hprod := hshort.mul (hinv.pow 2)
  have hprod' : Tendsto (fun N : ℕ =>
      (engelsmaS2CoordinateFiberShortSquareDiagonal
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) ^
            Fintype.card (engelsmaOffFaceFinset m)) *
      (1 / (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N))) ^ 2)
      atTop (nhds 0) := by
    simpa using hprod
  apply hprod'.congr'
  have hL := tendsto_log_engelsmaMaynardRadius_atTop halpha
  filter_upwards [hL.eventually (eventually_gt_atTop 0)] with N hLpos
  let R := engelsmaMaynardRadius alpha N
  let D := tripleLogCutoff (N - 1)
  let S := preSieveSingularSeries D
  let L := Real.log R
  have hS : 0 < S := by
    dsimp [S]
    exact preSieveSingularSeries_pos D
  have hLpos' : 0 < L := by simpa [L, R] using hLpos
  have hSL : S * L ≠ 0 := (mul_pos hS hLpos').ne'
  have hk : Fintype.card (engelsmaOffFaceFinset m) = 104 := by
    simp [engelsmaOffFaceFinset, Finset.card_erase_of_mem m.property,
      BoundedGaps.engelsmaTuple_card]
  rw [hk]
  field_simp [hSL]

theorem tendsto_normalizedEngelsmaS2CoordinateOneFiberSquareDiagonal_sub_complementOuterMoment_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      (engelsmaMaynardS2CoordinateOneFiberSquareDiagonal alpha N m -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
          engelsmaS2CoordinateFiberGoodComplementOuterMoment
            (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) ^ 106)
      atTop (nhds 0) := by
  have hshort :=
    tendsto_engelsmaS2CoordinateFiberShortSquareDiagonal_div_squareScale_zero
      halpha m
  have hgood :=
    tendsto_normalizedEngelsmaS2CoordinateFiberGoodSquareDiagonal_sub_complementOuterMoment_zero
      halpha m
  have hsum : Tendsto (fun N : ℕ =>
      (engelsmaS2CoordinateFiberShortSquareDiagonal
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) ^ 106) +
      ((engelsmaS2CoordinateFiberGoodSquareDiagonal
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
          engelsmaS2CoordinateFiberGoodComplementOuterMoment
            (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) ^ 106))
      atTop (nhds 0) := by
    simpa using hshort.add hgood
  apply hsum.congr'
  filter_upwards [] with N
  rw [engelsmaMaynardS2CoordinateOneFiberSquareDiagonal_eq_good_add_short]
  ring_nf

end BoundedGaps.Maynard
