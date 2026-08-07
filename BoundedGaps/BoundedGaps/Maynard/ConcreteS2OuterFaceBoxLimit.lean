import BoundedGaps.Maynard.ConcreteS2OuterMeanLimit
import BoundedGaps.Maynard.MaynardS2OuterFaceBox

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

noncomputable def engelsmaS2OuterCoordinateOneFaceBoxMass
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ maynardS2OuterCoordinateOneFaceBox
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m,
    ∏ h : BoundedGaps.engelsmaTuple,
      maynardS2OuterSquarefreeAF (engelsmaMaynardModulus N) (r h)

noncomputable def normalizedEngelsmaS2OuterCoordinateOneFaceBoxMass
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  engelsmaS2OuterCoordinateOneFaceBoxMass alpha N m /
    (maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^
        ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card

noncomputable def normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  engelsmaS2OuterCoordinateOneFaceBoxMass alpha N m /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^
        ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card

set_option maxRecDepth 5000 in
theorem tendsto_normalizedEngelsmaS2OuterCoordinateOneFaceBoxMass
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2OuterCoordinateOneFaceBoxMass alpha N m)
      atTop (nhds 1) := by
  have hscalar :=
    tendsto_engelsmaS2OuterSquarefreeMean_div_leadingTerm_one halpha
  have hpow : Tendsto (fun N : ℕ =>
      (maynardS2OuterSquarefreeMean (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) /
        (maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N))) ^
        ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card)
      atTop (nhds 1) := by
    simpa using hscalar.pow
      ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card
  apply hpow.congr'
  filter_upwards [] with N
  unfold normalizedEngelsmaS2OuterCoordinateOneFaceBoxMass
    engelsmaS2OuterCoordinateOneFaceBoxMass
  unfold engelsmaMaynardModulus
  rw [maynardS2OuterCoordinateOneFaceBox_sum_eq_erase_prod_mean]
  rw [Finset.prod_const]
  rw [div_pow]

set_option maxRecDepth 5000 in
theorem tendsto_normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve alpha N m)
      atTop (nhds 1) := by
  have hscalar :=
    tendsto_engelsmaS2OuterSquarefreeMean_div_preSieveLeadingTerm_one halpha
  have hpow : Tendsto (fun N : ℕ =>
      (maynardS2OuterSquarefreeMean (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N))) ^
        ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card)
      atTop (nhds 1) := by
    simpa using hscalar.pow
      ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card
  apply hpow.congr'
  filter_upwards [] with N
  unfold normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve
    engelsmaS2OuterCoordinateOneFaceBoxMass
  unfold engelsmaMaynardModulus
  rw [maynardS2OuterCoordinateOneFaceBox_sum_eq_erase_prod_mean]
  rw [Finset.prod_const]
  rw [div_pow]

end BoundedGaps.Maynard
