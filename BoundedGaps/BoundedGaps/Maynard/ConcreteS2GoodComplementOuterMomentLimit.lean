import BoundedGaps.Maynard.ConcreteS2GoodComplementNormalization
import BoundedGaps.Maynard.ConcreteS2OuterFaceBoxLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter

noncomputable def engelsmaS2EndpointSquareReplacementLoss
    (alpha : ℝ) (N : ℕ) : ℝ :=
  (smallKCandidateBound * Real.log 3) *
    (2 * (Real.log (engelsmaMaynardRadius alpha N) *
      smallKCandidateBound) + smallKCandidateBound * Real.log 3)

noncomputable def normalizedEngelsmaS2CoordinateFiberGoodOuterMoment
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  engelsmaS2CoordinateFiberGoodOuterMoment
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m /
    ((preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) ^
        ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card *
      Real.log (engelsmaMaynardRadius alpha N) ^ 2)

theorem tendsto_engelsmaS2EndpointSquareReplacementLoss_div_log_sq_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      engelsmaS2EndpointSquareReplacementLoss alpha N /
        Real.log (engelsmaMaynardRadius alpha N) ^ 2)
      atTop (nhds 0) := by
  let C := smallKCandidateBound * Real.log 3
  let K := smallKCandidateBound
  let L := fun N : ℕ => Real.log (engelsmaMaynardRadius alpha N)
  have hL : Tendsto L atTop atTop :=
    tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hfirst : Tendsto (fun N : ℕ => 2 * C * K / L N)
      atTop (nhds 0) := hL.const_div_atTop (2 * C * K)
  have hinv : Tendsto (fun N : ℕ => C / L N) atTop (nhds 0) :=
    hL.const_div_atTop C
  have hsecond : Tendsto (fun N : ℕ => (C / L N) ^ 2)
      atTop (nhds 0) := by simpa using hinv.pow 2
  have hsum : Tendsto (fun N : ℕ =>
      2 * C * K / L N + (C / L N) ^ 2) atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  apply hsum.congr'
  filter_upwards [hL.eventually (eventually_ne_atTop 0)] with N hLN
  unfold engelsmaS2EndpointSquareReplacementLoss
  dsimp [C, K, L]
  field_simp [hLN]

set_option maxRecDepth 6000 in
theorem tendsto_normalizedEngelsmaS2CoordinateFiberGoodOuterMoment_sub_complement_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2CoordinateFiberGoodOuterMoment alpha N m -
        normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
          alpha N m)
      atTop (nhds 0) := by
  have hLoss :=
    tendsto_engelsmaS2EndpointSquareReplacementLoss_div_log_sq_zero halpha
  have hBox :=
    tendsto_normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve
      halpha m
  have hupper : Tendsto (fun N : ℕ =>
      engelsmaS2EndpointSquareReplacementLoss alpha N /
          Real.log (engelsmaMaynardRadius alpha N) ^ 2 *
        normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve alpha N m)
      atTop (nhds 0) := by
    simpa using hLoss.mul hBox
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) ?_ hupper
  have hLogRadius := tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hRadius : ∀ᶠ N : ℕ in atTop,
      1 < engelsmaMaynardRadius alpha N := by
    filter_upwards [hLogRadius.eventually (eventually_gt_atTop 0)] with N hLN
    exact_mod_cast
      ((Real.log_pos_iff (Nat.cast_nonneg _)).mp hLN)
  filter_upwards [hRadius] with N hRN
  let R := engelsmaMaynardRadius alpha N
  let D := tripleLogCutoff (N - 1)
  let S := preSieveSingularSeries D
  let L := Real.log R
  let k := ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card
  let P := ∏ _ ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m,
    maynardS2OuterSquarefreeMean (primorial D) R
  let B := engelsmaS2EndpointSquareReplacementLoss alpha N
  have hL : 0 < L := Real.log_pos (by simpa [R] using hRN)
  have hS : 0 < S := preSieveSingularSeries_pos D
  have hden : 0 < (S * L) ^ k * L ^ 2 := by positivity
  have hdiff :=
    abs_engelsmaS2CoordinateFiberGoodOuterMoment_sub_complement_le_faceBox
      (D := D) m (by simpa [R] using hRN)
  have hdiff' :
      |engelsmaS2CoordinateFiberGoodOuterMoment R D m -
        engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m| ≤
        B * P := by
    simpa [B, P, R, D, engelsmaS2EndpointSquareReplacementLoss] using hdiff
  have hdiv :
      |engelsmaS2CoordinateFiberGoodOuterMoment R D m / ((S * L) ^ k * L ^ 2) -
        engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m /
          ((S * L) ^ k * L ^ 2)| ≤
        (B / L ^ 2) * (P / (S * L) ^ k) := by
    rw [show engelsmaS2CoordinateFiberGoodOuterMoment R D m /
            ((S * L) ^ k * L ^ 2) -
          engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m /
            ((S * L) ^ k * L ^ 2) =
        (engelsmaS2CoordinateFiberGoodOuterMoment R D m -
          engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m) /
            ((S * L) ^ k * L ^ 2) by ring]
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    calc
      |engelsmaS2CoordinateFiberGoodOuterMoment R D m -
          engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m| ≤
          B * P := hdiff'
      _ = ((B / L ^ 2) * (P / (S * L) ^ k)) *
          ((S * L) ^ k * L ^ 2) := by
        field_simp [hL.ne', hS.ne']
  have hboxEq :
      normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve alpha N m =
        P / (S * L) ^ k := by
    unfold normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve
      engelsmaS2OuterCoordinateOneFaceBoxMass
    unfold engelsmaMaynardModulus
    rw [maynardS2OuterCoordinateOneFaceBox_sum_eq_erase_prod_mean]
  rw [hboxEq]
  simpa [normalizedEngelsmaS2CoordinateFiberGoodOuterMoment,
    normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment,
    R, D, S, L, k, B] using hdiv

end BoundedGaps.Maynard
