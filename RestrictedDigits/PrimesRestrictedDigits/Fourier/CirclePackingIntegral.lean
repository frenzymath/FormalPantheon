import PrimesRestrictedDigits.Fourier.CirclePacking
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrating finite circle-ball overlap

This module converts the pointwise overlap count from `CirclePacking` into the finite integral
inequality.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

theorem sum_integral_closedBall_le_of_card
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (center : ι -> UnitAddCircle) (g : UnitAddCircle -> Real)
    (hg : Continuous g) (hg0 : ∀ z, 0 <= g z)
    (r M : Real)
    (hoverlap : ∀ z,
      ((indicesInClosedBall s center z r).card : Real) <= M) :
    (∑ i ∈ s, ∫ z in Metric.closedBall (center i) r, g z) <=
      M * ∫ z : UnitAddCircle, g z := by
  classical
  have hgIntegrable : MeasureTheory.Integrable g MeasureTheory.volume :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  let indicated (i : ι) : UnitAddCircle -> Real :=
    (Metric.closedBall (center i) r).indicator g
  have hindicatedIntegrable (i : ι) :
      MeasureTheory.Integrable (indicated i) MeasureTheory.volume :=
    hgIntegrable.indicator measurableSet_closedBall
  have hsumIntegrable :
      MeasureTheory.Integrable (fun z => ∑ i ∈ s, indicated i z)
        MeasureTheory.volume :=
    MeasureTheory.integrable_finsetSum s fun i _ => hindicatedIntegrable i
  have hrightIntegrable :
      MeasureTheory.Integrable (fun z => M * g z) MeasureTheory.volume :=
    hgIntegrable.const_mul M
  have hpoint (z : UnitAddCircle) :
      (∑ i ∈ s, indicated i z) =
        (indicesInClosedBall s center z r).card * g z := by
    rw [show
      (indicesInClosedBall s center z r).card * g z =
        ∑ i ∈ indicesInClosedBall s center z r, g z by
          simp only [Finset.sum_const, nsmul_eq_mul]]
    simp only [indicesInClosedBall, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hcenter : center i ∈ Metric.closedBall z r
    · have hz : z ∈ Metric.closedBall (center i) r := by
        simpa only [Metric.mem_closedBall, dist_comm] using hcenter
      simp [indicated, hz, hcenter]
    · have hz : z ∉ Metric.closedBall (center i) r := by
        simpa only [Metric.mem_closedBall, dist_comm] using hcenter
      simp [indicated, hz, hcenter]
  calc
    (∑ i ∈ s, ∫ z in Metric.closedBall (center i) r, g z) =
        ∑ i ∈ s, ∫ z : UnitAddCircle, indicated i z := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← MeasureTheory.integral_indicator measurableSet_closedBall]
    _ = ∫ z : UnitAddCircle, ∑ i ∈ s, indicated i z := by
      rw [MeasureTheory.integral_finsetSum s]
      exact fun i _ => hindicatedIntegrable i
    _ <= ∫ z : UnitAddCircle, M * g z := by
      apply MeasureTheory.integral_mono_ae hsumIntegrable hrightIntegrable
      exact Filter.Eventually.of_forall fun z => by
        change (∑ i ∈ s, indicated i z) <= M * g z
        rw [hpoint]
        exact mul_le_mul_of_nonneg_right (hoverlap z) (hg0 z)
    _ = M * ∫ z : UnitAddCircle, g z := by
      rw [MeasureTheory.integral_const_mul]

end

end PrimesRestrictedDigits
