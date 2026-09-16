import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite packing on the unit additive circle

This module proves the explicit overlap estimate used in the repaired large-sieve argument.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- Indices whose perturbed center lies in a specified closed circle ball. -/
noncomputable def indicesInClosedBall
    {ι : Type*} (s : Finset ι) (center : ι -> UnitAddCircle)
    (z : UnitAddCircle) (r : Real) : Finset ι := by
  classical
  exact s.filter fun i => center i ∈ Metric.closedBall z r

theorem mem_indicesInClosedBall_iff
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {center : ι -> UnitAddCircle} {z : UnitAddCircle} {r : Real} {i : ι} :
    i ∈ indicesInClosedBall s center z r ↔
      i ∈ s ∧ center i ∈ Metric.closedBall z r := by
  classical
  simp [indicesInClosedBall]

/-- Perturbing a `1 / L`-separated finite family by at most `delta` gives
closed balls of radius `1 / (4 * L)` with overlap at most
`4 * (1 + delta * L)`. -/
theorem card_filter_mem_closedBall_le_of_pairwise_dist
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (base center : ι -> UnitAddCircle) {L delta : Real}
    (hL : 1 <= L) (hdelta : 0 <= delta)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist (base i) (base j))
    (hperturbed : ∀ i ∈ s, dist (base i) (center i) <= delta)
    (z : UnitAddCircle) :
    ((indicesInClosedBall s center z (1 / (4 * L))).card : Real) <=
      4 * (1 + delta * L) := by
  classical
  let r : Real := 1 / (4 * L)
  let selected := indicesInClosedBall s center z r
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hr0 : 0 <= r := by
    dsimp [r]
    positivity
  have hr : r < 1 / 2 := by
    dsimp [r]
    apply (div_lt_div_iff₀ (by positivity : (0 : Real) < 4 * L)
      (by norm_num : (0 : Real) < 2)).mpr
    nlinarith
  have hdisjoint : (↑selected : Set ι).PairwiseDisjoint
      (fun i => Metric.ball (base i) r) := by
    intro i hi j hj hij
    apply Metric.ball_disjoint_ball
    have hi' := (mem_indicesInClosedBall_iff.mp hi).1
    have hj' := (mem_indicesInClosedBall_iff.mp hj).1
    calc
      r + r = 1 / (2 * L) := by
        dsimp [r]
        field_simp; ring
      _ <= 1 / L := by
        rw [div_le_div_iff₀ (by positivity : (0 : Real) < 2 * L) hL0]
        nlinarith
      _ <= dist (base i) (base j) := hseparated i hi' j hj' hij
  have hunionSubset :
      (⋃ i ∈ selected, Metric.ball (base i) r) ⊆
        Metric.closedBall z (delta + 2 * r) := by
    intro w hw
    simp only [Set.mem_iUnion] at hw
    obtain ⟨i, hiSelected, hwi⟩ := hw
    have hiFilter := mem_indicesInClosedBall_iff.mp hiSelected
    have hbaseCenter := hperturbed i hiFilter.1
    have hcenterZ := Metric.mem_closedBall.mp hiFilter.2
    have hwBase := Metric.mem_ball.mp hwi
    rw [Metric.mem_closedBall]
    calc
      dist w z <= dist w (base i) + dist (base i) z := dist_triangle _ _ _
      _ <= dist w (base i) +
          (dist (base i) (center i) + dist (center i) z) := by
        gcongr
        exact dist_triangle _ _ _
      _ <= r + (delta + r) := by gcongr
      _ <= delta + 2 * r := by ring_nf; exact le_rfl
  have hballMeasure (i : ι) :
      MeasureTheory.volume.real (Metric.ball (base i) r) = 2 * r := by
    have hae := AddCircle.closedBall_ae_eq_ball
      (x := base i) (ε := r)
    rw [MeasureTheory.Measure.real, ← MeasureTheory.measure_congr hae]
    rw [AddCircle.volume_closedBall]
    rw [min_eq_right (by linarith : 2 * r <= (1 : Real))]
    rw [ENNReal.toReal_ofReal (by positivity : 0 <= 2 * r)]
  have hunionMeasure :
      MeasureTheory.volume.real (⋃ i ∈ selected, Metric.ball (base i) r) =
        ∑ i ∈ selected,
          MeasureTheory.volume.real (Metric.ball (base i) r) := by
    exact MeasureTheory.measureReal_biUnion_finset hdisjoint
      (fun _ _ => measurableSet_ball)
  have hcontainerMeasure :
      MeasureTheory.volume.real (Metric.closedBall z (delta + 2 * r)) <=
        2 * (delta + 2 * r) := by
    rw [MeasureTheory.Measure.real, AddCircle.volume_closedBall]
    rw [ENNReal.toReal_ofReal]
    · exact min_le_right _ _
    · exact le_min (by norm_num) (mul_nonneg (by norm_num) (by positivity))
  have hmeasureMono :
      MeasureTheory.volume.real (⋃ i ∈ selected, Metric.ball (base i) r) <=
        MeasureTheory.volume.real (Metric.closedBall z (delta + 2 * r)) :=
    MeasureTheory.measureReal_mono hunionSubset (by finiteness)
  have hmeasure :
      (selected.card : Real) * (2 * r) <= 2 * (delta + 2 * r) := by
    calc
      (selected.card : Real) * (2 * r) =
          ∑ i ∈ selected,
            MeasureTheory.volume.real (Metric.ball (base i) r) := by
        simp only [hballMeasure, Finset.sum_const, nsmul_eq_mul]
      _ = MeasureTheory.volume.real
          (⋃ i ∈ selected, Metric.ball (base i) r) := hunionMeasure.symm
      _ <= MeasureTheory.volume.real
          (Metric.closedBall z (delta + 2 * r)) := hmeasureMono
      _ <= 2 * (delta + 2 * r) := hcontainerMeasure
  change (selected.card : Real) <= 4 * (1 + delta * L)
  have hscaled := mul_le_mul_of_nonneg_left hmeasure
    (show 0 <= 2 * L by positivity)
  dsimp [r] at hscaled
  field_simp at hscaled
  nlinarith

/-- Independent-scale overlap bound. The original family is separated at
`1 / L`, while the selected perturbed centers are tested at scale `1 / R`. -/
theorem card_filter_mem_closedBall_le_of_pairwise_dist_at_scale
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (base center : ι -> UnitAddCircle) {L R delta : Real}
    (hL : 1 <= L) (hR : 1 <= R) (hdelta : 0 <= delta)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist (base i) (base j))
    (hperturbed : ∀ i ∈ s, dist (base i) (center i) <= delta)
    (z : UnitAddCircle) :
    ((indicesInClosedBall s center z (1 / (4 * R))).card : Real) <=
      1 + L / R + 4 * delta * L := by
  classical
  let rL : Real := 1 / (4 * L)
  let rR : Real := 1 / (4 * R)
  let selected := indicesInClosedBall s center z rR
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hrL0 : 0 <= rL := by
    dsimp [rL]
    positivity
  have hrL : rL < 1 / 2 := by
    dsimp [rL]
    apply (div_lt_div_iff₀ (by positivity : (0 : Real) < 4 * L)
      (by norm_num : (0 : Real) < 2)).mpr
    nlinarith
  have hdisjoint : (↑selected : Set ι).PairwiseDisjoint
      (fun i => Metric.ball (base i) rL) := by
    intro i hi j hj hij
    apply Metric.ball_disjoint_ball
    have hi' := (mem_indicesInClosedBall_iff.mp hi).1
    have hj' := (mem_indicesInClosedBall_iff.mp hj).1
    calc
      rL + rL = 1 / (2 * L) := by
        dsimp [rL]
        field_simp; ring
      _ <= 1 / L := by
        rw [div_le_div_iff₀ (by positivity : (0 : Real) < 2 * L) hL0]
        nlinarith
      _ <= dist (base i) (base j) := hseparated i hi' j hj' hij
  have hunionSubset :
      (⋃ i ∈ selected, Metric.ball (base i) rL) ⊆
        Metric.closedBall z (delta + rR + rL) := by
    intro w hw
    simp only [Set.mem_iUnion] at hw
    obtain ⟨i, hiSelected, hwi⟩ := hw
    have hiFilter := mem_indicesInClosedBall_iff.mp hiSelected
    have hbaseCenter := hperturbed i hiFilter.1
    have hcenterZ := Metric.mem_closedBall.mp hiFilter.2
    have hwBase := Metric.mem_ball.mp hwi
    rw [Metric.mem_closedBall]
    calc
      dist w z <= dist w (base i) + dist (base i) z := dist_triangle _ _ _
      _ <= dist w (base i) +
          (dist (base i) (center i) + dist (center i) z) := by
        gcongr
        exact dist_triangle _ _ _
      _ <= rL + (delta + rR) := by gcongr
      _ <= delta + rR + rL := by ring_nf; exact le_rfl
  have hballMeasure (i : ι) :
      MeasureTheory.volume.real (Metric.ball (base i) rL) = 2 * rL := by
    have hae := AddCircle.closedBall_ae_eq_ball
      (x := base i) (ε := rL)
    rw [MeasureTheory.Measure.real, ← MeasureTheory.measure_congr hae]
    rw [AddCircle.volume_closedBall]
    rw [min_eq_right (by linarith : 2 * rL <= (1 : Real))]
    rw [ENNReal.toReal_ofReal (by positivity : 0 <= 2 * rL)]
  have hunionMeasure :
      MeasureTheory.volume.real (⋃ i ∈ selected, Metric.ball (base i) rL) =
        ∑ i ∈ selected,
          MeasureTheory.volume.real (Metric.ball (base i) rL) := by
    exact MeasureTheory.measureReal_biUnion_finset hdisjoint
      (fun _ _ => measurableSet_ball)
  have hcontainerMeasure :
      MeasureTheory.volume.real
          (Metric.closedBall z (delta + rR + rL)) <=
        2 * (delta + rR + rL) := by
    rw [MeasureTheory.Measure.real, AddCircle.volume_closedBall]
    rw [ENNReal.toReal_ofReal]
    · exact min_le_right _ _
    · exact le_min (by norm_num)
        (mul_nonneg (by norm_num) (by positivity))
  have hmeasureMono :
      MeasureTheory.volume.real
          (⋃ i ∈ selected, Metric.ball (base i) rL) <=
        MeasureTheory.volume.real
          (Metric.closedBall z (delta + rR + rL)) :=
    MeasureTheory.measureReal_mono hunionSubset (by finiteness)
  have hmeasure :
      (selected.card : Real) * (2 * rL) <=
        2 * (delta + rR + rL) := by
    calc
      (selected.card : Real) * (2 * rL) =
          ∑ i ∈ selected,
            MeasureTheory.volume.real (Metric.ball (base i) rL) := by
        simp only [hballMeasure, Finset.sum_const, nsmul_eq_mul]
      _ = MeasureTheory.volume.real
          (⋃ i ∈ selected, Metric.ball (base i) rL) := hunionMeasure.symm
      _ <= MeasureTheory.volume.real
          (Metric.closedBall z (delta + rR + rL)) := hmeasureMono
      _ <= 2 * (delta + rR + rL) := hcontainerMeasure
  change (selected.card : Real) <= 1 + L / R + 4 * delta * L
  have hscaled := mul_le_mul_of_nonneg_left hmeasure
    (show 0 <= 2 * L by positivity)
  dsimp [rL, rR] at hscaled
  field_simp at hscaled
  apply le_of_mul_le_mul_right _ hR0
  calc
    (selected.card : Real) * R <= L * (4 * delta * R + 1) + R := hscaled
    _ = (1 + L / R + 4 * delta * L) * R := by
      field_simp
      ring

end

end PrimesRestrictedDigits
