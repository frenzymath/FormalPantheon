import PrimesRestrictedDigits.Fourier.CirclePacking
import Mathlib.MeasureTheory.Measure.Real

/-!
# Cardinality bounds for separated circle families

These finite packing consequences are the geometric input to the dense branch.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

theorem card_le_two_mul_of_pairwise_circleDist
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (base : ι -> UnitAddCircle) {L : Real} (hL : 1 <= L)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist (base i) (base j)) :
    (s.card : Real) <= 2 * L := by
  classical
  let r : Real := 1 / (4 * L)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hr0 : 0 <= r := by
    dsimp [r]
    positivity
  have hrhalf : r < 1 / 2 := by
    dsimp [r]
    apply (div_lt_div_iff₀ (by positivity : (0 : Real) < 4 * L)
      (by norm_num : (0 : Real) < 2)).mpr
    nlinarith
  have hdisjoint : (s : Set ι).PairwiseDisjoint
      (fun i => Metric.ball (base i) r) := by
    intro i hi j hj hij
    apply Metric.ball_disjoint_ball
    calc
      r + r = 1 / (2 * L) := by
        dsimp [r]
        field_simp
        ring
      _ <= 1 / L := by
        rw [div_le_div_iff₀ (by positivity : (0 : Real) < 2 * L) hL0]
        nlinarith
      _ <= dist (base i) (base j) := hseparated i hi j hj hij
  have hball (i : ι) :
      MeasureTheory.volume.real (Metric.ball (base i) r) = 2 * r := by
    have hae := AddCircle.closedBall_ae_eq_ball
      (x := base i) (ε := r)
    rw [MeasureTheory.Measure.real, ← MeasureTheory.measure_congr hae]
    rw [AddCircle.volume_closedBall]
    rw [min_eq_right (by linarith : 2 * r <= (1 : Real))]
    rw [ENNReal.toReal_ofReal (by positivity : 0 <= 2 * r)]
  have hsum :
      (s.card : Real) * (2 * r) <= 1 := by
    have hmeasure := MeasureTheory.sum_measureReal_le_measureReal_univ
      (μ := MeasureTheory.volume)
      (fun i hi => measurableSet_ball)
      hdisjoint
    rw [show (∑ i ∈ s,
        MeasureTheory.volume.real (Metric.ball (base i) r)) =
        (s.card : Real) * (2 * r) by
          simp only [hball, Finset.sum_const, nsmul_eq_mul]] at hmeasure
    have huniv : MeasureTheory.volume.real (Set.univ : Set UnitAddCircle) = 1 := by
      rw [MeasureTheory.Measure.real, AddCircle.measure_univ]
      norm_num
    simpa only [huniv] using hmeasure
  dsimp [r] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (show 0 <= 2 * L by positivity)
  field_simp at hscaled
  nlinarith

/-- A separated family has only `4*(1+delta*L)` points in a closed circle
ball of radius `delta`. This is obtained by filtering first and applying the
existing repaired perturbation-packing theorem with a constant center. -/
theorem card_filter_closedBall_le_of_pairwise_circleDist
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (base : ι -> UnitAddCircle) {L delta : Real}
    (hL : 1 <= L) (hdelta : 0 <= delta)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist (base i) (base j))
    (z : UnitAddCircle) :
    ((indicesInClosedBall s base z delta).card : Real) <=
      4 * (1 + delta * L) := by
  classical
  let selected := indicesInClosedBall s base z delta
  let center : ι -> UnitAddCircle := fun _ => z
  have hperturbed (i : ι) (hi : i ∈ selected) :
      dist (base i) (center i) <= delta := by
    have hi' := (mem_indicesInClosedBall_iff.mp hi).2
    exact Metric.mem_closedBall.mp hi'
  have hsample := card_filter_mem_closedBall_le_of_pairwise_dist
    selected base center hL hdelta
    (fun i hi j hj hij => hseparated i
      (mem_indicesInClosedBall_iff.mp hi).1 j
      (mem_indicesInClosedBall_iff.mp hj).1 hij)
    hperturbed z
  have hsame :
      indicesInClosedBall selected center z (1 / (4 * L)) = selected := by
    ext i
    simp only [mem_indicesInClosedBall_iff, selected, center]
    constructor
    · intro h
      exact h.1
    · intro h
      refine ⟨h, ?_⟩
      rw [Metric.mem_closedBall]
      simp only [dist_self]
      positivity
  rw [hsame] at hsample
  exact hsample

end

end PrimesRestrictedDigits
