import PrimesRestrictedDigits.Fourier.CirclePacking
import PrimesRestrictedDigits.Fourier.CirclePackingIntegral
import PrimesRestrictedDigits.Fourier.ClosedWindowMaximum
import PrimesRestrictedDigits.Fourier.PeriodicLocalSmoothing
import PrimesRestrictedDigits.Fourier.PeriodicCircleIntegral

/-!
# Two-scale separated sampling on the unit circle

The packing scale for the original points and the averaging scale for the perturbed maxima are
kept independent. This is the circular replacement for the coloring step in the repaired proof
of Lemma 10.7.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- A `1 / L`-separated family, sampled in perturbation windows and averaged
at the independent scale `R`, satisfies the two-scale circle bound. -/
theorem sum_closedWindowMaximum_le_of_pairwise_circleDist_twoScale
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f envelope : Real -> Real}
    (hf : Continuous f) (henvelope : Continuous envelope)
    (hf0 : ∀ x, 0 <= f x) (henvelope0 : ∀ x, 0 <= envelope x)
    (hfPeriod : Function.Periodic f 1)
    (henvelopePeriod : Function.Periodic envelope 1)
    (hvariation : ∀ {u v : Real}, u <= v ->
      |f v - f u| <= ∫ x in u..v, envelope x)
    (base : ι -> Real) {L R delta : Real}
    (hL : 1 <= L) (hR : 1 <= R) (hdelta : 0 <= delta)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist ((base i : Real) : UnitAddCircle)
        ((base j : Real) : UnitAddCircle))
    (beta : Real) :
    (∑ i ∈ s, closedWindowMaximum f delta (base i + beta)) <=
      (1 + 4 * delta * L + L / R) *
        (2 * R * (∫ x in (0 : Real)..1, f x) +
          ∫ x in (0 : Real)..1, envelope x) := by
  classical
  let eta (i : ι) : Real :=
    Classical.choose (exists_closedWindowMaximum_eq hf hdelta (base i + beta))
  have hetaMem (i : ι) : eta i ∈ Set.Icc (-delta) delta :=
    (Classical.choose_spec
      (exists_closedWindowMaximum_eq hf hdelta (base i + beta))).1
  have hetaMax (i : ι) :
      closedWindowMaximum f delta (base i + beta) =
        f (base i + beta + eta i) :=
    (Classical.choose_spec
      (exists_closedWindowMaximum_eq hf hdelta (base i + beta))).2
  let shiftedBase (i : ι) : UnitAddCircle := (base i + beta : Real)
  let center (i : ι) : UnitAddCircle :=
    (base i + beta + eta i : Real)
  have hshiftedSeparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist (shiftedBase i) (shiftedBase j) := by
    intro i hi j hj hij
    have htranslate := dist_add_right
      ((base i : Real) : UnitAddCircle)
      ((base j : Real) : UnitAddCircle) (beta : UnitAddCircle)
    rw [show shiftedBase i =
        ((base i : Real) : UnitAddCircle) + (beta : UnitAddCircle) by
          simp [shiftedBase]]
    rw [show shiftedBase j =
        ((base j : Real) : UnitAddCircle) + (beta : UnitAddCircle) by
          simp [shiftedBase]]
    rw [htranslate]
    exact hseparated i hi j hj hij
  have hperturbed : ∀ i ∈ s,
      dist (shiftedBase i) (center i) <= delta := by
    intro i hi
    have hquotient :
        ‖((eta i : Real) : UnitAddCircle)‖ <= ‖eta i‖ :=
      QuotientAddGroup.norm_mk_le_norm
    have hetaAbs : |eta i| <= delta := abs_le.mpr (hetaMem i)
    calc
      dist (shiftedBase i) (center i) =
          ‖((eta i : Real) : UnitAddCircle)‖ := by
        rw [dist_eq_norm]
        change
          ‖(((base i + beta) - (base i + beta + eta i) : Real) :
            UnitAddCircle)‖ = _
        rw [show (base i + beta) - (base i + beta + eta i) = -eta i by ring]
        change ‖-((eta i : Real) : UnitAddCircle)‖ = _
        rw [norm_neg]
      _ <= ‖eta i‖ := hquotient
      _ = |eta i| := Real.norm_eq_abs _
      _ <= delta := hetaAbs
  let liftF : UnitAddCircle -> Real := hfPeriod.lift
  let liftEnvelope : UnitAddCircle -> Real := henvelopePeriod.lift
  have hliftF : Continuous liftF := periodicLift_continuous hf hfPeriod
  have hliftEnvelope : Continuous liftEnvelope :=
    periodicLift_continuous henvelope henvelopePeriod
  have hliftF0 (z : UnitAddCircle) : 0 <= liftF z := by
    obtain ⟨z⟩ := z
    change 0 <= hfPeriod.lift ((z : Real) : UnitAddCircle)
    rw [hfPeriod.lift_coe]
    exact hf0 z
  have hliftEnvelope0 (z : UnitAddCircle) : 0 <= liftEnvelope z := by
    obtain ⟨z⟩ := z
    change 0 <= henvelopePeriod.lift ((z : Real) : UnitAddCircle)
    rw [henvelopePeriod.lift_coe]
    exact henvelope0 z
  let radius : Real := 1 / (4 * R)
  let overlap : Real := 1 + 4 * delta * L + L / R
  have hoverlap (z : UnitAddCircle) :
      ((indicesInClosedBall s center z radius).card : Real) <= overlap := by
    dsimp [radius, overlap]
    convert card_filter_mem_closedBall_le_of_pairwise_dist_at_scale s
      shiftedBase center hL hR hdelta hshiftedSeparated hperturbed z using 1;
      ring
  have hsumF :
      (∑ i ∈ s, ∫ z in Metric.closedBall (center i) radius, liftF z) <=
        overlap * ∫ z : UnitAddCircle, liftF z :=
    sum_integral_closedBall_le_of_card s center liftF hliftF hliftF0
      radius overlap hoverlap
  have hsumEnvelope :
      (∑ i ∈ s,
        ∫ z in Metric.closedBall (center i) radius, liftEnvelope z) <=
        overlap * ∫ z : UnitAddCircle, liftEnvelope z :=
    sum_integral_closedBall_le_of_card s center liftEnvelope hliftEnvelope
      hliftEnvelope0 radius overlap hoverlap
  have hlocal (i : ι) :
      f (base i + beta + eta i) <=
        2 * R * (∫ z in Metric.closedBall (center i) radius, liftF z) +
          ∫ z in Metric.closedBall (center i) radius, liftEnvelope z := by
    simpa only [center, radius, liftF, liftEnvelope] using
      le_periodicLift_closedBall_average_add_envelope hf henvelope
        hfPeriod henvelopePeriod henvelope0 hvariation hR
          (base i + beta + eta i)
  have hoverlap0 : 0 <= overlap := by
    dsimp [overlap]
    positivity
  have hperiodF :
      (∫ z : UnitAddCircle, liftF z) = ∫ x in (0 : Real)..1, f x := by
    dsimp [liftF]
    simpa using (intervalIntegral_eq_integral_periodicLift hfPeriod 0).symm
  have hperiodEnvelope :
      (∫ z : UnitAddCircle, liftEnvelope z) =
        ∫ x in (0 : Real)..1, envelope x := by
    dsimp [liftEnvelope]
    simpa using
      (intervalIntegral_eq_integral_periodicLift henvelopePeriod 0).symm
  calc
    (∑ i ∈ s, closedWindowMaximum f delta (base i + beta)) =
        ∑ i ∈ s, f (base i + beta + eta i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hetaMax i
    _ <= ∑ i ∈ s,
        (2 * R * (∫ z in Metric.closedBall (center i) radius, liftF z) +
          ∫ z in Metric.closedBall (center i) radius, liftEnvelope z) := by
      exact Finset.sum_le_sum fun i hi => hlocal i
    _ = 2 * R *
          (∑ i ∈ s, ∫ z in Metric.closedBall (center i) radius, liftF z) +
        ∑ i ∈ s,
          ∫ z in Metric.closedBall (center i) radius, liftEnvelope z := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ <= 2 * R *
          (overlap * ∫ z : UnitAddCircle, liftF z) +
        overlap * ∫ z : UnitAddCircle, liftEnvelope z := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hsumF (by positivity)) hsumEnvelope
    _ = overlap *
        (2 * R * (∫ z : UnitAddCircle, liftF z) +
          ∫ z : UnitAddCircle, liftEnvelope z) := by ring
    _ = overlap *
        (2 * R * (∫ x in (0 : Real)..1, f x) +
          ∫ x in (0 : Real)..1, envelope x) := by
      rw [hperiodF, hperiodEnvelope]
    _ = _ := by rfl

end

end PrimesRestrictedDigits
