import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Periodic real integrals on the unit additive circle

These bridges let the separated-sampling proof for use Haar measure on `UnitAddCircle` while
retaining the source's real interval integrals.
-/

namespace PrimesRestrictedDigits

theorem periodicLift_continuous
    {f : Real -> Real} (hf : Continuous f) (hp : Function.Periodic f 1) :
    Continuous hp.lift := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  convert hf using 1
  ext x
  exact hp.lift_coe x

theorem intervalIntegral_eq_integral_periodicLift
    {f : Real -> Real} (hp : Function.Periodic f 1) (t : Real) :
    (∫ x in t..t + 1, f x) = ∫ z : UnitAddCircle, hp.lift z := by
  simpa only [hp.lift_coe] using
    (AddCircle.intervalIntegral_preimage 1 t hp.lift)

/-- A centered real interval shorter than one period projects, up to null
endpoints, to the corresponding closed ball on `UnitAddCircle`. -/
theorem intervalIntegral_centered_eq_integral_closedBall_periodicLift
    {f : Real -> Real} (_hf : Continuous f) (hp : Function.Periodic f 1)
    (t r : Real) (hr0 : 0 <= r) (hr : r < 1 / 2) :
    (∫ x in t - r..t + r, f x) =
      ∫ z in Metric.closedBall (t : UnitAddCircle) r, hp.lift z := by
  let a : Real := t - 1 / 2
  let g : UnitAddCircle -> Real :=
    (Metric.closedBall (t : UnitAddCircle) r).indicator hp.lift
  have hperiod : Set.Ioc a (a + 1) ⊆ Metric.closedBall t (1 / 2) := by
    intro x hx
    rw [Real.closedBall_eq_Icc]
    rw [Set.mem_Ioc] at hx
    rw [Set.mem_Icc]
    dsimp [a] at hx ⊢
    constructor <;> linarith
  have hpreimage :
      ((fun x : Real => (x : UnitAddCircle)) ⁻¹'
          Metric.closedBall (t : UnitAddCircle) r) ∩ Set.Ioc a (a + 1) =
        Metric.closedBall t r := by
    rw [AddCircle.coe_real_preimage_closedBall_inter_eq]
    · simp only [abs_one, hr, if_true]
      apply Set.inter_eq_left.mpr
      intro x hx
      rw [Real.closedBall_eq_Icc, Set.mem_Icc] at hx
      rw [Set.mem_Ioc]
      dsimp [a] at hx ⊢
      constructor <;> linarith
    · simpa only [abs_one] using hperiod
  have hcircle := AddCircle.integral_preimage 1 a g
  rw [← MeasureTheory.integral_indicator measurableSet_closedBall]
  rw [← hcircle]
  have hreal :
      (∫ x in Set.Ioc a (a + 1), g (x : UnitAddCircle)) =
        ∫ x in Metric.closedBall t r, f x := by
    have hg (x : Real) :
        g (x : UnitAddCircle) =
          (((fun y : Real => (y : UnitAddCircle)) ⁻¹'
            Metric.closedBall (t : UnitAddCircle) r).indicator f x) := by
      by_cases hx : (x : UnitAddCircle) ∈
          Metric.closedBall (t : UnitAddCircle) r <;>
        simp [g, hx, hp.lift_coe]
    simp_rw [hg]
    rw [MeasureTheory.setIntegral_indicator
      (measurableSet_closedBall.preimage AddCircle.measurable_mk')]
    rw [Set.inter_comm, hpreimage]
  rw [hreal]
  rw [Real.closedBall_eq_Icc, intervalIntegral.integral_of_le (by linarith)]
  exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc

end PrimesRestrictedDigits
