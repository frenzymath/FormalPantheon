import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
/-! # StandardSimplexVolumeD904 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

private def standardSimplex3Base : Set (Real × Real) :=
  closedIccFiberCell (Icc (0 : Real) 1)
    (fun _ : Real => 0) (fun x : Real => 1 - x)

def standardSimplex3 : Set ((Real × Real) × Real) :=
  closedIccFiberCell standardSimplex3Base
    (fun _ : Real × Real => 0)
    (fun x : Real × Real => 1 - x.1 - x.2)

private theorem standardSimplex3Base_measurable : MeasurableSet standardSimplex3Base := by
  apply measurableSet_closedIccFiberCell
  · exact measurableSet_Icc
  · fun_prop
  · fun_prop

private theorem standardSimplex3Base_ordered : ∀ x ∈ Icc (0 : Real) 1, (0 : Real) ≤ 1 - x := by
  intro x hx
  linarith [hx.2]

private theorem standardSimplex3_measurable : MeasurableSet standardSimplex3 := by
  apply measurableSet_closedIccFiberCell standardSimplex3Base_measurable
  · fun_prop
  · fun_prop

private theorem standardSimplex3_subset_box :
    standardSimplex3 ⊆ ((Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1) ×ˢ
      Icc (0 : Real) 1) := by
  intro z hz
  change z.1 ∈ standardSimplex3Base ∧ z.2 ∈ Icc (0 : Real) (1 - z.1.1 - z.1.2) at hz
  have hbase := hz.1
  have hfiber := hz.2
  change z.1.1 ∈ Icc (0 : Real) 1 ∧
      z.1.2 ∈ Icc (0 : Real) (1 - z.1.1) at hbase
  change ((z.1.1 ∈ Icc (0 : Real) 1 ∧ z.1.2 ∈ Icc (0 : Real) 1) ∧
      z.2 ∈ Icc (0 : Real) 1)
  refine ⟨⟨hbase.1, ?_⟩, ?_⟩
  · exact ⟨hbase.2.1, by linarith [hbase.2.2, hbase.1.1]⟩
  · exact ⟨hfiber.1, by linarith [hfiber.2, hbase.1.1, hbase.2.1]⟩

private theorem standardSimplex3_ordered : ∀ x ∈ standardSimplex3Base,
    (0 : Real) ≤ 1 - x.1 - x.2 := by
  intro x hx
  exact sub_nonneg.mpr (by linarith [hx.2.2])

private theorem standardSimplex3Base_integrable_one :
    IntegrableOn (fun _ : Real => (1 : Real)) (Icc 0 1) volume := by
  exact continuousOn_const.integrableOn_Icc

private theorem standardSimplex3_integrable_one :
    IntegrableOn (fun _ : (Real × Real) × Real => (1 : Real)) standardSimplex3
      (volume.prod volume) := by
  exact integrableOn_const (measure_ne_top_of_subset standardSimplex3_subset_box
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).measure_ne_top)

private theorem standardSimplex3Base_integrable_affine :
    IntegrableOn (fun x : Real × Real => 1 - x.1 - x.2) standardSimplex3Base volume := by
  have hcont : ContinuousOn (fun x : Real × Real => 1 - x.1 - x.2)
      (Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1) := by
    fun_prop
  apply hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) |>.mono_set
  intro x hx
  change x.1 ∈ Icc (0 : Real) 1 ∧ x.2 ∈ Icc (0 : Real) (1 - x.1) at hx
  exact ⟨hx.1, ⟨hx.2.1, by linarith [hx.2.2, hx.1.1]⟩⟩

private theorem standardSimplex3Base_subset_box :
    standardSimplex3Base ⊆ Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1 := by
  intro x hx
  change x.1 ∈ Icc (0 : Real) 1 ∧ x.2 ∈ Icc (0 : Real) (1 - x.1) at hx
  exact ⟨hx.1, ⟨hx.2.1, by linarith [hx.2.2, hx.1.1]⟩⟩

private theorem standardSimplex3Base_integrable_one_pair :
    IntegrableOn (fun _ : Real × Real => (1 : Real)) standardSimplex3Base volume := by
  apply integrableOn_const
  · exact measure_ne_top_of_subset standardSimplex3Base_subset_box
      ((isCompact_Icc.prod isCompact_Icc).measure_ne_top)
  · norm_num

private theorem standardSimplex3Base_integrable_affine_prod :
    IntegrableOn (fun x : Real × Real => 1 - x.1 - x.2) standardSimplex3Base
      (volume.prod volume) := by
  simpa only [← Measure.volume_eq_prod] using standardSimplex3Base_integrable_affine

private theorem standardSimplex3Base_integrable_one_pair_prod :
    IntegrableOn (fun _ : Real × Real => (1 : Real)) standardSimplex3Base
      (volume.prod volume) := by
  simpa only [← Measure.volume_eq_prod] using standardSimplex3Base_integrable_one_pair

private theorem inner_standardSimplex3 (x : Real × Real) :
    (∫ _ in (0 : Real)..(1 - x.1 - x.2), (1 : Real)) = 1 - x.1 - x.2 := by
  simp

private theorem triangle_inner_standardSimplex3 (x : Real) :
    (∫ y in (0 : Real)..(1 - x), (1 - x - y)) = (1 - x)^2 / 2 := by
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const, integral_id]
    ring
  · exact intervalIntegrable_const
  · exact continuousOn_id.intervalIntegrable

private theorem triangle_outer_standardSimplex3 :
    (∫ x in (0 : Real)..1, (1 - x)^2 / 2) = (1 : Real) / 6 := by
  have hconst : IntervalIntegrable (fun _ : Real => (1 : Real)) volume 0 1 :=
    intervalIntegrable_const
  have hid : IntervalIntegrable (fun x : Real => x) volume 0 1 :=
    continuousOn_id.intervalIntegrable
  have hsq : IntervalIntegrable (fun x : Real => x ^ 2) volume 0 1 :=
    (continuousOn_id.pow 2).intervalIntegrable
  have htwo : IntervalIntegrable (fun x : Real => 2 * x) volume 0 1 := by
    exact (continuousOn_const.mul continuousOn_id).intervalIntegrable
  have hlin : IntervalIntegrable (fun x : Real => 1 - 2 * x) volume 0 1 :=
    hconst.sub htwo
  calc
    (∫ x in (0 : Real)..1, (1 - x)^2 / 2) =
        (1 / 2 : Real) * (∫ x in (0 : Real)..1, 1 - 2 * x + x^2) := by
      rw [show (fun x : Real => (1 - x)^2 / 2) =
        (fun x : Real => (1 / 2 : Real) * (1 - 2 * x + x^2)) by
          funext x; ring, intervalIntegral.integral_const_mul]
    _ = (1 / 2 : Real) *
        ((∫ x in (0 : Real)..1, 1 - 2 * x) +
          (∫ x in (0 : Real)..1, x^2)) := by
      rw [intervalIntegral.integral_add hlin hsq]
    _ = (1 : Real) / 6 := by
      rw [intervalIntegral.integral_sub hconst htwo,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_id, integral_pow]
      norm_num

theorem standardSimplex3_setIntegral_one :
    (∫ _z in standardSimplex3, (1 : Real) ∂(volume.prod volume)) = (1 : Real) / 6 := by
  change (∫ z in closedIccFiberCell standardSimplex3Base
      (fun _ : Real × Real => 0)
      (fun x : Real × Real => 1 - x.1 - x.2),
      (1 : Real) ∂(volume.prod volume)) = (1 : Real) / 6
  rw [setIntegral_closedIccFiberCell_eq_iterated
    standardSimplex3Base (fun _ : Real × Real => 0)
    (fun x : Real × Real => 1 - x.1 - x.2)
    (fun z : (Real × Real) × Real => (1 : Real))
    standardSimplex3Base_measurable (by fun_prop) (by fun_prop)
    standardSimplex3_ordered standardSimplex3_integrable_one]
  have hbase :
      (∫ x in standardSimplex3Base,
        (∫ t in (0 : Real)..(1 - x.1 - x.2), (1 : Real)) ∂volume) =
      (∫ x in standardSimplex3Base, 1 - x.1 - x.2 ∂volume) := by
    apply setIntegral_congr_fun standardSimplex3Base_measurable
    intro x hx
    exact inner_standardSimplex3 x
  rw [hbase]
  rw [Measure.volume_eq_prod]
  change (∫ x in closedIccFiberCell (Icc (0 : Real) 1)
      (fun _ : Real => 0) (fun x : Real => 1 - x),
      (1 - x.1 - x.2) ∂(volume.prod volume)) = (1 : Real) / 6
  rw [setIntegral_closedIccFiberCell_eq_iterated
    (Icc (0 : Real) 1) (fun _ : Real => 0) (fun x : Real => 1 - x)
    (fun x : Real × Real => 1 - x.1 - x.2)
    measurableSet_Icc (by fun_prop) (by fun_prop)
    standardSimplex3Base_ordered]
  · apply congrArg (fun q : Real => q) ?_
    change (∫ x in Icc (0 : Real) 1,
      (∫ t in (0 : Real)..(1 - x), 1 - x - t)) = (1 : Real) / 6
    calc
      (∫ x in Icc (0 : Real) 1,
          (∫ t in (0 : Real)..(1 - x), 1 - x - t)) =
          ∫ x in Icc (0 : Real) 1, (1 - x)^2 / 2 := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        exact triangle_inner_standardSimplex3 x
      _ = (1 : Real) / 6 := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
        rw [← intervalIntegral.integral_of_le (by norm_num)]
        exact triangle_outer_standardSimplex3
  · exact standardSimplex3Base_integrable_affine_prod

private theorem standardSimplex3_volume_real :
    volume.real standardSimplex3 = (1 : Real) / 6 := by
  rw [Measure.volume_eq_prod]
  rw [← setIntegral_one_eq_measureReal]
  exact standardSimplex3_setIntegral_one

theorem standardSimplex3_volume :
    (volume.prod volume) standardSimplex3 = ENNReal.ofReal ((1 : Real) / 6) := by
  rw [← ofReal_setIntegral_one_of_measure_ne_top
    (measure_ne_top_of_subset standardSimplex3_subset_box
      ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).measure_ne_top)]
  rw [standardSimplex3_setIntegral_one]

end PrimesRestrictedDigits
