import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9Analytic
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # SectionSixFirstHighCentralSmallQuadrupleI9MiddleVolume -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def i9mv_fT (z : ((Real × Real) × Real)) : Real :=
  ∫ _ in sectionSixFirstHighCentralSmallI9T z.1.1 z.1.2 z.2..z.2, (1 : Real)

private def i9mv_fW (z : Real × Real) : Real :=
  ∫ w in sectionSixFirstHighCentralSmallI9W3 z.1 z.2..z.2, i9mv_fT (z, w)

private def i9mv_fV (u : Real) : Real :=
  ∫ v in sectionSixFirstHighCentralSmallI9W u..
    sectionSixFirstHighCentralSmallI9VUpper u, i9mv_fW (u, v)

private theorem i9mv_u_measurable :
    MeasurableSet sectionSixFirstHighCentralSmallI9USet := by
  unfold sectionSixFirstHighCentralSmallI9USet
  exact measurableSet_Icc

private theorem i9mv_uv_measurable :
    MeasurableSet sectionSixFirstHighCentralSmallI9UVSet := by
  unfold sectionSixFirstHighCentralSmallI9UVSet
  apply measurableSet_closedIccFiberCell i9mv_u_measurable
  · change Measurable (fun u : Real => (1 - u) / 6)
    fun_prop
  · change Measurable (fun u : Real => (16 / 25 - u) / 2)
    fun_prop

private theorem i9mv_uvw_measurable :
    MeasurableSet sectionSixFirstHighCentralSmallI9UVWSet := by
  unfold sectionSixFirstHighCentralSmallI9UVWSet
  apply measurableSet_closedIccFiberCell i9mv_uv_measurable
  · change Measurable (fun z : Real × Real => (1 - z.1 - z.2) / 5)
    fun_prop
  · fun_prop

private theorem i9mv_t_measurable :
    Measurable (fun z : ((Real × Real) × Real) =>
      sectionSixFirstHighCentralSmallI9T z.1.1 z.1.2 z.2) := by
  change Measurable (fun z : ((Real × Real) × Real) =>
    (1 - z.1.1 - z.1.2 - z.2) / 4)
  fun_prop

private theorem i9mv_w_measurable :
    Measurable sectionSixFirstHighCentralSmallI9W := by
  change Measurable (fun u : Real => (1 - u) / 6)
  fun_prop

private theorem i9mv_vupper_measurable :
    Measurable (fun u : Real => sectionSixFirstHighCentralSmallI9VUpper u) := by
  change Measurable (fun u : Real => (16 / 25 - u) / 2)
  fun_prop

private theorem i9mv_continuous_variable_interval {X : Type*} [TopologicalSpace X]
    (f : X → Real → Real) (a b : X → Real)
    (hf : Continuous f.uncurry) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => ∫ t in a x..b x, f x t) := by
  have hparam : Continuous (fun x : X =>
      ∫ y in (0 : Real)..1, f x (a x + (b x - a x) * y)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop
  have heq : (fun x => ∫ t in a x..b x, f x t) =
      (fun x => (b x - a x) *
        ∫ y in (0 : Real)..1, f x (a x + (b x - a x) * y)) := by
    funext x
    have h := (intervalIntegral.smul_integral_comp_add_mul (a := (0 : Real)) (b := 1)
      (fun t => f x t) (b x - a x) (a x)).symm
    have h0 : a x + (b x - a x) * 0 = a x := by ring
    have h1 : a x + (b x - a x) * 1 = b x := by ring
    rw [h0, h1] at h
    simpa only [smul_eq_mul] using h
  rw [heq]
  fun_prop

private def i9mv_boxUV : Set (Real × Real) :=
  sectionSixFirstHighCentralSmallI9USet ×ˢ Icc (0 : Real) 1

private def i9mv_boxUVW : Set ((Real × Real) × Real) :=
  i9mv_boxUV ×ˢ Icc (0 : Real) 1

private def i9mv_box4 : Set (((Real × Real) × Real) × Real) :=
  i9mv_boxUVW ×ˢ Icc (0 : Real) 1

private theorem i9mv_uv_subset_box :
    sectionSixFirstHighCentralSmallI9UVSet ⊆ i9mv_boxUV := by
  intro z hz
  change z.1 ∈ sectionSixFirstHighCentralSmallI9USet ∧
    z.2 ∈ Icc (sectionSixFirstHighCentralSmallI9W z.1)
      (sectionSixFirstHighCentralSmallI9VUpper z.1) at hz
  rcases hz with ⟨hu, hv⟩
  refine ⟨hu, ?_⟩
  rcases hu with ⟨huL, huU⟩
  rcases hv with ⟨hvL, hvU⟩
  change 0 ≤ z.2 ∧ z.2 ≤ 1
  norm_num [sectionSixFirstHighCentralSmallI9W,
    sectionSixFirstHighCentralSmallI9VUpper,
    sectionSixFirstHighCentralSmallI9CarrierCap,
    sectionSixFirstHighCentralSmallI9Beta, div_eq_mul_inv] at hvL hvU huL huU ⊢
  ring_nf at hvL hvU ⊢
  constructor <;> nlinarith

private theorem i9mv_uvw_subset_box :
    sectionSixFirstHighCentralSmallI9UVWSet ⊆ i9mv_boxUVW := by
  intro z hz
  change z.1 ∈ sectionSixFirstHighCentralSmallI9UVSet ∧
    z.2 ∈ Icc (sectionSixFirstHighCentralSmallI9W3 z.1.1 z.1.2) z.1.2 at hz
  rcases hz with ⟨huv, hw⟩
  have huv' := i9mv_uv_subset_box huv
  refine ⟨huv', ?_⟩
  rcases huv' with ⟨⟨huL, huU⟩, ⟨hvL, hvU⟩⟩
  rcases hw with ⟨hwL, hwU⟩
  have huv0 := huv
  change z.1.1 ∈ sectionSixFirstHighCentralSmallI9USet ∧
    z.1.2 ∈ Icc (sectionSixFirstHighCentralSmallI9W z.1.1)
      (sectionSixFirstHighCentralSmallI9VUpper z.1.1) at huv0
  rcases huv0 with ⟨⟨huL0, huU0⟩, ⟨hvL0, hvU0⟩⟩
  change 0 ≤ z.2 ∧ z.2 ≤ 1
  norm_num [sectionSixFirstHighCentralSmallI9W3,
    sectionSixFirstHighCentralSmallI9Beta, sectionSixFirstHighCentralSmallI9Seam,
    sectionSixFirstHighCentralSmallI9CarrierCap, div_eq_mul_inv] at hwL hwU ⊢
  norm_num [sectionSixFirstHighCentralSmallI9W] at hvL0 huL0 huU0
  norm_num [sectionSixFirstHighCentralSmallI9VUpper,
    sectionSixFirstHighCentralSmallI9CarrierCap, div_eq_mul_inv] at hvU0
  ring_nf at hvU0
  have hzv0 : 0 ≤ z.1.2 := by linarith [hvL0, huU0]
  ring_nf at hwL ⊢
  constructor
  · linarith [hwL, huL0, huU0, hzv0]
  · linarith [hwU, hvU]

private theorem i9mv_nested_subset_box :
    sectionSixFirstHighCentralSmallI9NestedBox ⊆ i9mv_box4 := by
  intro x hx
  have hxm : x ∈ sectionSixFirstHighCentralSmallI9MiddleBox := by
    rw [← sectionSixFirstHighCentralSmallI9_nestedBox_eq_middleBox]
    exact hx
  have hc := sectionSixFirstHighCentralSmallI9_middleBox_coordinate_lower hxm
  rcases hxm with ⟨hu, hvL, hvU, hwL, hwU, htL, htU⟩
  rcases hu with ⟨huL, huU⟩
  have hvOne : x.1.1.2 ≤ 1 := by
    norm_num [sectionSixFirstHighCentralSmallI9VUpper,
      sectionSixFirstHighCentralSmallI9CarrierCap,
      sectionSixFirstHighCentralSmallI9Beta, div_eq_mul_inv] at hvU huL
    ring_nf at hvU huL
    nlinarith
  have hwOne : x.1.2 ≤ 1 := by linarith [hwU, hvOne]
  have htOne : x.2 ≤ 1 := by linarith [htU, hwOne]
  change ((x.1.1.1 ∈ Icc _ _ ∧ x.1.1.2 ∈ Icc (0 : Real) 1) ∧
    x.1.2 ∈ Icc (0 : Real) 1) ∧ x.2 ∈ Icc (0 : Real) 1
  constructor
  · constructor
    · constructor
      · exact ⟨huL, huU⟩
      · exact ⟨by linarith [hc.1], hvOne⟩
    · exact ⟨by linarith [hc.2.1], hwOne⟩
  · exact ⟨by linarith [hc.2.2], htOne⟩

private theorem i9mv_one_integrable :
    IntegrableOn (fun _ : (((Real × Real) × Real) × Real) => (1 : Real))
      sectionSixFirstHighCentralSmallI9NestedBox := by
  exact integrableOn_const (measure_ne_top_of_subset i9mv_nested_subset_box
    (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
      isCompact_Icc).measure_ne_top)

private theorem i9mv_fT_continuous : Continuous i9mv_fT := by
  have heq : i9mv_fT = (fun z : ((Real × Real) × Real) =>
      z.2 - sectionSixFirstHighCentralSmallI9T z.1.1 z.1.2 z.2) := by
    funext z
    simp [i9mv_fT, intervalIntegral.integral_const, smul_eq_mul]
  rw [heq]
  change Continuous (fun z : ((Real × Real) × Real) =>
    z.2 - (1 - z.1.1 - z.1.2 - z.2) / 4)
  fun_prop

private theorem i9mv_fW_continuous : Continuous i9mv_fW := by
  apply i9mv_continuous_variable_interval
  · exact i9mv_fT_continuous.comp (by fun_prop)
  · change Continuous (fun z : Real × Real => (1 - z.1 - z.2) / 5)
    fun_prop
  · fun_prop

private theorem i9mv_fV_continuous : Continuous i9mv_fV := by
  apply i9mv_continuous_variable_interval
  · exact i9mv_fW_continuous.comp (by fun_prop)
  · change Continuous (fun u : Real => (1 - u) / 6)
    fun_prop
  · change Continuous (fun u : Real => (16 / 25 - u) / 2)
    fun_prop

private theorem i9mv_fT_integrable :
    IntegrableOn i9mv_fT sectionSixFirstHighCentralSmallI9UVWSet := by
  exact (ContinuousOn.integrableOn_compact
    (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc))
    i9mv_fT_continuous.continuousOn).mono_set i9mv_uvw_subset_box

private theorem i9mv_fW_integrable :
    IntegrableOn i9mv_fW sectionSixFirstHighCentralSmallI9UVSet := by
  exact (ContinuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc) i9mv_fW_continuous.continuousOn).mono_set
    i9mv_uv_subset_box

private theorem i9mv_fV_integrable :
    IntegrableOn i9mv_fV sectionSixFirstHighCentralSmallI9USet := by
  exact ContinuousOn.integrableOn_compact isCompact_Icc
    i9mv_fV_continuous.continuousOn

private theorem i9mv_fT_nonneg {z : ((Real × Real) × Real)}
    (hz : z ∈ sectionSixFirstHighCentralSmallI9UVWSet) : 0 ≤ i9mv_fT z := by
  rcases hz with ⟨⟨hu, hv⟩, hw⟩
  rcases hu with ⟨huL, huU⟩
  rcases hv with ⟨hvL, hvU⟩
  rcases hw with ⟨hwL, hwU⟩
  simp [i9mv_fT, intervalIntegral.integral_const, smul_eq_mul]
  dsimp [sectionSixFirstHighCentralSmallI9T]
  norm_num [sectionSixFirstHighCentralSmallI9W3,
    sectionSixFirstHighCentralSmallI9VUpper,
    sectionSixFirstHighCentralSmallI9CarrierCap,
    sectionSixFirstHighCentralSmallI9Width,
    sectionSixFirstHighCentralSmallI9Beta] at huL hvU hwL hwU ⊢
  linarith

private theorem i9mv_t_width {z : ((Real × Real) × Real)}
    (hz : z ∈ sectionSixFirstHighCentralSmallI9UVWSet) :
    i9mv_fT z ≤ sectionSixFirstHighCentralSmallI9Width / 4 := by
  rcases hz with ⟨⟨hu, hv⟩, hw⟩
  rcases hu with ⟨huL, huU⟩
  rcases hv with ⟨hvL, hvU⟩
  rcases hw with ⟨hwL, hwU⟩
  simp [i9mv_fT, intervalIntegral.integral_const, smul_eq_mul]
  dsimp [sectionSixFirstHighCentralSmallI9T]
  norm_num [sectionSixFirstHighCentralSmallI9W3,
    sectionSixFirstHighCentralSmallI9VUpper,
    sectionSixFirstHighCentralSmallI9CarrierCap,
    sectionSixFirstHighCentralSmallI9Width,
    sectionSixFirstHighCentralSmallI9Beta] at huL hvU hwL hwU ⊢
  linarith

private theorem i9mv_w_width {u v : Real}
    (hu : u ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam)
    (hv : v ∈ Icc (sectionSixFirstHighCentralSmallI9W u)
      (sectionSixFirstHighCentralSmallI9VUpper u)) :
    v - sectionSixFirstHighCentralSmallI9W3 u v ≤
      sectionSixFirstHighCentralSmallI9Width / 5 := by
  dsimp [sectionSixFirstHighCentralSmallI9W3]
  norm_num [sectionSixFirstHighCentralSmallI9VUpper,
    sectionSixFirstHighCentralSmallI9CarrierCap,
    sectionSixFirstHighCentralSmallI9Beta,
    sectionSixFirstHighCentralSmallI9Width,
    sectionSixFirstHighCentralSmallI9Seam] at hu hv ⊢
  linarith [hu.1, hv.2]

private theorem i9mv_v_width {u : Real}
    (hu : u ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam) :
    sectionSixFirstHighCentralSmallI9VUpper u -
      sectionSixFirstHighCentralSmallI9W u ≤
        sectionSixFirstHighCentralSmallI9Width / 6 := by
  dsimp [sectionSixFirstHighCentralSmallI9VUpper,
    sectionSixFirstHighCentralSmallI9W]
  norm_num [sectionSixFirstHighCentralSmallI9CarrierCap,
    sectionSixFirstHighCentralSmallI9Beta,
    sectionSixFirstHighCentralSmallI9Width,
    sectionSixFirstHighCentralSmallI9Seam] at hu ⊢
  linarith [hu.1]

private theorem i9mv_u_width :
    sectionSixFirstHighCentralSmallI9Seam -
      sectionSixFirstHighCentralSmallI9Beta ≤
        sectionSixFirstHighCentralSmallI9Width / 2 := by
  norm_num [sectionSixFirstHighCentralSmallI9Seam,
    sectionSixFirstHighCentralSmallI9Beta,
    sectionSixFirstHighCentralSmallI9Width]

private theorem i9mv_fW_nonneg {u v : Real}
    (hu : u ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam)
    (hv : v ∈ Icc (sectionSixFirstHighCentralSmallI9W u)
      (sectionSixFirstHighCentralSmallI9VUpper u)) :
    0 ≤ i9mv_fW (u, v) := by
  have hwo : sectionSixFirstHighCentralSmallI9W3 u v ≤ v := by
    dsimp [sectionSixFirstHighCentralSmallI9W3]
    norm_num [sectionSixFirstHighCentralSmallI9W,
      sectionSixFirstHighCentralSmallI9VUpper,
      sectionSixFirstHighCentralSmallI9CarrierCap,
      sectionSixFirstHighCentralSmallI9Beta] at hu hv ⊢
    linarith [hu.1, hv.1]
  apply intervalIntegral.integral_nonneg hwo
  intro w hw
  apply i9mv_fT_nonneg
  exact ⟨⟨hu, hv⟩, hw⟩

private theorem i9mv_fT_le_width {u v w : Real}
    (hu : u ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam)
    (hv : v ∈ Icc (sectionSixFirstHighCentralSmallI9W u)
      (sectionSixFirstHighCentralSmallI9VUpper u))
    (hw : w ∈ Icc (sectionSixFirstHighCentralSmallI9W3 u v) v) :
    i9mv_fT ((u, v), w) ≤ sectionSixFirstHighCentralSmallI9Width / 4 := by
  exact i9mv_t_width ⟨⟨hu, hv⟩, hw⟩

private theorem i9mv_fW_le_width_sq {u v : Real}
    (hu : u ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam)
    (hv : v ∈ Icc (sectionSixFirstHighCentralSmallI9W u)
      (sectionSixFirstHighCentralSmallI9VUpper u)) :
    i9mv_fW (u, v) ≤ sectionSixFirstHighCentralSmallI9Width ^ 2 / (4 * 5) := by
  have hwo : sectionSixFirstHighCentralSmallI9W3 u v ≤ v := by
    dsimp [sectionSixFirstHighCentralSmallI9W3]
    norm_num [sectionSixFirstHighCentralSmallI9W,
      sectionSixFirstHighCentralSmallI9VUpper,
      sectionSixFirstHighCentralSmallI9CarrierCap,
      sectionSixFirstHighCentralSmallI9Beta] at hu hv ⊢
    linarith [hu.1, hv.1]
  have hf : IntervalIntegrable (fun w : Real => i9mv_fT ((u, v), w)) volume
      (sectionSixFirstHighCentralSmallI9W3 u v) v := by
    exact (i9mv_fT_continuous.comp (by fun_prop)).intervalIntegrable _ _
  have hg : IntervalIntegrable
      (fun _ : Real => sectionSixFirstHighCentralSmallI9Width / 4) volume
      (sectionSixFirstHighCentralSmallI9W3 u v) v :=
    continuous_const.intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on hwo hf hg (by
    intro w hw
    exact i9mv_fT_le_width hu hv hw)
  rw [intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  have hmul := mul_le_mul_of_nonneg_right (i9mv_w_width hu hv)
    (by norm_num [sectionSixFirstHighCentralSmallI9Width] :
      0 ≤ sectionSixFirstHighCentralSmallI9Width / 4)
  change (∫ w in sectionSixFirstHighCentralSmallI9W3 u v..v,
      i9mv_fT ((u, v), w)) ≤ _
  nlinarith [hm, hmul]

private theorem i9mv_fV_nonneg {u : Real}
    (hu : u ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam) : 0 ≤ i9mv_fV u := by
  have hvo : sectionSixFirstHighCentralSmallI9W u ≤
      sectionSixFirstHighCentralSmallI9VUpper u := by
    dsimp [sectionSixFirstHighCentralSmallI9W,
      sectionSixFirstHighCentralSmallI9VUpper]
    norm_num [sectionSixFirstHighCentralSmallI9CarrierCap,
      sectionSixFirstHighCentralSmallI9Seam] at hu ⊢
    linarith [hu.2]
  apply intervalIntegral.integral_nonneg hvo
  intro v hv
  exact i9mv_fW_nonneg hu hv

private theorem i9mv_fV_le_width_cube {u : Real}
    (hu : u ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam) :
    i9mv_fV u ≤ sectionSixFirstHighCentralSmallI9Width ^ 3 / (4 * 5 * 6) := by
  have hvo : sectionSixFirstHighCentralSmallI9W u ≤
      sectionSixFirstHighCentralSmallI9VUpper u := by
    dsimp [sectionSixFirstHighCentralSmallI9W,
      sectionSixFirstHighCentralSmallI9VUpper]
    norm_num [sectionSixFirstHighCentralSmallI9CarrierCap,
      sectionSixFirstHighCentralSmallI9Seam] at hu ⊢
    linarith [hu.2]
  have hf : IntervalIntegrable (fun v : Real => i9mv_fW (u, v)) volume
      (sectionSixFirstHighCentralSmallI9W u)
      (sectionSixFirstHighCentralSmallI9VUpper u) := by
    exact (i9mv_fW_continuous.comp (by fun_prop)).intervalIntegrable _ _
  have hg : IntervalIntegrable
      (fun _ : Real => sectionSixFirstHighCentralSmallI9Width ^ 2 / (4 * 5)) volume
      (sectionSixFirstHighCentralSmallI9W u)
      (sectionSixFirstHighCentralSmallI9VUpper u) :=
    continuous_const.intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on hvo hf hg (by
    intro v hv
    exact i9mv_fW_le_width_sq hu hv)
  rw [intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  have hmul := mul_le_mul_of_nonneg_right (i9mv_v_width hu)
    (by positivity : 0 ≤ sectionSixFirstHighCentralSmallI9Width ^ 2 / (4 * 5))
  change (∫ v in sectionSixFirstHighCentralSmallI9W u..
      sectionSixFirstHighCentralSmallI9VUpper u, i9mv_fW (u, v)) ≤ _
  nlinarith [hm, hmul]

private theorem i9mv_fubini :
    volume.real sectionSixFirstHighCentralSmallI9NestedBox =
      ∫ u in sectionSixFirstHighCentralSmallI9Beta..
        sectionSixFirstHighCentralSmallI9Seam,
        ∫ v in sectionSixFirstHighCentralSmallI9W u..
          sectionSixFirstHighCentralSmallI9VUpper u,
          ∫ w in sectionSixFirstHighCentralSmallI9W3 u v..v,
            ∫ _ in sectionSixFirstHighCentralSmallI9T u v w..w, (1 : Real) := by
  rw [← setIntegral_one_eq_measureReal, Measure.volume_eq_prod]
  unfold sectionSixFirstHighCentralSmallI9NestedBox
  rw [setIntegral_closedIccFiberCell_eq_iterated _ _ _ _
    i9mv_uvw_measurable i9mv_t_measurable (by fun_prop)
    (by
      intro z hz
      rcases hz with ⟨huv, hw⟩
      dsimp [sectionSixFirstHighCentralSmallI9T,
        sectionSixFirstHighCentralSmallI9W3] at hw ⊢
      linarith [hw.1]) i9mv_one_integrable]
  change (∫ z in sectionSixFirstHighCentralSmallI9UVWSet, i9mv_fT z) = _
  rw [Measure.volume_eq_prod]
  unfold sectionSixFirstHighCentralSmallI9UVWSet
  rw [setIntegral_closedIccFiberCell_eq_iterated _ _ _ _
    i9mv_uv_measurable
    (by change Measurable (fun z : Real × Real => (1 - z.1 - z.2) / 5); fun_prop)
    (by fun_prop)
    (by
      intro z hz
      rcases hz with ⟨hu, hv⟩
      dsimp [sectionSixFirstHighCentralSmallI9W,
        sectionSixFirstHighCentralSmallI9W3] at hv ⊢
      linarith [hv.1]) i9mv_fT_integrable]
  change (∫ z in sectionSixFirstHighCentralSmallI9UVSet, i9mv_fW z) = _
  rw [Measure.volume_eq_prod]
  unfold sectionSixFirstHighCentralSmallI9UVSet
  rw [setIntegral_closedIccFiberCell_eq_iterated _ _ _ _
    i9mv_u_measurable i9mv_w_measurable i9mv_vupper_measurable
    (by
      intro u hu
      rcases hu with ⟨huL, huU⟩
      norm_num [sectionSixFirstHighCentralSmallI9W,
        sectionSixFirstHighCentralSmallI9VUpper,
        sectionSixFirstHighCentralSmallI9CarrierCap,
        sectionSixFirstHighCentralSmallI9Seam,
        div_eq_mul_inv] at huL huU ⊢
      linarith) i9mv_fW_integrable]
  change (∫ u in Icc sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam, i9mv_fV u) = _
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num [
      sectionSixFirstHighCentralSmallI9Beta,
      sectionSixFirstHighCentralSmallI9Seam])]
  rfl

theorem sectionSixFirstHighCentralSmallI9_middleBox_volume_le :
    volume.real sectionSixFirstHighCentralSmallI9MiddleBox ≤
      sectionSixFirstHighCentralSmallI9Width ^ 4 / 240 := by
  rw [← sectionSixFirstHighCentralSmallI9_nestedBox_eq_middleBox]
  have hvol := i9mv_fubini
  have hvol' : volume.real sectionSixFirstHighCentralSmallI9NestedBox =
      ∫ u in sectionSixFirstHighCentralSmallI9Beta..
        sectionSixFirstHighCentralSmallI9Seam, i9mv_fV u := by
    simpa [i9mv_fV, i9mv_fW, i9mv_fT] using hvol
  rw [hvol']
  have houter : sectionSixFirstHighCentralSmallI9Beta ≤
      sectionSixFirstHighCentralSmallI9Seam := by
    norm_num [sectionSixFirstHighCentralSmallI9Beta,
      sectionSixFirstHighCentralSmallI9Seam]
  have hf : IntervalIntegrable i9mv_fV volume
      sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam :=
    i9mv_fV_continuous.intervalIntegrable _ _
  have hg : IntervalIntegrable
      (fun _ : Real => sectionSixFirstHighCentralSmallI9Width ^ 3 / (4 * 5 * 6)) volume
      sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam := continuous_const.intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on houter hf hg (by
    intro u hu
    exact i9mv_fV_le_width_cube hu)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have hmul := mul_le_mul_of_nonneg_right i9mv_u_width
    (by norm_num [sectionSixFirstHighCentralSmallI9Width] :
      0 ≤ sectionSixFirstHighCentralSmallI9Width ^ 3 / (4 * 5 * 6))
  nlinarith [hmul]

end

end PrimesRestrictedDigits
