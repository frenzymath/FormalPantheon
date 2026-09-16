import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0RefinedProfileD962
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Two-ceiling rational profile for P0

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12). This profile has one baseline and one
positive-part correction, with no numerical cap assumed or asserted.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P0BaselineD963
    (x : (Real × Real) × Real) : Real :=
  (281 / 500) * (x.2 - 16249 / 250000) /
    ((16249 / 250000) * x.1.1 * x.1.2 * x.2 ^ 2)

def sectionSixFirstLowCentralSmallI5P0ExcessD963
    (x : (Real × Real) × Real) : Real :=
  (643 / 500000) * max 0 (17 * x.2 - 4 * (1 - x.1.1 - x.1.2 - x.2)) /
    (x.1.1 * x.1.2 * x.2 ^ 2 * (1 - x.1.1 - x.1.2 - x.2))

def sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963
    (x : (Real × Real) × Real) : Real :=
  sectionSixFirstLowCentralSmallI5P0BaselineD963 x +
    sectionSixFirstLowCentralSmallI5P0ExcessD963 x

theorem sectionSixFirstLowCentralSmallI5P0RefinedBase_iff_fiveWalls_D963
    (x : (Real × Real) × Real) :
    x ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase ↔
      x.1.2 ≤ x.1.1 ∧ (212499 / 500000 : Real) ≤ x.1.1 + x.1.2 ∧
      x.1.1 + 2 * x.1.2 ≤ 16 / 25 ∧
      (16249 / 250000 : Real) ≤ x.2 ∧ x.1.1 + x.2 ≤ 180001 / 500000 := by
  unfold sectionSixFirstLowCentralSmallI5P0RefinedBase
    sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
  simp only [mem_inter_iff, mem_prod, mem_Icc, mem_setOf_eq]
  norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  constructor
  · rintro ⟨hbox, hwv, hvu, huv, hu2v, huw, hvw⟩
    exact ⟨hvu, huv, hu2v, hbox.2.1, huw⟩
  · rintro ⟨hvu, huv, hu2v, hw, huw⟩
    refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨hw, ?_⟩⟩, ?_, hvu,
      huv, hu2v, huw, ?_⟩ <;> linarith

private theorem base_bounds_D963 {x : (Real × Real) × Real}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase) :
    0 < x.1.1 ∧ 0 < x.1.2 ∧ 0 < x.2 ∧
      (16249 / 250000 : Real) ≤ x.2 ∧
      0 < 1 - x.1.1 - x.1.2 - x.2 ∧
      23 / 8 * x.2 ≤ 1 - x.1.1 - x.1.2 - x.2 ∧
      (16249 / 250000 : Real) ≤ 4 * (1 - x.1.1 - x.1.2 - x.2) / 17 := by
  rcases (sectionSixFirstLowCentralSmallI5P0RefinedBase_iff_fiveWalls_D963 x).1 hx with
    ⟨hvu, huv, hu2v, hw, huw⟩
  refine ⟨?_, ?_, ?_, hw, ?_, ?_, ?_⟩ <;> linarith

private theorem buchstab_le_c1_D963 {y : Real} (hy : 15 / 8 ≤ y) :
    buchstabFunction y ≤ 70893 / 125000 := by
  by_cases h3 : 3 ≤ y
  · exact (buchstabFunction_le_tailEnvelope h3).trans (by norm_num)
  by_cases h2 : 2 ≤ y
  · exact buchstabFunction_le_middleEnvelope h2 (le_of_not_ge h3)
  rw [buchstabFunction_eq_inv (by linarith) (le_of_not_ge h2), inv_eq_one_div,
    div_le_iff₀ (by linarith : 0 < y)]
  linarith

private theorem constant_fiber_le_D963 {u v w B l h C : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hl : 0 < l)
    (hlh : l ≤ h) (hB : 2 * h ≤ B)
    (hbound : ∀ t ∈ Icc l h, buchstabFunction ((B - t) / t) ≤ C) :
    (∫ t in l..h, buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) ≤
      C / (u * v * w) * (1 / l - 1 / h) := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  have hf := sectionSixBuchstabFiber_intervalIntegrable hu hv hw hl hlh.le hB
  have hg : IntervalIntegrable
      (fun t : Real => C / (u * v * w * t ^ 2)) volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htpos : 0 < t := hl.trans_le ht.1
    fun_prop (disch := positivity)
  calc
    (∫ t in l..h, buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) ≤
        ∫ t in l..h, C / (u * v * w * t ^ 2) := by
      apply intervalIntegral.integral_mono_on hlh.le hf hg
      intro t ht
      have htpos : 0 < t := hl.trans_le ht.1
      exact div_le_div_of_nonneg_right (hbound t ht) (by positivity)
    _ = _ := sectionSixFiber_integral_constant_inv_sq hu hv hw hl hlh

theorem sectionSixFirstLowCentralSmallI5P0FullFiber_le_twoCeilingProfile_D963
    {x : (Real × Real) × Real}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase) :
    (∫ t in (16249 / 250000 : Real)..x.2,
      sectionSixFirstLowCentralSmallQuadrupleKernel (x, t)) ≤
        sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 x := by
  obtain ⟨hu, hv, hw, hgw, hB, hBw, hGcut⟩ := base_bounds_D963 hx
  let B := 1 - x.1.1 - x.1.2 - x.2
  let m := min x.2 (4 * B / 17)
  have hgm : (16249 / 250000 : Real) ≤ m := le_min hgw hGcut
  have hmw : m ≤ x.2 := min_le_left _ _
  have hmcut : m ≤ 4 * B / 17 := min_le_right _ _
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hgm
  have hBm : 2 * m ≤ B := by dsimp [B]; linarith
  have hBw' : 2 * x.2 ≤ B := by dsimp [B]; linarith
  have hfirst := constant_fiber_le_D963
    (u := x.1.1) (v := x.1.2) (w := x.2) (B := B)
    (l := 16249 / 250000) (h := m) (C := 281 / 500)
    hu hv hw (by norm_num) hgm hBm (by
      intro t ht
      apply buchstabFunction_le_refinedTailEnvelope
      have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
      rw [le_div_iff₀ htpos]
      linarith [ht.2])
  have hsecond := constant_fiber_le_D963
    (u := x.1.1) (v := x.1.2) (w := x.2) (B := B)
    (l := m) (h := x.2) (C := 70893 / 125000)
    hu hv hw hm hmw hBw' (by
      intro t ht
      apply buchstab_le_c1_D963
      have htpos : 0 < t := hm.trans_le ht.1
      rw [le_div_iff₀ htpos]
      dsimp [B]
      linarith [ht.2])
  have hi1 := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw (by norm_num : (0 : Real) < 16249 / 250000) hgm hBm
  have hi2 := sectionSixBuchstabFiber_intervalIntegrable hu hv hw hm hmw hBw'
  have hsum := add_le_add hfirst hsecond
  rw [intervalIntegral.integral_add_adjacent_intervals hi1 hi2] at hsum
  change (∫ t in (16249 / 250000 : Real)..x.2,
    buchstabFunction ((B - t) / t) / (x.1.1 * x.1.2 * x.2 * t ^ 2)) ≤ _
  apply hsum.trans_eq
  unfold sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963
    sectionSixFirstLowCentralSmallI5P0BaselineD963 sectionSixFirstLowCentralSmallI5P0ExcessD963
  by_cases hcut : x.2 ≤ 4 * B / 17
  · have hmax : max 0 (17 * x.2 - 4 * (1 - x.1.1 - x.1.2 - x.2)) = 0 := by
      apply max_eq_left
      dsimp [B] at hcut
      linarith
    dsimp only [m]
    rw [min_eq_left hcut, hmax]
    field_simp [hu.ne', hv.ne', hw.ne', hB.ne']; ring
  · have hcut' : 4 * B / 17 ≤ x.2 := le_of_not_ge hcut
    have hmax : max 0 (17 * x.2 - 4 * (1 - x.1.1 - x.1.2 - x.2)) =
        17 * x.2 - 4 * (1 - x.1.1 - x.1.2 - x.2) := by
      apply max_eq_right
      dsimp [B] at hcut'
      linarith
    dsimp only [m]
    rw [min_eq_right hcut', hmax]
    dsimp only [B]
    field_simp [hu.ne', hv.ne', hw.ne', hB.ne']; ring

theorem sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963
      sectionSixFirstLowCentralSmallI5P0RefinedBase volume := by
  apply ContinuousOn.integrableOn_compact
    sectionSixFirstLowCentralSmallI5P0RefinedBase_isCompact
  intro x hx
  obtain ⟨hu, hv, hw, _, hB, _, _⟩ := base_bounds_D963 hx
  apply ContinuousAt.continuousWithinAt
  unfold sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963
    sectionSixFirstLowCentralSmallI5P0BaselineD963 sectionSixFirstLowCentralSmallI5P0ExcessD963
  fun_prop (disch := positivity)

theorem sectionSixFirstLowCentralSmallI5P0Target_integral_le_twoCeilingProfile_D963 :
    (∫ z in sectionSixFirstLowCentralSmallI5PairPatternTarget (0 : Fin 4),
      sectionSixFirstLowCentralSmallQuadrupleKernel z ∂volume) ≤
        ∫ x in sectionSixFirstLowCentralSmallI5P0RefinedBase,
          sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 x ∂volume :=
  sectionSixFirstLowCentralSmallI5P0Target_integral_le_of_fullFiber_D962
    sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963_integrable
    (fun _ hx => sectionSixFirstLowCentralSmallI5P0FullFiber_le_twoCeilingProfile_D963 hx)

end

end PrimesRestrictedDigits
