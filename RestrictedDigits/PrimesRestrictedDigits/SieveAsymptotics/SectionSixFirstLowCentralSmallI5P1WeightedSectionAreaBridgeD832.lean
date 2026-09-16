import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1WeightedSectionBridgeD831
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0AnalyticD816
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
/-! # SectionSixFirstLowCentralSmallI5P1WeightedSectionAreaBridgeD832 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

theorem sectionSixFirstLowCentralSmallI5P1D832_p1Case1_inner_formula
    {a d r : Real} (ha : a ≠ 0) :
    (∫ s in (0 : Real)..
      min r (sectionSixFirstLowCentralSmallI5P1D807L d - r),
      sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight a (r, s)) =
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a
          (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r)) := by
  unfold sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight
  change (∫ s in (0 : Real)..
      min r (sectionSixFirstLowCentralSmallI5P1D807L d - r),
      sectionSixFirstLowCentralSmallI5P1D814Q4 a r *
        sectionSixFirstLowCentralSmallI5P1D814Q4 a s) = _
  rw [intervalIntegral.integral_const_mul]
  rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive ha]
  have hq0 : sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a 0 = 0 := by
    simp [sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
      sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
  rw [hq0, sub_zero]

theorem sectionSixFirstLowCentralSmallI5P1D832_p1Case1_weightedSection_eq_area
    {a d : Real} (ha : a ≠ 0)
    (hd : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr) :
    sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection a d =
      sectionSixFirstLowCentralSmallI5P1D830P1Case1Area a d := by
  have horder := sectionSixFirstLowCentralSmallI5P1D830_p1Case1_endpoint_order hd
  have h0m : 0 ≤ sectionSixFirstLowCentralSmallI5P1D807L d / 2 := horder.1
  have hmH : sectionSixFirstLowCentralSmallI5P1D807L d / 2 ≤
      sectionSixFirstLowCentralSmallI5P1D807H d := horder.2.1
  have h0H : 0 ≤ sectionSixFirstLowCentralSmallI5P1D807H d :=
    h0m.trans hmH
  let g : Real → Real := fun r =>
    sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a
        (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r))
  have hgcont : Continuous g := by
    dsimp [g]
    have hprimcont : Continuous
        (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a) := by
      unfold sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
        sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
      fun_prop
    apply (sectionSixFirstLowCentralSmallI5P1D816_q4_continuous a).mul
    apply hprimcont.comp
    exact continuous_id.min (continuous_const.sub continuous_id)
  have hg0m : IntervalIntegrable g volume 0
      (sectionSixFirstLowCentralSmallI5P1D807L d / 2) :=
    hgcont.intervalIntegrable _ _
  have hinner : ∀ r : Real,
      (∫ s in (0 : Real)..
        min r (sectionSixFirstLowCentralSmallI5P1D807L d - r),
        sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight a (r, s)) =
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a
            (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r)) := by
    intro r
    exact sectionSixFirstLowCentralSmallI5P1D832_p1Case1_inner_formula ha
  have hset :
      sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection a d =
        ∫ r in Set.Icc 0 (sectionSixFirstLowCentralSmallI5P1D807H d), g r := by
    unfold sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
    apply integral_congr_ae
    filter_upwards with r
    rw [hinner]
  have hinterval :
      (∫ r in Set.Icc 0 (sectionSixFirstLowCentralSmallI5P1D807H d), g r) =
        ∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807H d, g r := by
    rw [integral_Icc_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le h0H).symm
  have hsplit :
      (∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807H d, g r) =
        (∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807L d / 2, g r) +
          ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
            sectionSixFirstLowCentralSmallI5P1D807H d, g r := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals hg0m (hgcont.intervalIntegrable _ _)
  have hlower :
      (∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807L d / 2, g r) =
        (∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807L d / 2,
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp [g]
    have hr' : r ∈ Set.Icc (0 : Real)
        (sectionSixFirstLowCentralSmallI5P1D807L d / 2) := by
      simpa [Set.uIcc_of_le h0m] using hr
    have hmin : min r (sectionSixFirstLowCentralSmallI5P1D807L d - r) = r := by
      apply min_eq_left
      linarith [hr'.2]
    rw [hmin]
  have hupper :
      (∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
        sectionSixFirstLowCentralSmallI5P1D807H d, g r) =
        ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
          sectionSixFirstLowCentralSmallI5P1D807H d,
          sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperIntegrand a d r := by
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp [g]
    have hr' : r ∈ Set.Icc (sectionSixFirstLowCentralSmallI5P1D807L d / 2)
        (sectionSixFirstLowCentralSmallI5P1D807H d) := by
      simpa [Set.uIcc_of_le hmH] using hr
    have hmin : min r (sectionSixFirstLowCentralSmallI5P1D807L d - r) =
        sectionSixFirstLowCentralSmallI5P1D807L d - r := by
      apply min_eq_right
      linarith [hr'.1]
    rw [hmin]
    rfl
  calc
    sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection a d =
        ∫ r in Set.Icc 0 (sectionSixFirstLowCentralSmallI5P1D807H d), g r := hset
    _ = ∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807H d, g r := hinterval
    _ = (∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807L d / 2, g r) +
          ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
            sectionSixFirstLowCentralSmallI5P1D807H d, g r := hsplit
    _ = (∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807L d / 2,
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a r) +
          ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
            sectionSixFirstLowCentralSmallI5P1D807H d,
            sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperIntegrand a d r := by
      rw [hlower, hupper]
    _ = (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a
          (sectionSixFirstLowCentralSmallI5P1D807L d / 2)) ^ 2 / 2 +
          ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
            sectionSixFirstLowCentralSmallI5P1D807H d,
            sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperIntegrand a d r := by
      have htri := sectionSixFirstLowCentralSmallI5P1D816_triangular_q4
        (a := a) (H := sectionSixFirstLowCentralSmallI5P1D807L d / 2) ha
      have hq0 : sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a 0 = 0 := by
        simp [sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
          sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
      have hinner0 : ∀ r : Real,
          (∫ s in (0 : Real)..r,
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a s) =
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a r := by
        intro r
        rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive ha,
          hq0, sub_zero]
      have htri' :
          (∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807L d / 2,
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a r) =
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a
              (sectionSixFirstLowCentralSmallI5P1D807L d / 2) ^ 2 / 2 := by
        calc
          (∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807L d / 2,
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
                sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a r) =
              ∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807L d / 2,
                sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
                  (∫ s in (0 : Real)..r,
                    sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a s) := by
            apply intervalIntegral.integral_congr
            intro r hr
            change sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
                sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a r =
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
                (∫ s in (0 : Real)..r,
                  sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a s)
            rw [hinner0 r]
          _ = sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a
                (sectionSixFirstLowCentralSmallI5P1D807L d / 2) ^ 2 / 2 := htri
      rw [htri']
    _ = sectionSixFirstLowCentralSmallI5P1D830P1Case1Area a d := by
      rfl


end
end PrimesRestrictedDigits
