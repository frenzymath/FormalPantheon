import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0AnalyticD816
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece2Case2AreaD879 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# Piece2 Case2 Q4 weighted-section identity

This module records the symbolic Q4 area split for the transformed Piece2 endpoint. It makes
no claim about the majorant, the kernel, or any numerical/cap or aggregate estimate.
-/

private abbrev L : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807L
private abbrev Q4 : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4
private abbrev Prim : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive

def sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection
    (a d : Real) : Real :=
  ∫ r in Set.Icc (0 : Real)
      (sectionSixFirstLowCentralSmallI5P1D807L d),
    ∫ s in (0 : Real)..
        min r (sectionSixFirstLowCentralSmallI5P1D807L d - r),
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a s

def sectionSixFirstLowCentralSmallI5P1D879Piece2Case2Area
    (a d : Real) : Real :=
  (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a
      (sectionSixFirstLowCentralSmallI5P1D807L d / 2)) ^ 2 / 2 +
    ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
        sectionSixFirstLowCentralSmallI5P1D807L d,
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a
          (sectionSixFirstLowCentralSmallI5P1D807L d - r)

theorem sectionSixFirstLowCentralSmallI5P1D879_piece2_weightedSection_eq_case2Area
    {a d : Real} (ha : a ≠ 0)
    (hL0 : 0 ≤ sectionSixFirstLowCentralSmallI5P1D807L d) :
    sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection a d =
      sectionSixFirstLowCentralSmallI5P1D879Piece2Case2Area a d := by
  let g : Real → Real := fun r => Q4 a r * Prim a (min r (L d - r))
  have hgcont : Continuous g := by
    dsimp [g]
    have hp : Continuous (Prim a) := by
      unfold Prim sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
        sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
      fun_prop
    exact (sectionSixFirstLowCentralSmallI5P1D816_q4_continuous a).mul
      (hp.comp (continuous_id.min (continuous_const.sub continuous_id)))
  have hinner : ∀ r : Real,
      (∫ s in (0 : Real)..min r (L d - r), Q4 a r * Q4 a s) = g r := by
    intro r
    dsimp [g]
    rw [intervalIntegral.integral_const_mul]
    rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive ha]
    have hP0 :
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a 0 = 0 := by
      simp [sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
    rw [hP0, sub_zero]
  have hset :
      sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection a d =
        ∫ r in Set.Icc 0 (L d), g r := by
    unfold sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection
    apply integral_congr_ae
    filter_upwards with r
    exact hinner r
  have hinterval :
      (∫ r in Set.Icc 0 (L d), g r) =
        ∫ r in (0 : Real)..L d, g r := by
    rw [integral_Icc_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le hL0).symm
  have hsplit :
      (∫ r in (0 : Real)..L d, g r) =
        (∫ r in (0 : Real)..L d / 2, g r) +
          ∫ r in L d / 2..L d, g r := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hgcont.intervalIntegrable _ _) (hgcont.intervalIntegrable _ _)
  have hlower :
      (∫ r in (0 : Real)..L d / 2, g r) =
        ∫ r in (0 : Real)..L d / 2, Q4 a r * Prim a r := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Set.Icc (0 : Real) (L d / 2) := by
      simpa [Set.uIcc_of_le (by linarith : (0 : Real) ≤ L d / 2)] using hr
    dsimp [g]
    rw [min_eq_left (by linarith [hr'.2])]
  have hupper :
      (∫ r in L d / 2..L d, g r) =
        ∫ r in L d / 2..L d, Q4 a r * Prim a (L d - r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Set.Icc (L d / 2) (L d) := by
      simpa [Set.uIcc_of_le (by linarith : L d / 2 ≤ L d)] using hr
    dsimp [g]
    rw [min_eq_right (by linarith [hr'.1])]
  have htri :
      (∫ r in (0 : Real)..L d / 2, Q4 a r * Prim a r) =
        (Prim a (L d / 2)) ^ 2 / 2 := by
    have h := sectionSixFirstLowCentralSmallI5P1D816_triangular_q4
      (a := a) (H := L d / 2) ha
    have hP0 :
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a 0 = 0 := by
      simp [sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
    have hinner0 : ∀ r : Real,
        (∫ s in (0 : Real)..r, Q4 a s) = Prim a r := by
      intro r
      rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive ha,
        hP0, sub_zero]
    calc
      (∫ r in (0 : Real)..L d / 2, Q4 a r * Prim a r) =
          ∫ r in (0 : Real)..L d / 2,
            Q4 a r * (∫ s in (0 : Real)..r, Q4 a s) := by
        apply intervalIntegral.integral_congr
        intro r hr
        change Q4 a r * Prim a r =
          Q4 a r * (∫ s in (0 : Real)..r, Q4 a s)
        rw [hinner0]
      _ = (Prim a (L d / 2)) ^ 2 / 2 := h
  calc
    sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection a d =
        ∫ r in Set.Icc 0 (L d), g r := hset
    _ = ∫ r in (0 : Real)..L d, g r := hinterval
    _ = (∫ r in (0 : Real)..L d / 2, g r) +
          ∫ r in L d / 2..L d, g r := hsplit
    _ = (∫ r in (0 : Real)..L d / 2, Q4 a r * Prim a r) +
          ∫ r in L d / 2..L d, Q4 a r * Prim a (L d - r) := by
      rw [hlower, hupper]
    _ = sectionSixFirstLowCentralSmallI5P1D879Piece2Case2Area a d := by
      rw [htri]
      rfl


end
end PrimesRestrictedDigits
