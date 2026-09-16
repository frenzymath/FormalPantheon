import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserRawFirstWeight
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogIntegral
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelLimitRecurrences

/-!
# Exact integrals for the raw first dimension-one Rosser weights

This is the raw infinite-rank counterpart of the first transformed integral in Iwaniec's
Section 8, Eqs. (8.8)--(8.9).
-/

open MeasureTheory Set
open scoped Interval Topology

namespace PrimesRestrictedDigits

private theorem raw_first_coordinate_facts
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hsLower : 2 <= s) :
    0 < s0 ∧ 1 < level ^ (1 / s0) ∧
      level ^ (1 / s0) <= z ∧
      buchstabArgument level (level ^ (1 / s0)) = s0 - 1 ∧
      buchstabArgument level z = s - 1 := by
  have hlevelOne : 1 < level := by linarith
  have hlevelPos : 0 < level := by linarith
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hwOne : 1 < level ^ (1 / s0) :=
    Real.one_lt_rpow hlevelOne (one_div_pos.mpr hs0Pos)
  have hwz : level ^ (1 / s0) <= z :=
    (dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 hsLower).le
  exact ⟨hs0Pos, hwOne, hwz,
    buchstabArgument_rpow_one_div hlevelOne hs0Pos,
    buchstabArgument_eq_sub_one_of_log_ratio hs⟩

theorem log_mul_integral_dimensionOneRosserPlusRawFirstWeight_eq
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hsLower : 3 <= s) :
    Real.log level *
        (∫ x in (level ^ (1 / s0))..z,
          dimensionOneRosserPlusRawFirstWeight level x /
            (x * Real.log x)) =
      ∫ t in (s - 1)..(s0 - 1),
        dimensionOneRosserModelMinusRaw t / t := by
  have hcoord := raw_first_coordinate_facts hlevel hz hs hss0
    (by linarith : 2 <= s)
  have harg : ∀ x ∈ Icc (level ^ (1 / s0)) z,
      (2 : Real) <= buchstabArgument level x := by
    intro x hx
    have hrange := buchstabArgument_mem_Icc_realEndpoints
      (show 1 < level by linarith) (show 1 < z by linarith)
      (show 0 < s by linarith) hs hss0 hx
    linarith [hrange.1]
  simpa only [dimensionOneRosserPlusRawFirstWeight] using
    log_mul_integral_buchstabWeight_eq
      (F := dimensionOneRosserModelMinusRaw)
      (lower := (2 : Real)) (by linarith : 0 < level) hcoord.2.1
      hcoord.2.2.1 (by norm_num) harg
      hcoord.2.2.2.1 hcoord.2.2.2.2
      continuousOn_dimensionOneRosserModelMinusRaw

theorem log_mul_integral_dimensionOneRosserMinusRawFirstWeight_eq
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hsLower : 2 <= s) :
    Real.log level *
        (∫ x in (level ^ (1 / s0))..z,
          dimensionOneRosserMinusRawFirstWeight level x /
            (x * Real.log x)) =
      ∫ t in (s - 1)..(s0 - 1),
        dimensionOneRosserModelPlusRaw t / t := by
  have hcoord := raw_first_coordinate_facts hlevel hz hs hss0 hsLower
  have harg : ∀ x ∈ Icc (level ^ (1 / s0)) z,
      (1 : Real) <= buchstabArgument level x := by
    intro x hx
    have hrange := buchstabArgument_mem_Icc_realEndpoints
      (show 1 < level by linarith) (show 1 < z by linarith)
      (show 0 < s by linarith) hs hss0 hx
    linarith [hrange.1]
  simpa only [dimensionOneRosserMinusRawFirstWeight] using
    log_mul_integral_buchstabWeight_eq
      (F := dimensionOneRosserModelPlusRaw)
      (lower := (1 : Real)) (by linarith : 0 < level) hcoord.2.1
      hcoord.2.2.1 (by norm_num) harg
      hcoord.2.2.2.1 hcoord.2.2.2.2
      continuousOn_dimensionOneRosserModelPlusRaw_Ici_one

private theorem raw_integral_shifted_interval_eq
    (F : Real -> Real) (s s0 : Real) :
    (∫ t in (s - 1)..(s0 - 1), F t / t) =
      ∫ t in s..s0, F (t - 1) / (t - 1) := by
  simpa only [sub_eq_add_neg] using
    (intervalIntegral.integral_comp_add_right
      (f := fun t : Real => F t / t) (a := s) (b := s0) (-1)).symm

theorem integral_dimensionOneRosserModelMinusRaw_div_eq
    {s s0 : Real} (hs : 3 <= s) (hss0 : s <= s0) :
    (∫ t in (s - 1)..(s0 - 1),
      dimensionOneRosserModelMinusRaw t / t) =
      dimensionOneRosserModelPlusRaw s -
        dimensionOneRosserModelPlusRaw s0 := by
  rw [raw_integral_shifted_interval_eq]
  have hint : IntegrableOn
      (fun t : Real => dimensionOneRosserModelMinusRaw (t - 1) /
        (t - 1)) (Ioi s) := by
    exact (integrableOn_shifted_dimensionOneRosserModelMinusRaw hs).congr_fun
      (fun t ht => rfl) measurableSet_Ioi
  calc
    (∫ t in s..s0,
        dimensionOneRosserModelMinusRaw (t - 1) / (t - 1)) =
        (∫ t in Ioi s,
            dimensionOneRosserModelMinusRaw (t - 1) / (t - 1)) -
          ∫ t in Ioi s0,
            dimensionOneRosserModelMinusRaw (t - 1) / (t - 1) :=
      (intervalIntegral.integral_Ioi_sub_Ioi hint hss0).symm
    _ = dimensionOneRosserModelPlusRaw s -
        dimensionOneRosserModelPlusRaw s0 := by
      rw [<- dimensionOneRosserModelPlusRaw_eq_integral_Ioi hs,
        <- dimensionOneRosserModelPlusRaw_eq_integral_Ioi (hs.trans hss0)]

theorem integral_dimensionOneRosserModelPlusRaw_div_eq
    {s s0 : Real} (hs : 2 <= s) (hss0 : s <= s0) :
    (∫ t in (s - 1)..(s0 - 1),
      dimensionOneRosserModelPlusRaw t / t) =
      dimensionOneRosserModelMinusRaw s -
        dimensionOneRosserModelMinusRaw s0 := by
  rw [raw_integral_shifted_interval_eq]
  have hint : IntegrableOn
      (fun t : Real => dimensionOneRosserModelPlusRaw (t - 1) /
        (t - 1)) (Ioi s) := by
    exact (integrableOn_shifted_dimensionOneRosserModelPlusRaw hs).congr_fun
      (fun t ht => rfl) measurableSet_Ioi
  calc
    (∫ t in s..s0,
        dimensionOneRosserModelPlusRaw (t - 1) / (t - 1)) =
        (∫ t in Ioi s,
            dimensionOneRosserModelPlusRaw (t - 1) / (t - 1)) -
          ∫ t in Ioi s0,
            dimensionOneRosserModelPlusRaw (t - 1) / (t - 1) :=
      (intervalIntegral.integral_Ioi_sub_Ioi hint hss0).symm
    _ = dimensionOneRosserModelMinusRaw s -
        dimensionOneRosserModelMinusRaw s0 := by
      rw [<- dimensionOneRosserModelMinusRaw_eq_integral_Ioi hs,
        <- dimensionOneRosserModelMinusRaw_eq_integral_Ioi (hs.trans hss0)]

end PrimesRestrictedDigits
