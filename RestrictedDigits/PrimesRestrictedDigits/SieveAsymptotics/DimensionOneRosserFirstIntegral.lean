import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogIntegral
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelRecurrences

/-!
# Exact integrals for the first dimension-one Rosser weight

This file proves the change of logarithmic variable and finite-model endpoint evaluations in
Iwaniec's first transformed recurrence term. See `IWANIEC-ROSSER-SIEVE-1980`, Section 8, Eqs.
(8.8)--(8.9).
-/

open MeasureTheory Set
open scoped Interval Topology

namespace PrimesRestrictedDigits

/-- The decreasing Buchstab coordinate transforms the upper-target weight
into the lower finite-model kernel, with the endpoints reversed. -/
theorem log_mul_integral_dimensionOneRosserPlusFirstWeight_eq
    (R : Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hsLower : 3 <= s) :
    Real.log level *
        (∫ x in (level ^ (1 / s0))..z,
          dimensionOneRosserPlusFirstWeight R level x /
            (x * Real.log x)) =
      ∫ t in (s - 1)..(s0 - 1),
        dimensionOneRosserModelMinusPartialSum R t / t := by
  have hlevelOne : 1 < level := by linarith
  have hlevelPos : 0 < level := by linarith
  have hzOne : 1 < z := by linarith
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hwOne : 1 < level ^ (1 / s0) :=
    Real.one_lt_rpow hlevelOne (one_div_pos.mpr hs0Pos)
  have hwz : level ^ (1 / s0) <= z :=
    (dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0
      (by linarith)).le
  have harg : ∀ x ∈ Icc (level ^ (1 / s0)) z,
      (2 : Real) <= buchstabArgument level x := by
    intro x hx
    have hrange := buchstabArgument_mem_Icc_realEndpoints
      hlevelOne hzOne hsPos hs hss0 hx
    linarith [hrange.1]
  simpa only [dimensionOneRosserPlusFirstWeight] using
    log_mul_integral_buchstabWeight_eq
      (F := dimensionOneRosserModelMinusPartialSum R)
      (lower := (2 : Real)) hlevelPos hwOne hwz (by norm_num) harg
      (buchstabArgument_rpow_one_div hlevelOne hs0Pos)
      (buchstabArgument_eq_sub_one_of_log_ratio hs)
      (dimensionOneRosserModelMinusPartialSum_continuousOn R)

/-- The decreasing Buchstab coordinate transforms the lower-target weight
into the upper finite-model kernel, including the endpoint `s = 2`. -/
theorem log_mul_integral_dimensionOneRosserMinusFirstWeight_eq
    (R : Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hsLower : 2 <= s) :
    Real.log level *
        (∫ x in (level ^ (1 / s0))..z,
          dimensionOneRosserMinusFirstWeight R level x /
            (x * Real.log x)) =
      ∫ t in (s - 1)..(s0 - 1),
        dimensionOneRosserModelPlusPartialSum R t / t := by
  have hlevelOne : 1 < level := by linarith
  have hlevelPos : 0 < level := by linarith
  have hzOne : 1 < z := by linarith
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hwOne : 1 < level ^ (1 / s0) :=
    Real.one_lt_rpow hlevelOne (one_div_pos.mpr hs0Pos)
  have hwz : level ^ (1 / s0) <= z :=
    (dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 hsLower).le
  have harg : ∀ x ∈ Icc (level ^ (1 / s0)) z,
      (1 : Real) <= buchstabArgument level x := by
    intro x hx
    have hrange := buchstabArgument_mem_Icc_realEndpoints
      hlevelOne hzOne hsPos hs hss0 hx
    linarith [hrange.1]
  simpa only [dimensionOneRosserMinusFirstWeight] using
    log_mul_integral_buchstabWeight_eq
      (F := dimensionOneRosserModelPlusPartialSum R)
      (lower := (1 : Real)) hlevelPos hwOne hwz (by norm_num) harg
      (buchstabArgument_rpow_one_div hlevelOne hs0Pos)
      (buchstabArgument_eq_sub_one_of_log_ratio hs)
      (dimensionOneRosserModelPlusPartialSum_continuousOn R)

private theorem integral_shifted_interval_eq
    (F : Real -> Real) (s s0 : Real) :
    (∫ t in (s - 1)..(s0 - 1), F t / t) =
      ∫ t in s..s0, F (t - 1) / (t - 1) := by
  simpa only [sub_eq_add_neg] using
    (intervalIntegral.integral_comp_add_right
      (f := fun t : Real => F t / t) (a := s) (b := s0) (-1)).symm

/-- A finite interval of the lower model kernel is the difference of the
upper-model tails. The weak hypothesis includes the source seam `s = 3`. -/
theorem integral_dimensionOneRosserModelMinusPartialSum_div_eq
    (R : Nat) {s s0 : Real} (hs : 3 <= s) (hss0 : s <= s0) :
    (∫ t in (s - 1)..(s0 - 1),
      dimensionOneRosserModelMinusPartialSum R t / t) =
      dimensionOneRosserModelPlusPartialSum R s -
        dimensionOneRosserModelPlusPartialSum R s0 := by
  rw [integral_shifted_interval_eq]
  have hint : IntegrableOn
      (fun t : Real => dimensionOneRosserModelMinusPartialSum R (t - 1) /
        (t - 1)) (Ioi s) := by
    exact (integrable_shiftedRosserKernel_minusPartialSum R).integrableOn.congr_fun
      (fun t ht => rfl) measurableSet_Ioi
  calc
    (∫ t in s..s0,
        dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1)) =
        (∫ t in Ioi s,
            dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1)) -
          ∫ t in Ioi s0,
            dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1) :=
      (intervalIntegral.integral_Ioi_sub_Ioi hint hss0).symm
    _ = dimensionOneRosserModelPlusPartialSum R s -
        dimensionOneRosserModelPlusPartialSum R s0 := by
      rw [<- dimensionOneRosserModelPlusPartialSum_integral R hs,
        <- dimensionOneRosserModelPlusPartialSum_integral R (hs.trans hss0)]

/-- A finite interval of the upper model kernel is the difference of the
successor lower-model tails. The weak hypothesis includes `s = 2`. -/
theorem integral_dimensionOneRosserModelPlusPartialSum_div_eq
    (R : Nat) {s s0 : Real} (hs : 2 <= s) (hss0 : s <= s0) :
    (∫ t in (s - 1)..(s0 - 1),
      dimensionOneRosserModelPlusPartialSum R t / t) =
      dimensionOneRosserModelMinusPartialSum (R + 1) s -
        dimensionOneRosserModelMinusPartialSum (R + 1) s0 := by
  rw [integral_shifted_interval_eq]
  have hint : IntegrableOn
      (fun t : Real => dimensionOneRosserModelPlusPartialSum R (t - 1) /
        (t - 1)) (Ioi s) := by
    exact (integrable_shiftedRosserKernel_plusPartialSum R).integrableOn.congr_fun
      (fun t ht => rfl) measurableSet_Ioi
  calc
    (∫ t in s..s0,
        dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1)) =
        (∫ t in Ioi s,
            dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1)) -
          ∫ t in Ioi s0,
            dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1) :=
      (intervalIntegral.integral_Ioi_sub_Ioi hint hss0).symm
    _ = dimensionOneRosserModelMinusPartialSum (R + 1) s -
        dimensionOneRosserModelMinusPartialSum (R + 1) s0 := by
      rw [<- dimensionOneRosserModelMinusPartialSum_succ_integral R hs,
        <- dimensionOneRosserModelMinusPartialSum_succ_integral R
          (hs.trans hss0)]

end PrimesRestrictedDigits
