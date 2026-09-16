import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayFiniteTails
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogIntegral

/-!
# Unscaled delay weights for the dimension-one Rosser recurrence

This file transports the project-local unscaled delay profiles through the decreasing Buchstab
coordinate. It is independent of Iwaniec's artificial second weight.
-/

open MeasureTheory Set
open scoped Interval Topology

namespace PrimesRestrictedDigits

/-- The unscaled delay weight paired with an upper Rosser target. -/
noncomputable def dimensionOneRosserPlusUnscaledDelayWeight
    (level x : Real) : Real :=
  dimensionOneDelayScaledMinus (buchstabArgument level x) /
    Real.log (level / x)

/-- The unscaled delay weight paired with a lower Rosser target. -/
noncomputable def dimensionOneRosserMinusUnscaledDelayWeight
    (level x : Real) : Real :=
  dimensionOneDelayScaledPlus (buchstabArgument level x) /
    Real.log (level / x)

private theorem unscaledDelay_source_z_lt_level
    {level z s : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s) :
    z < level := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogIdentity : s * Real.log z = Real.log level :=
    (eq_div_iff hlogz.ne').mp hs
  apply (Real.log_lt_log_iff hzPos hlevelPos).mp
  nlinarith

private theorem unscaledDelayWeight_point_facts
    {level z s u x : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u))
    (hx : x ∈ Icc (level ^ (1 / u)) z) :
    1 < x ∧ x < level ∧ 0 < Real.log (level / x) ∧
      buchstabArgument level x ∈ Icc (s - 1) (u - 1) := by
  have hlevelOne : 1 < level := by linarith
  have hzOne : 1 < z := by linarith
  have hsPos : 0 < s := by linarith
  have hxOne : 1 < x := by linarith [hcutoff, hx.1]
  have hxLevel : x < level := hx.2.trans_lt
    (unscaledDelay_source_z_lt_level hlevel hz hs hsLower)
  have hratio : 1 < level / x := (one_lt_div (by linarith)).2 hxLevel
  exact ⟨hxOne, hxLevel, Real.log_pos hratio,
    buchstabArgument_mem_Icc_realEndpoints hlevelOne hzOne hsPos hs hsu hx⟩

private theorem unscaledDelayWeight_properties
    (F : Real -> Real) {lower level z s u : Real}
    (hFcont : Continuous F)
    (hFpos : ∀ {t : Real}, 0 < t -> 0 < F t)
    (hFanti : AntitoneOn F (Ici lower))
    (hlowerPos : 0 < lower)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hlower : lower <= s - 1) (hsu : s < u)
    (hcutoff : 2 <= level ^ (1 / u)) :
    (∀ x ∈ Icc (level ^ (1 / u)) z,
        0 <= F (buchstabArgument level x) / Real.log (level / x)) ∧
      ContinuousOn
        (fun x => F (buchstabArgument level x) / Real.log (level / x))
        (Icc (level ^ (1 / u)) z) ∧
      MonotoneOn
        (fun x => F (buchstabArgument level x) / Real.log (level / x))
        (Icc (level ^ (1 / u)) z) := by
  let interval : Set Real := Icc (level ^ (1 / u)) z
  have hargCont : ContinuousOn (buchstabArgument level) interval :=
    (continuousOn_buchstabArgument level).mono (by
      intro x hx
      exact (unscaledDelayWeight_point_facts hlevel hz hs hsLower hsu
        hcutoff hx).1)
  have hargMaps : MapsTo (buchstabArgument level) interval (Ici lower) := by
    intro x hx
    have hrange := (unscaledDelayWeight_point_facts hlevel hz hs hsLower hsu
      hcutoff hx).2.2.2
    exact hlower.trans hrange.1
  have hnumCont : ContinuousOn (fun x => F (buchstabArgument level x))
      interval := by
    change ContinuousOn (F ∘ buchstabArgument level) interval
    exact hFcont.continuousOn.comp hargCont hargMaps
  have hdivCont : ContinuousOn (fun x : Real => level / x) interval := by
    apply continuousOn_const.div continuousOn_id
    intro x hx
    exact ne_of_gt (zero_lt_one.trans
      (unscaledDelayWeight_point_facts hlevel hz hs hsLower hsu
        hcutoff hx).1)
  have hdenCont : ContinuousOn (fun x : Real => Real.log (level / x))
      interval := by
    apply Real.continuousOn_log.comp hdivCont
    intro x hx
    have hfacts := unscaledDelayWeight_point_facts hlevel hz hs hsLower hsu
      hcutoff hx
    exact ne_of_gt (div_pos (by linarith)
      (zero_lt_one.trans hfacts.1))
  constructor
  · intro x hx
    have hfacts := unscaledDelayWeight_point_facts hlevel hz hs hsLower hsu
      hcutoff hx
    exact div_nonneg (hFpos (by linarith [hlower, hfacts.2.2.2.1])).le
      hfacts.2.2.1.le
  constructor
  · apply hnumCont.div hdenCont
    intro x hx
    exact (unscaledDelayWeight_point_facts hlevel hz hs hsLower hsu
      hcutoff hx).2.2.1.ne'
  · intro x hx y hy hxy
    have hxfacts := unscaledDelayWeight_point_facts hlevel hz hs hsLower hsu
      hcutoff hx
    have hyfacts := unscaledDelayWeight_point_facts hlevel hz hs hsLower hsu
      hcutoff hy
    have hargXY : buchstabArgument level y <= buchstabArgument level x :=
      buchstabArgument_antitoneOn (show 1 < level by linarith)
        (show x ∈ Ioi (1 : Real) by exact hxfacts.1)
        (show y ∈ Ioi (1 : Real) by exact hyfacts.1) hxy
    have hnumXY : F (buchstabArgument level x) <=
        F (buchstabArgument level y) :=
      hFanti (hargMaps hy) (hargMaps hx) hargXY
    have hdenYX : Real.log (level / y) <= Real.log (level / x) :=
      log_div_antitoneOn (show 0 < level by linarith)
        (show x ∈ Ioi (0 : Real) by exact zero_lt_one.trans hxfacts.1)
        (show y ∈ Ioi (0 : Real) by exact zero_lt_one.trans hyfacts.1) hxy
    exact div_le_div₀
      (hFpos (hlowerPos.trans_le (hargMaps hy))).le hnumXY
      hyfacts.2.2.1 hdenYX

/-- Regularity of the upper-target unscaled delay weight on its natural
source interval. -/
theorem dimensionOneRosserPlusUnscaledDelayWeight_properties
    {level z s u : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u)) :
    (∀ x ∈ Icc (level ^ (1 / u)) z,
        0 <= dimensionOneRosserPlusUnscaledDelayWeight level x) ∧
      ContinuousOn (dimensionOneRosserPlusUnscaledDelayWeight level)
        (Icc (level ^ (1 / u)) z) ∧
      MonotoneOn (dimensionOneRosserPlusUnscaledDelayWeight level)
        (Icc (level ^ (1 / u)) z) := by
  unfold dimensionOneRosserPlusUnscaledDelayWeight
  exact unscaledDelayWeight_properties dimensionOneDelayScaledMinus
    dimensionOneDelayScaledMinus_continuous dimensionOneDelayScaledMinus_pos
    dimensionOneDelayScaledMinus_antitoneOn (by norm_num) hlevel hz hs (by linarith)
    (by linarith) hsu hcutoff

/-- Regularity of the lower-target unscaled delay weight on its natural
source interval. -/
theorem dimensionOneRosserMinusUnscaledDelayWeight_properties
    {level z s u : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u)) :
    (∀ x ∈ Icc (level ^ (1 / u)) z,
        0 <= dimensionOneRosserMinusUnscaledDelayWeight level x) ∧
      ContinuousOn (dimensionOneRosserMinusUnscaledDelayWeight level)
        (Icc (level ^ (1 / u)) z) ∧
      MonotoneOn (dimensionOneRosserMinusUnscaledDelayWeight level)
        (Icc (level ^ (1 / u)) z) := by
  unfold dimensionOneRosserMinusUnscaledDelayWeight
  exact unscaledDelayWeight_properties dimensionOneDelayScaledPlus
    dimensionOneDelayScaledPlus_continuous dimensionOneDelayScaledPlus_pos
    dimensionOneDelayScaledPlus_antitoneOn (by norm_num) hlevel hz hs hsLower
    (by linarith) hsu hcutoff

private theorem log_mul_integral_unscaledDelayWeight_eq
    (F : Real -> Real) {lower level z s u : Real}
    (hFcont : ContinuousOn F (Ici lower))
    (hlowerPos : 0 < lower)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hlower : lower <= s - 1) (hsu : s < u)
    (hcutoff : 2 <= level ^ (1 / u)) :
    Real.log level *
        (∫ x in (level ^ (1 / u))..z,
          (F (buchstabArgument level x) / Real.log (level / x)) /
            (x * Real.log x)) =
      ∫ t in s..u, F (t - 1) / (t - 1) := by
  have hlevelOne : 1 < level := by linarith
  have hlevelPos : 0 < level := by linarith
  have hzOne : 1 < z := by linarith
  have hsPos : 0 < s := by linarith
  have huPos : 0 < u := hsPos.trans hsu
  have hwOne : 1 < level ^ (1 / u) := by linarith [hcutoff]
  have hwz : level ^ (1 / u) <= z :=
    (dimensionOneRosserFirstCutoff_lt hlevel hz hs hsu hsLower).le
  have harg : ∀ x ∈ Icc (level ^ (1 / u)) z,
      lower <= buchstabArgument level x := by
    intro x hx
    have hrange := buchstabArgument_mem_Icc_realEndpoints
      hlevelOne hzOne hsPos hs hsu hx
    exact hlower.trans hrange.1
  have hraw := log_mul_integral_buchstabWeight_eq
    (F := F) (lower := lower) hlevelPos hwOne hwz
      hlowerPos harg
      (buchstabArgument_rpow_one_div hlevelOne huPos)
      (buchstabArgument_eq_sub_one_of_log_ratio hs) hFcont
  rw [hraw]
  simpa only [sub_eq_add_neg] using
    (intervalIntegral.integral_comp_add_right
      (f := fun t : Real => F t / t) (a := s) (b := u) (-1)).symm

/-- Exact logarithmic substitution for the upper-target unscaled delay
weight. -/
theorem log_mul_integral_dimensionOneRosserPlusUnscaledDelayWeight_eq
    {level z s u : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u)) :
    Real.log level *
        (∫ x in (level ^ (1 / u))..z,
          dimensionOneRosserPlusUnscaledDelayWeight level x /
            (x * Real.log x)) =
      ∫ t in s..u,
        dimensionOneDelayScaledMinus (t - 1) / (t - 1) := by
  unfold dimensionOneRosserPlusUnscaledDelayWeight
  exact log_mul_integral_unscaledDelayWeight_eq dimensionOneDelayScaledMinus
    (lower := (2 : Real))
    dimensionOneDelayScaledMinus_continuous.continuousOn (by norm_num)
    hlevel hz hs
    (by linarith) (by linarith) hsu hcutoff

/-- Exact logarithmic substitution for the lower-target unscaled delay
weight. -/
theorem log_mul_integral_dimensionOneRosserMinusUnscaledDelayWeight_eq
    {level z s u : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsu : s < u) (hcutoff : 2 <= level ^ (1 / u)) :
    Real.log level *
        (∫ x in (level ^ (1 / u))..z,
          dimensionOneRosserMinusUnscaledDelayWeight level x /
            (x * Real.log x)) =
      ∫ t in s..u,
        dimensionOneDelayScaledPlus (t - 1) / (t - 1) := by
  unfold dimensionOneRosserMinusUnscaledDelayWeight
  exact log_mul_integral_unscaledDelayWeight_eq dimensionOneDelayScaledPlus
    (lower := (1 : Real))
    dimensionOneDelayScaledPlus_continuous.continuousOn (by norm_num)
    hlevel hz hs
    hsLower (by linarith) hsu hcutoff

end PrimesRestrictedDigits
