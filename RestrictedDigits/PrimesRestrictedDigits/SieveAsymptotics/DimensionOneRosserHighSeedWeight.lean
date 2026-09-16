import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedCalculus
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogIntegral

/-!
# Transformed weight for the independent high-rank seed

This file transports the elementary seed envelope through the decreasing Buchstab coordinate.
It supplies the sign-free weight used in the independent replacement for Iwaniec's Eq. (8.13).
-/

open MeasureTheory Set
open scoped Interval Topology

namespace PrimesRestrictedDigits

/-- The seed envelope divided by the logarithmic factor in the first Rosser
weight. -/
noncomputable def dimensionOneRosserSeedWeight
    (level x : Real) : Real :=
  dimensionOneRosserSeedEnvelope (buchstabArgument level x) /
    Real.log (level / x)

private theorem dimensionOneRosserSeed_z_lt_level
    {level z s : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) :
    z < level := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsTwo : 2 <= s := by
    have hexp : (1 : Real) <= Real.exp 5000 :=
      Real.one_le_exp (by norm_num)
    linarith
  have hlogIdentity : s * Real.log z = Real.log level :=
    (eq_div_iff hlogz.ne').mp hs
  apply (Real.log_lt_log_iff hzPos hlevelPos).mp
  nlinarith

private theorem dimensionOneRosserSeedWeight_point_facts
    {level z s s0 x : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hx : x ∈ Icc (level ^ (1 / s0)) z) :
    1 < x ∧ x < level ∧ 0 < Real.log (level / x) ∧
      buchstabArgument level x ∈ Icc (s - 1) (s0 - 1) := by
  have hlevelOne : 1 < level := by linarith
  have hzOne : 1 < z := by linarith
  have hsPos : 0 < s := by
    have := Real.exp_pos (5000 : Real)
    linarith
  have hxOne : 1 < x := by linarith [hcutoff, hx.1]
  have hxLevel : x < level :=
    hx.2.trans_lt (dimensionOneRosserSeed_z_lt_level hlevel hz hs hsLarge)
  have hratio : 1 < level / x := (one_lt_div (by linarith)).mpr hxLevel
  exact ⟨hxOne, hxLevel, Real.log_pos hratio,
    buchstabArgument_mem_Icc_realEndpoints hlevelOne hzOne hsPos hs hss0 hx⟩

private theorem dimensionOneRosserSeedWeight_nonneg
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    ∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserSeedWeight level x := by
  intro x hx
  have hfacts := dimensionOneRosserSeedWeight_point_facts hlevel hz hs
    hsLarge hss0 hcutoff hx
  unfold dimensionOneRosserSeedWeight
  exact div_nonneg (dimensionOneRosserSeedEnvelope_pos _).le
    hfacts.2.2.1.le

private theorem dimensionOneRosserSeedWeight_continuousOn
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    ContinuousOn (dimensionOneRosserSeedWeight level)
      (Icc (level ^ (1 / s0)) z) := by
  let interval := Icc (level ^ (1 / s0)) z
  have hargCont : ContinuousOn (buchstabArgument level) interval :=
    (continuousOn_buchstabArgument level).mono (by
      intro x hx
      exact (dimensionOneRosserSeedWeight_point_facts hlevel hz hs hsLarge
        hss0 hcutoff hx).1)
  have hargMaps : MapsTo (buchstabArgument level) interval (Ioi 1) := by
    intro x hx
    have hrange := (dimensionOneRosserSeedWeight_point_facts hlevel hz hs
      hsLarge hss0 hcutoff hx).2.2.2
    have hexp : 1 < Real.exp 5000 := by
      linarith [Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)]
    change 1 < buchstabArgument level x
    linarith [hrange.1]
  have hnum : ContinuousOn
      (fun x => dimensionOneRosserSeedEnvelope (buchstabArgument level x))
      interval := by
    change ContinuousOn
      (dimensionOneRosserSeedEnvelope ∘ buchstabArgument level) interval
    exact dimensionOneRosserSeedEnvelope_continuousOn.comp hargCont hargMaps
  have hdiv : ContinuousOn (fun x : Real => level / x) interval := by
    apply continuousOn_const.div continuousOn_id
    intro x hx
    exact ne_of_gt (zero_lt_one.trans
      (dimensionOneRosserSeedWeight_point_facts hlevel hz hs hsLarge hss0
        hcutoff hx).1)
  have hden : ContinuousOn (fun x : Real => Real.log (level / x)) interval := by
    apply Real.continuousOn_log.comp hdiv
    intro x hx
    exact ne_of_gt (div_pos (by linarith)
      (zero_lt_one.trans
        (dimensionOneRosserSeedWeight_point_facts hlevel hz hs hsLarge hss0
          hcutoff hx).1))
  unfold dimensionOneRosserSeedWeight
  apply hnum.div hden
  intro x hx
  exact (dimensionOneRosserSeedWeight_point_facts hlevel hz hs hsLarge hss0
    hcutoff hx).2.2.1.ne'

private theorem dimensionOneRosserSeedWeight_monotoneOn
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    MonotoneOn (dimensionOneRosserSeedWeight level)
      (Icc (level ^ (1 / s0)) z) := by
  intro x hx y hy hxy
  have hxfacts := dimensionOneRosserSeedWeight_point_facts hlevel hz hs
    hsLarge hss0 hcutoff hx
  have hyfacts := dimensionOneRosserSeedWeight_point_facts hlevel hz hs
    hsLarge hss0 hcutoff hy
  have hargAnti := buchstabArgument_antitoneOn
    (show 1 < level by linarith)
  have hargXY : buchstabArgument level y <= buchstabArgument level x :=
    hargAnti (by exact hxfacts.1) (by exact hyfacts.1) hxy
  have hxmin : Real.exp 5000 <= buchstabArgument level x := by
    linarith [hxfacts.2.2.2.1]
  have hymin : Real.exp 5000 <= buchstabArgument level y := by
    linarith [hyfacts.2.2.2.1]
  have hnumXY :
      dimensionOneRosserSeedEnvelope (buchstabArgument level x) <=
        dimensionOneRosserSeedEnvelope (buchstabArgument level y) :=
    dimensionOneRosserSeedEnvelope_strictAntiOn.antitoneOn
      (show buchstabArgument level y ∈ Ici (Real.exp 5000) by exact hymin)
      (show buchstabArgument level x ∈ Ici (Real.exp 5000) by exact hxmin)
      hargXY
  have hdenYX : Real.log (level / y) <= Real.log (level / x) :=
    log_div_antitoneOn (show 0 < level by linarith)
      (show x ∈ Ioi 0 by exact zero_lt_one.trans hxfacts.1)
      (show y ∈ Ioi 0 by exact zero_lt_one.trans hyfacts.1) hxy
  unfold dimensionOneRosserSeedWeight
  exact div_le_div₀ (dimensionOneRosserSeedEnvelope_pos _).le hnumXY
    hyfacts.2.2.1 hdenYX

/-- The seed weight satisfies all hypotheses required by weighted density
summation on the full source interval. -/
theorem dimensionOneRosserSeedWeight_properties
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserSeedWeight level x) ∧
    ContinuousOn (dimensionOneRosserSeedWeight level)
      (Icc (level ^ (1 / s0)) z) ∧
    MonotoneOn (dimensionOneRosserSeedWeight level)
      (Icc (level ^ (1 / s0)) z) := by
  exact ⟨dimensionOneRosserSeedWeight_nonneg hlevel hz hs hsLarge hss0
      hcutoff,
    dimensionOneRosserSeedWeight_continuousOn hlevel hz hs hsLarge hss0
      hcutoff,
    dimensionOneRosserSeedWeight_monotoneOn hlevel hz hs hsLarge hss0
      hcutoff⟩

/-- The decreasing Buchstab coordinate gives the exact shifted seed-envelope
integral, with neither endpoint discarded. -/
theorem log_mul_integral_dimensionOneRosserSeedWeight_eq
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    Real.log level *
        (∫ x in (level ^ (1 / s0))..z,
          dimensionOneRosserSeedWeight level x /
            (x * Real.log x)) =
      ∫ t in s..s0,
        dimensionOneRosserSeedEnvelope (t - 1) / (t - 1) := by
  have hlevelOne : 1 < level := by linarith
  have hlevelPos : 0 < level := by linarith
  have hsPos : 0 < s := by
    have := Real.exp_pos (5000 : Real)
    linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hwOne : 1 < level ^ (1 / s0) := by linarith [hcutoff]
  have hwz : level ^ (1 / s0) <= z :=
    (dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 (by
      have hexp : (1 : Real) <= Real.exp 5000 :=
        Real.one_le_exp (by norm_num)
      linarith)).le
  have harg : ∀ x ∈ Icc (level ^ (1 / s0)) z,
      Real.exp 5000 <= buchstabArgument level x := by
    intro x hx
    have hrange := (dimensionOneRosserSeedWeight_point_facts hlevel hz hs
      hsLarge hss0 hcutoff hx).2.2.2
    linarith [hrange.1]
  have hcontinuous : ContinuousOn dimensionOneRosserSeedEnvelope
      (Ici (Real.exp 5000)) :=
    dimensionOneRosserSeedEnvelope_continuousOn.mono (by
      intro t ht
      have hexp : 1 < Real.exp 5000 := by
        linarith [Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)]
      exact hexp.trans_le ht)
  have htransform := log_mul_integral_buchstabWeight_eq
    (F := dimensionOneRosserSeedEnvelope) (lower := Real.exp 5000)
    hlevelPos hwOne hwz (Real.exp_pos _) harg
    (buchstabArgument_rpow_one_div hlevelOne hs0Pos)
    (buchstabArgument_eq_sub_one_of_log_ratio hs) hcontinuous
  have hshift :
      (∫ t in (s - 1)..(s0 - 1),
        dimensionOneRosserSeedEnvelope t / t) =
        ∫ t in s..s0,
          dimensionOneRosserSeedEnvelope (t - 1) / (t - 1) := by
    simpa only [sub_eq_add_neg] using
      (intervalIntegral.integral_comp_add_right
        (f := fun t : Real => dimensionOneRosserSeedEnvelope t / t)
        (a := s) (b := s0) (-1)).symm
  calc
    Real.log level *
        (∫ x in (level ^ (1 / s0))..z,
          dimensionOneRosserSeedWeight level x /
            (x * Real.log x)) =
      ∫ t in (s - 1)..(s0 - 1),
        dimensionOneRosserSeedEnvelope t / t := by
      simpa only [dimensionOneRosserSeedWeight] using htransform
    _ = _ := hshift

end PrimesRestrictedDigits
