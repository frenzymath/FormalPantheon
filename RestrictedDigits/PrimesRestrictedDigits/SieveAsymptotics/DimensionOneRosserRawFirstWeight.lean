import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelPlusEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogTransform

/-!
# Regularity of the raw first dimension-one Rosser weights

This is the infinite-rank analogue of the first transformed weights in Iwaniec's Section 8,
Eqs. (8.8)--(8.9). It proves only the closed-interval regularity needed by the
weighted-density theorem.
-/

open Set

namespace PrimesRestrictedDigits

/-- Raw first weight for an upper target. -/
noncomputable def dimensionOneRosserPlusRawFirstWeight
    (level x : Real) : Real :=
  dimensionOneRosserModelMinusRaw (buchstabArgument level x) /
    Real.log (level / x)

/-- Raw first weight for a lower target. -/
noncomputable def dimensionOneRosserMinusRawFirstWeight
    (level x : Real) : Real :=
  dimensionOneRosserModelPlusRaw (buchstabArgument level x) /
    Real.log (level / x)

private theorem raw_source_z_lt_level
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

private theorem raw_source_weight_point_facts
    {level z s s0 x : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 2 <= s)
    (hx : x ∈ Icc (level ^ (1 / s0)) z) :
    1 < x ∧ x < level ∧ 0 < Real.log (level / x) ∧
      buchstabArgument level x ∈ Icc (s - 1) (s0 - 1) := by
  have hlevelOne : 1 < level := by linarith
  have hzOne : 1 < z := by linarith
  have hxOne : 1 < x := by linarith [hcutoff, hx.1]
  have hxLevel : x < level := hx.2.trans_lt
    (raw_source_z_lt_level hlevel hz hs hsLower)
  have hratio : 1 < level / x := (one_lt_div (by linarith)).mpr hxLevel
  have hsPos : 0 < s := by linarith
  exact ⟨hxOne, hxLevel, Real.log_pos hratio,
    buchstabArgument_mem_Icc_realEndpoints hlevelOne hzOne hsPos hs hss0 hx⟩

private theorem raw_continuousOn_log_level_div
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 2 <= s) :
    ContinuousOn (fun x : Real => Real.log (level / x))
      (Icc (level ^ (1 / s0)) z) := by
  have hdiv : ContinuousOn (fun x : Real => level / x)
      (Icc (level ^ (1 / s0)) z) := by
    apply continuousOn_const.div continuousOn_id
    intro x hx
    change x ≠ 0
    exact ne_of_gt (by linarith [(raw_source_weight_point_facts hlevel hz hs
      hss0 hcutoff hsLower hx).1])
  change ContinuousOn (Real.log ∘ fun x : Real => level / x)
    (Icc (level ^ (1 / s0)) z)
  apply Real.continuousOn_log.comp hdiv
  intro x hx
  exact ne_of_gt (div_pos (by linarith)
    (by linarith [(raw_source_weight_point_facts hlevel hz hs hss0
      hcutoff hsLower hx).1]))

private theorem plus_raw_first_weight_nonneg
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 3 <= s) :
    ∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserPlusRawFirstWeight level x := by
  intro x hx
  have hfacts := raw_source_weight_point_facts hlevel hz hs hss0 hcutoff
    (by linarith) hx
  unfold dimensionOneRosserPlusRawFirstWeight
  exact div_nonneg (dimensionOneRosserModelMinusRaw_nonneg _) hfacts.2.2.1.le

private theorem plus_raw_first_weight_continuousOn
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 3 <= s) :
    ContinuousOn (dimensionOneRosserPlusRawFirstWeight level)
      (Icc (level ^ (1 / s0)) z) := by
  have hargCont : ContinuousOn (buchstabArgument level)
      (Icc (level ^ (1 / s0)) z) :=
    (continuousOn_buchstabArgument level).mono (by
      intro x hx
      exact (raw_source_weight_point_facts hlevel hz hs hss0 hcutoff
        (by linarith) hx).1)
  have hargMaps : MapsTo (buchstabArgument level)
      (Icc (level ^ (1 / s0)) z) (Ici 2) := by
    intro x hx
    have hrange := (raw_source_weight_point_facts hlevel hz hs hss0
      hcutoff (by linarith) hx).2.2.2
    change 2 <= buchstabArgument level x
    linarith [hrange.1]
  have hnum : ContinuousOn
      (fun x => dimensionOneRosserModelMinusRaw (buchstabArgument level x))
      (Icc (level ^ (1 / s0)) z) := by
    change ContinuousOn
      (dimensionOneRosserModelMinusRaw ∘ buchstabArgument level)
      (Icc (level ^ (1 / s0)) z)
    exact continuousOn_dimensionOneRosserModelMinusRaw.comp hargCont hargMaps
  unfold dimensionOneRosserPlusRawFirstWeight
  apply hnum.div
    (raw_continuousOn_log_level_div hlevel hz hs hss0 hcutoff (by linarith))
  intro x hx
  exact (raw_source_weight_point_facts hlevel hz hs hss0 hcutoff
    (by linarith) hx).2.2.1.ne'

private theorem plus_raw_first_weight_monotoneOn
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 3 <= s) :
    MonotoneOn (dimensionOneRosserPlusRawFirstWeight level)
      (Icc (level ^ (1 / s0)) z) := by
  intro x hx y hy hxy
  have hxfacts := raw_source_weight_point_facts hlevel hz hs hss0 hcutoff
    (by linarith) hx
  have hyfacts := raw_source_weight_point_facts hlevel hz hs hss0 hcutoff
    (by linarith) hy
  have hargXY : buchstabArgument level y <= buchstabArgument level x :=
    buchstabArgument_antitoneOn (show 1 < level by linarith)
      hxfacts.1 hyfacts.1 hxy
  have hnumXY :
      dimensionOneRosserModelMinusRaw (buchstabArgument level x) <=
        dimensionOneRosserModelMinusRaw (buchstabArgument level y) :=
    (dimensionOneRosserModelRaw_antitoneOn).2
      (show buchstabArgument level y ∈ Ici 2 by
        change 2 <= buchstabArgument level y
        linarith [hyfacts.2.2.2.1])
      (show buchstabArgument level x ∈ Ici 2 by
        change 2 <= buchstabArgument level x
        linarith [hxfacts.2.2.2.1]) hargXY
  have hdenYX : Real.log (level / y) <= Real.log (level / x) :=
    log_div_antitoneOn (show 0 < level by linarith)
      (show x ∈ Ioi 0 by exact zero_lt_one.trans hxfacts.1)
      (show y ∈ Ioi 0 by exact zero_lt_one.trans hyfacts.1) hxy
  unfold dimensionOneRosserPlusRawFirstWeight
  exact div_le_div₀ (dimensionOneRosserModelMinusRaw_nonneg _) hnumXY
    hyfacts.2.2.1 hdenYX

theorem dimensionOneRosserPlusRawFirstWeight_properties
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 3 <= s) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserPlusRawFirstWeight level x) ∧
      ContinuousOn (dimensionOneRosserPlusRawFirstWeight level)
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn (dimensionOneRosserPlusRawFirstWeight level)
        (Icc (level ^ (1 / s0)) z) := by
  exact ⟨plus_raw_first_weight_nonneg hlevel hz hs hss0 hcutoff hsLower,
    plus_raw_first_weight_continuousOn hlevel hz hs hss0 hcutoff hsLower,
    plus_raw_first_weight_monotoneOn hlevel hz hs hss0 hcutoff hsLower⟩

private theorem minus_raw_first_weight_nonneg
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 2 <= s) :
    ∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserMinusRawFirstWeight level x := by
  intro x hx
  have hfacts := raw_source_weight_point_facts hlevel hz hs hss0 hcutoff
    hsLower hx
  unfold dimensionOneRosserMinusRawFirstWeight
  exact div_nonneg (dimensionOneRosserModelPlusRaw_nonneg _) hfacts.2.2.1.le

private theorem minus_raw_first_weight_continuousOn
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 2 <= s) :
    ContinuousOn (dimensionOneRosserMinusRawFirstWeight level)
      (Icc (level ^ (1 / s0)) z) := by
  have hargCont : ContinuousOn (buchstabArgument level)
      (Icc (level ^ (1 / s0)) z) :=
    (continuousOn_buchstabArgument level).mono (by
      intro x hx
      exact (raw_source_weight_point_facts hlevel hz hs hss0 hcutoff
        hsLower hx).1)
  have hargMaps : MapsTo (buchstabArgument level)
      (Icc (level ^ (1 / s0)) z) (Ici 1) := by
    intro x hx
    have hrange := (raw_source_weight_point_facts hlevel hz hs hss0
      hcutoff hsLower hx).2.2.2
    change 1 <= buchstabArgument level x
    linarith [hrange.1]
  have hnum : ContinuousOn
      (fun x => dimensionOneRosserModelPlusRaw (buchstabArgument level x))
      (Icc (level ^ (1 / s0)) z) := by
    change ContinuousOn
      (dimensionOneRosserModelPlusRaw ∘ buchstabArgument level)
      (Icc (level ^ (1 / s0)) z)
    exact continuousOn_dimensionOneRosserModelPlusRaw_Ici_one.comp
      hargCont hargMaps
  unfold dimensionOneRosserMinusRawFirstWeight
  apply hnum.div
    (raw_continuousOn_log_level_div hlevel hz hs hss0 hcutoff hsLower)
  intro x hx
  exact (raw_source_weight_point_facts hlevel hz hs hss0 hcutoff
    hsLower hx).2.2.1.ne'

private theorem minus_raw_first_weight_monotoneOn
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 2 <= s) :
    MonotoneOn (dimensionOneRosserMinusRawFirstWeight level)
      (Icc (level ^ (1 / s0)) z) := by
  intro x hx y hy hxy
  have hxfacts := raw_source_weight_point_facts hlevel hz hs hss0 hcutoff
    hsLower hx
  have hyfacts := raw_source_weight_point_facts hlevel hz hs hss0 hcutoff
    hsLower hy
  have hargXY : buchstabArgument level y <= buchstabArgument level x :=
    buchstabArgument_antitoneOn (show 1 < level by linarith)
      hxfacts.1 hyfacts.1 hxy
  have hnumXY :
      dimensionOneRosserModelPlusRaw (buchstabArgument level x) <=
        dimensionOneRosserModelPlusRaw (buchstabArgument level y) :=
    dimensionOneRosserModelPlusRaw_antitoneOn_Ici_one
      (show buchstabArgument level y ∈ Ici 1 by
        change 1 <= buchstabArgument level y
        linarith [hyfacts.2.2.2.1])
      (show buchstabArgument level x ∈ Ici 1 by
        change 1 <= buchstabArgument level x
        linarith [hxfacts.2.2.2.1]) hargXY
  have hdenYX : Real.log (level / y) <= Real.log (level / x) :=
    log_div_antitoneOn (show 0 < level by linarith)
      (show x ∈ Ioi 0 by exact zero_lt_one.trans hxfacts.1)
      (show y ∈ Ioi 0 by exact zero_lt_one.trans hyfacts.1) hxy
  unfold dimensionOneRosserMinusRawFirstWeight
  exact div_le_div₀ (dimensionOneRosserModelPlusRaw_nonneg _) hnumXY
    hyfacts.2.2.1 hdenYX

theorem dimensionOneRosserMinusRawFirstWeight_properties
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 2 <= s) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserMinusRawFirstWeight level x) ∧
      ContinuousOn (dimensionOneRosserMinusRawFirstWeight level)
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn (dimensionOneRosserMinusRawFirstWeight level)
        (Icc (level ^ (1 / s0)) z) := by
  exact ⟨minus_raw_first_weight_nonneg hlevel hz hs hss0 hcutoff hsLower,
    minus_raw_first_weight_continuousOn hlevel hz hs hss0 hcutoff hsLower,
    minus_raw_first_weight_monotoneOn hlevel hz hs hss0 hcutoff hsLower⟩

end PrimesRestrictedDigits
