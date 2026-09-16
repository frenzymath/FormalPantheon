import PrimesRestrictedDigits.BasicEstimates.BuchstabSlab
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelPartialSums

/-!
# Logarithmic coordinates for the first dimension-one Rosser weight

This file supplies the coordinate geometry and weight regularity used in the first transformed
recurrence term of Iwaniec's Section 8. See `IWANIEC-ROSSER-SIEVE-1980`, Eqs. (8.8)--(8.9).
-/

open Set

namespace PrimesRestrictedDigits

/-- The source logarithmic coordinate agrees with the existing Buchstab
coordinate. -/
theorem log_div_log_eq_buchstabArgument
    {level x : Real} (hlevel : 0 < level) (hx : 1 < x) :
    Real.log (level / x) / Real.log x = buchstabArgument level x := by
  have hx0 : x ≠ 0 := by linarith
  have hlogx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [Real.log_div hlevel.ne' hx0]
  unfold buchstabArgument
  field_simp

/-- The logarithm in the first Rosser weight factors through the Buchstab
coordinate. -/
theorem log_div_eq_buchstabArgument_mul_log
    {level x : Real} (hlevel : 0 < level) (hx : 1 < x) :
    Real.log (level / x) = buchstabArgument level x * Real.log x := by
  have hlogx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have h := log_div_log_eq_buchstabArgument hlevel hx
  apply (div_eq_iff hlogx).mp
  simpa only [mul_comm] using h

/-- The logarithm of a positive real power with reciprocal exponent. -/
theorem log_rpow_one_div {level u : Real} (hlevel : 0 < level) :
    Real.log (level ^ (1 / u)) = Real.log level / u := by
  rw [Real.log_rpow hlevel]
  ring

/-- A reciprocal power endpoint has the expected Buchstab coordinate. -/
theorem buchstabArgument_rpow_one_div
    {level u : Real} (hlevel : 1 < level) (hu : 0 < u) :
    buchstabArgument level (level ^ (1 / u)) = u - 1 := by
  have hlevelPos : 0 < level := by linarith
  have hlogLevel : Real.log level ≠ 0 := (Real.log_pos hlevel).ne'
  have hu0 : u ≠ 0 := hu.ne'
  unfold buchstabArgument
  rw [log_rpow_one_div hlevelPos]
  field_simp

/-- A named log-ratio parameter is the Buchstab coordinate shifted by one. -/
theorem buchstabArgument_eq_sub_one_of_log_ratio
    {level z s : Real} (hs : s = Real.log level / Real.log z) :
    buchstabArgument level z = s - 1 := by
  unfold buchstabArgument
  rw [<- hs]

/-- For a fixed level above one, the Buchstab coordinate decreases on
arguments above one. -/
theorem buchstabArgument_antitoneOn {level : Real} (hlevel : 1 < level) :
    AntitoneOn (buchstabArgument level) (Ioi 1) := by
  intro x hx y hy hxy
  have hxOne : 1 < x := by exact hx
  have hyOne : 1 < y := by exact hy
  have hlogLevel : 0 <= Real.log level := (Real.log_pos hlevel).le
  have hlogx : 0 < Real.log x := Real.log_pos hxOne
  have hlogxy : Real.log x <= Real.log y :=
    Real.strictMonoOn_log.monotoneOn
      (show x ∈ Ioi 0 by exact zero_lt_one.trans hxOne)
      (show y ∈ Ioi 0 by exact zero_lt_one.trans hyOne) hxy
  unfold buchstabArgument
  exact sub_le_sub_right
    (div_le_div_of_nonneg_left hlogLevel hlogx hlogxy) 1

/-- The logarithmic denominator of the first Rosser weight decreases on the
positive half-line. -/
theorem log_div_antitoneOn {level : Real} (hlevel : 0 < level) :
    AntitoneOn (fun x : Real => Real.log (level / x)) (Ioi 0) := by
  intro x hx y hy hxy
  change Real.log (level / y) <= Real.log (level / x)
  rw [Real.log_div hlevel.ne' hy.ne', Real.log_div hlevel.ne' hx.ne']
  exact sub_le_sub_left (Real.log_le_log hx hxy) _

/-- The Buchstab coordinate is continuous on arguments above one. -/
theorem continuousOn_buchstabArgument (level : Real) :
    ContinuousOn (buchstabArgument level) (Ioi 1) := by
  intro x hx
  exact (hasDerivAt_buchstabArgument hx).continuousAt.continuousWithinAt

/-- The coordinate range on a power interval with real endpoints. This is
the real-parameter counterpart of `buchstabArgument_mem_Icc_powerInterval`.
-/
theorem buchstabArgument_mem_Icc_realPowerInterval
    {level lower upper x : Real} (hlevel : 1 < level)
    (hlower : 0 < lower) (hlu : lower <= upper)
    (hx : x ∈ Icc (level ^ (1 / upper))
      (level ^ (1 / lower))) :
    buchstabArgument level x ∈ Icc (lower - 1) (upper - 1) := by
  have hupper : 0 < upper := hlower.trans_le hlu
  have hleft : 1 < level ^ (1 / upper) :=
    Real.one_lt_rpow hlevel (one_div_pos.mpr hupper)
  have hright : 1 < level ^ (1 / lower) :=
    Real.one_lt_rpow hlevel (one_div_pos.mpr hlower)
  have hxOne : 1 < x := hleft.trans_le hx.1
  have hanti := buchstabArgument_antitoneOn hlevel
  constructor
  · rw [<- buchstabArgument_rpow_one_div hlevel hlower]
    exact hanti (by exact hxOne) (by exact hright) hx.2
  · rw [<- buchstabArgument_rpow_one_div hlevel hupper]
    exact hanti (by exact hleft) (by exact hxOne) hx.1

/-- The source interval maps to the exact reversed coordinate interval. -/
theorem buchstabArgument_mem_Icc_realEndpoints
    {level z s s0 x : Real} (hlevel : 1 < level) (hz : 1 < z)
    (hsPos : 0 < s) (hs : s = Real.log level / Real.log z)
    (hss0 : s < s0)
    (hx : x ∈ Icc (level ^ (1 / s0)) z) :
    buchstabArgument level x ∈ Icc (s - 1) (s0 - 1) := by
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hleft : 1 < level ^ (1 / s0) :=
    Real.one_lt_rpow hlevel (one_div_pos.mpr hs0Pos)
  have hxOne : 1 < x := hleft.trans_le hx.1
  have hanti := buchstabArgument_antitoneOn hlevel
  constructor
  · rw [<- buchstabArgument_eq_sub_one_of_log_ratio hs]
    exact hanti (by exact hxOne) (by exact hz) hx.2
  · rw [<- buchstabArgument_rpow_one_div hlevel hs0Pos]
    exact hanti (by exact hleft) (by exact hxOne) hx.1

/-- The reciprocal-power lower cutoff is strictly below `z` in the source
parameter regime. -/
theorem dimensionOneRosserFirstCutoff_lt
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hsLower : 2 <= s) :
    level ^ (1 / s0) < z := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogLevel : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hs0Pos : 0 < s0 := by linarith
  have hlogIdentity : s * Real.log z = Real.log level :=
    (eq_div_iff hlogz.ne').mp hs
  apply (Real.log_lt_log_iff
    (Real.rpow_pos_of_pos hlevelPos _) hzPos).mp
  rw [log_rpow_one_div hlevelPos, div_lt_iff₀ hs0Pos]
  nlinarith

/-- The first transformed weight for an upper target of rank `R`. -/
noncomputable def dimensionOneRosserPlusFirstWeight
    (R : Nat) (level x : Real) : Real :=
  dimensionOneRosserModelMinusPartialSum R
      (buchstabArgument level x) / Real.log (level / x)

/-- The first transformed weight for a lower target of rank `R+1`. -/
noncomputable def dimensionOneRosserMinusFirstWeight
    (R : Nat) (level x : Real) : Real :=
  dimensionOneRosserModelPlusPartialSum R
      (buchstabArgument level x) / Real.log (level / x)

private theorem source_z_lt_level
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

private theorem source_weight_point_facts
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
    (source_z_lt_level hlevel hz hs hsLower)
  have hratio : 1 < level / x := (one_lt_div (by linarith)).mpr hxLevel
  have hsPos : 0 < s := by linarith
  exact ⟨hxOne, hxLevel, Real.log_pos hratio,
    buchstabArgument_mem_Icc_realEndpoints hlevelOne hzOne hsPos hs hss0 hx⟩

private theorem continuousOn_log_level_div
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
    exact ne_of_gt (by linarith [(source_weight_point_facts hlevel hz hs hss0
      hcutoff hsLower hx).1])
  change ContinuousOn (Real.log ∘ fun x : Real => level / x)
    (Icc (level ^ (1 / s0)) z)
  apply Real.continuousOn_log.comp hdiv
  intro x hx
  exact ne_of_gt (div_pos (by linarith)
    (by linarith [(source_weight_point_facts hlevel hz hs hss0
      hcutoff hsLower hx).1]))

/-- The upper-target first weight is nonnegative on the complete source
interval, including the seam `s=3`. -/
theorem dimensionOneRosserPlusFirstWeight_nonneg
    (R : Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 3 <= s) :
    ∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserPlusFirstWeight R level x := by
  intro x hx
  have hfacts := source_weight_point_facts hlevel hz hs hss0 hcutoff
    (by linarith) hx
  unfold dimensionOneRosserPlusFirstWeight
  exact div_nonneg (dimensionOneRosserModelMinusPartialSum_nonneg _ _)
    hfacts.2.2.1.le

/-- The upper-target first weight is continuous on the complete source
interval. -/
theorem dimensionOneRosserPlusFirstWeight_continuousOn
    (R : Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 3 <= s) :
    ContinuousOn (dimensionOneRosserPlusFirstWeight R level)
      (Icc (level ^ (1 / s0)) z) := by
  have hargCont : ContinuousOn (buchstabArgument level)
      (Icc (level ^ (1 / s0)) z) :=
    (continuousOn_buchstabArgument level).mono (by
      intro x hx
      exact (source_weight_point_facts hlevel hz hs hss0 hcutoff
        (by linarith) hx).1)
  have hargMaps : MapsTo (buchstabArgument level)
      (Icc (level ^ (1 / s0)) z) (Ici 2) := by
    intro x hx
    exact (by
      have hrange := (source_weight_point_facts hlevel hz hs hss0
        hcutoff (by linarith) hx).2.2.2
      linarith [hrange.1] : 2 <= buchstabArgument level x)
  have hnum : ContinuousOn
      (fun x => dimensionOneRosserModelMinusPartialSum R
        (buchstabArgument level x)) (Icc (level ^ (1 / s0)) z) := by
    change ContinuousOn
      (dimensionOneRosserModelMinusPartialSum R ∘ buchstabArgument level)
      (Icc (level ^ (1 / s0)) z)
    exact (dimensionOneRosserModelMinusPartialSum_continuousOn R).comp
      hargCont hargMaps
  unfold dimensionOneRosserPlusFirstWeight
  apply hnum.div
    (continuousOn_log_level_div hlevel hz hs hss0 hcutoff (by linarith))
  intro x hx
  exact (source_weight_point_facts hlevel hz hs hss0 hcutoff
    (by linarith) hx).2.2.1.ne'

/-- The upper-target first weight is nondecreasing on the complete source
interval. -/
theorem dimensionOneRosserPlusFirstWeight_monotoneOn
    (R : Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 3 <= s) :
    MonotoneOn (dimensionOneRosserPlusFirstWeight R level)
      (Icc (level ^ (1 / s0)) z) := by
  intro x hx y hy hxy
  have hxfacts := source_weight_point_facts hlevel hz hs hss0 hcutoff
    (by linarith) hx
  have hyfacts := source_weight_point_facts hlevel hz hs hss0 hcutoff
    (by linarith) hy
  have hargAnti := buchstabArgument_antitoneOn (show 1 < level by linarith)
  have hargXY : buchstabArgument level y <= buchstabArgument level x :=
    hargAnti (by exact hxfacts.1) (by exact hyfacts.1) hxy
  have hnumXY :
      dimensionOneRosserModelMinusPartialSum R (buchstabArgument level x) <=
        dimensionOneRosserModelMinusPartialSum R
          (buchstabArgument level y) :=
    (dimensionOneRosserModelPartialSum_antitoneOn R).2
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
  unfold dimensionOneRosserPlusFirstWeight
  exact div_le_div₀
    (dimensionOneRosserModelMinusPartialSum_nonneg _ _) hnumXY
    hyfacts.2.2.1 hdenYX

/-- All three hypotheses needed by weighted density summation for the
upper-target first weight. -/
theorem dimensionOneRosserPlusFirstWeight_properties
    (R : Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 3 <= s) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserPlusFirstWeight R level x) ∧
      ContinuousOn (dimensionOneRosserPlusFirstWeight R level)
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn (dimensionOneRosserPlusFirstWeight R level)
        (Icc (level ^ (1 / s0)) z) := by
  exact ⟨dimensionOneRosserPlusFirstWeight_nonneg R hlevel hz hs hss0
      hcutoff hsLower,
    dimensionOneRosserPlusFirstWeight_continuousOn R hlevel hz hs hss0
      hcutoff hsLower,
    dimensionOneRosserPlusFirstWeight_monotoneOn R hlevel hz hs hss0
      hcutoff hsLower⟩

/-- The lower-target first weight is nonnegative on the complete source
interval, including the seam `s=2`. -/
theorem dimensionOneRosserMinusFirstWeight_nonneg
    (R : Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 2 <= s) :
    ∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserMinusFirstWeight R level x := by
  intro x hx
  have hfacts := source_weight_point_facts hlevel hz hs hss0 hcutoff
    hsLower hx
  unfold dimensionOneRosserMinusFirstWeight
  exact div_nonneg (dimensionOneRosserModelPlusPartialSum_nonneg _ _)
    hfacts.2.2.1.le

/-- The lower-target first weight is continuous on the complete source
interval. -/
theorem dimensionOneRosserMinusFirstWeight_continuousOn
    (R : Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 2 <= s) :
    ContinuousOn (dimensionOneRosserMinusFirstWeight R level)
      (Icc (level ^ (1 / s0)) z) := by
  have hargCont : ContinuousOn (buchstabArgument level)
      (Icc (level ^ (1 / s0)) z) :=
    (continuousOn_buchstabArgument level).mono (by
      intro x hx
      exact (source_weight_point_facts hlevel hz hs hss0 hcutoff
        hsLower hx).1)
  have hargMaps : MapsTo (buchstabArgument level)
      (Icc (level ^ (1 / s0)) z) (Ici 1) := by
    intro x hx
    change 1 <= buchstabArgument level x
    have hrange := (source_weight_point_facts hlevel hz hs hss0 hcutoff
      hsLower hx).2.2.2
    linarith [hrange.1]
  have hnum : ContinuousOn
      (fun x => dimensionOneRosserModelPlusPartialSum R
        (buchstabArgument level x)) (Icc (level ^ (1 / s0)) z) := by
    change ContinuousOn
      (dimensionOneRosserModelPlusPartialSum R ∘ buchstabArgument level)
      (Icc (level ^ (1 / s0)) z)
    exact (dimensionOneRosserModelPlusPartialSum_continuousOn R).comp
      hargCont hargMaps
  unfold dimensionOneRosserMinusFirstWeight
  apply hnum.div
    (continuousOn_log_level_div hlevel hz hs hss0 hcutoff hsLower)
  intro x hx
  exact (source_weight_point_facts hlevel hz hs hss0 hcutoff
    hsLower hx).2.2.1.ne'

/-- The lower-target first weight is nondecreasing on the complete source
interval. -/
theorem dimensionOneRosserMinusFirstWeight_monotoneOn
    (R : Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 2 <= s) :
    MonotoneOn (dimensionOneRosserMinusFirstWeight R level)
      (Icc (level ^ (1 / s0)) z) := by
  intro x hx y hy hxy
  have hxfacts := source_weight_point_facts hlevel hz hs hss0 hcutoff
    hsLower hx
  have hyfacts := source_weight_point_facts hlevel hz hs hss0 hcutoff
    hsLower hy
  have hargAnti := buchstabArgument_antitoneOn (show 1 < level by linarith)
  have hargXY : buchstabArgument level y <= buchstabArgument level x :=
    hargAnti (by exact hxfacts.1) (by exact hyfacts.1) hxy
  have hnumXY :
      dimensionOneRosserModelPlusPartialSum R (buchstabArgument level x) <=
        dimensionOneRosserModelPlusPartialSum R
          (buchstabArgument level y) :=
    (dimensionOneRosserModelPartialSum_antitoneOn R).1
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
  unfold dimensionOneRosserMinusFirstWeight
  exact div_le_div₀
    (dimensionOneRosserModelPlusPartialSum_nonneg _ _) hnumXY
    hyfacts.2.2.1 hdenYX

/-- All three hypotheses needed by weighted density summation for the
lower-target first weight. -/
theorem dimensionOneRosserMinusFirstWeight_properties
    (R : Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0)) (hsLower : 2 <= s) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserMinusFirstWeight R level x) ∧
      ContinuousOn (dimensionOneRosserMinusFirstWeight R level)
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn (dimensionOneRosserMinusFirstWeight R level)
        (Icc (level ^ (1 / s0)) z) := by
  exact ⟨dimensionOneRosserMinusFirstWeight_nonneg R hlevel hz hs hss0
      hcutoff hsLower,
    dimensionOneRosserMinusFirstWeight_continuousOn R hlevel hz hs hss0
      hcutoff hsLower,
    dimensionOneRosserMinusFirstWeight_monotoneOn R hlevel hz hs hss0
      hcutoff hsLower⟩

end PrimesRestrictedDigits
