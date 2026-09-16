import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogTransform

/-!
# Strict inner range in the dimension-one Rosser recurrence

The strict prime endpoint in Iwaniec's Eq. (8.8) maps to the open lower Buchstab-coordinate
endpoint.
-/

open Set

namespace PrimesRestrictedDigits

/-- For a level above one, the Buchstab coordinate is strictly decreasing on
arguments above one. -/
theorem buchstabArgument_strictAntiOn {level : Real} (hlevel : 1 < level) :
    StrictAntiOn (buchstabArgument level) (Ioi 1) := by
  intro x hx y _hy hxy
  have hlogLevel : 0 < Real.log level := Real.log_pos hlevel
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogxy : Real.log x < Real.log y :=
    Real.log_lt_log (zero_lt_one.trans hx) hxy
  unfold buchstabArgument
  exact sub_lt_sub_right
    (div_lt_div_of_pos_left hlogLevel hlogx hlogxy) 1

/-- The half-open source shell maps to the exact interval `(s-1,s0-1]`.
Strictness at the lower coordinate endpoint comes from the strict cutoff
`x<z`; the weak upper endpoint comes from the admitted point
`x=level^(1/s0)`. -/
theorem buchstabArgument_mem_Ioc_realEndpoints
    {level z s s0 x : Real} (hlevel : 1 < level) (hz : 1 < z)
    (hsPos : 0 < s) (hs : s = Real.log level / Real.log z)
    (hss0 : s < s0)
    (hx : x ∈ Ico (level ^ (1 / s0)) z) :
    buchstabArgument level x ∈ Ioc (s - 1) (s0 - 1) := by
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hleftOne : 1 < level ^ (1 / s0) :=
    Real.one_lt_rpow hlevel (one_div_pos.mpr hs0Pos)
  have hxOne : 1 < x := hleftOne.trans_le hx.1
  constructor
  · rw [<- buchstabArgument_eq_sub_one_of_log_ratio hs]
    exact buchstabArgument_strictAntiOn hlevel hxOne hz hx.2
  · rw [<- buchstabArgument_rpow_one_div hlevel hs0Pos]
    exact (buchstabArgument_strictAntiOn hlevel).antitoneOn
      hleftOne hxOne hx.1

/-- Literal log-ratio form of the strict inner coordinate range. -/
theorem log_div_log_mem_Ioc_realEndpoints
    {level z s s0 x : Real} (hlevel : 1 < level) (hz : 1 < z)
    (hsPos : 0 < s) (hs : s = Real.log level / Real.log z)
    (hss0 : s < s0)
    (hx : x ∈ Ico (level ^ (1 / s0)) z) :
    Real.log (level / x) / Real.log x ∈ Ioc (s - 1) (s0 - 1) := by
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hleftOne : 1 < level ^ (1 / s0) :=
    Real.one_lt_rpow hlevel (one_div_pos.mpr hs0Pos)
  have hxOne : 1 < x := hleftOne.trans_le hx.1
  rw [log_div_log_eq_buchstabArgument (by linarith : 0 < level) hxOne]
  exact buchstabArgument_mem_Ioc_realEndpoints
    hlevel hz hsPos hs hss0 hx

end PrimesRestrictedDigits
