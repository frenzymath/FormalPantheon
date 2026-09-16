import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondWeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Logarithmic substitution for the second dimension-one Rosser weight

This file proves the exact change of variable used before Iwaniec's Eq. (8.12). See
`IWANIEC-ROSSER-SIEVE-1980`, Eqs. (8.10)--(8.12).
-/

open MeasureTheory Set
open scoped Interval Topology

namespace PrimesRestrictedDigits

private theorem integral_secondWeight_div_eq
    (kernel : Real -> Real -> Real)
    (hkernel : forall {L : Real}, 0 < L ->
      ContinuousOn (kernel L) (Ioi 1))
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsTwo : 2 <= s) (hss0 : s < s0) :
    (∫ x in (level ^ (1 / s0))..z,
        kernel (Real.log level) (buchstabArgument level x + 1) /
          (x * Real.log x)) =
      ∫ t in s..s0, kernel (Real.log level) t / t := by
  let w : Real := level ^ (1 / s0)
  let coord : Real -> Real := fun x => buchstabArgument level x + 1
  let derivative : Real -> Real := fun x =>
    -Real.log level / (x * Real.log x ^ 2)
  let G : Real -> Real := fun t => kernel (Real.log level) t / t
  have hlevelOne : 1 < level := by linarith
  have hzOne : 1 < z := by linarith
  have hL : 0 < Real.log level := Real.log_pos hlevelOne
  have hsPos : 0 < s := by linarith
  have hsOne : 1 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hwOne : 1 < w := by
    dsimp [w]
    exact Real.one_lt_rpow hlevelOne (one_div_pos.mpr hs0Pos)
  have hwz : w <= z := by
    dsimp [w]
    exact (dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 hsTwo).le
  have huIcc : uIcc w z = Icc w z := uIcc_of_le hwz
  have hxOne : forall x : Real, x ∈ uIcc w z -> 1 < x := by
    intro x hx
    rw [huIcc] at hx
    exact hwOne.trans_le hx.1
  have hderiv : forall x : Real, x ∈ uIcc w z ->
      HasDerivAt coord (derivative x) x := by
    intro x hx
    dsimp [coord, derivative]
    convert (hasDerivAt_buchstabArgument (x := level) (t := x)
      (hxOne x hx)).add_const 1 using 1
  have hlog : ContinuousOn Real.log (uIcc w z) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (zero_lt_one.trans (hxOne x hx))
  have hden : forall x : Real, x ∈ uIcc w z ->
      x * Real.log x ^ 2 ≠ 0 := by
    intro x hx
    exact mul_ne_zero (ne_of_gt (zero_lt_one.trans (hxOne x hx)))
      (pow_ne_zero _ (ne_of_gt (Real.log_pos (hxOne x hx))))
  have hderivCont : ContinuousOn derivative (uIcc w z) := by
    dsimp [derivative]
    exact continuousOn_const.div
      (continuousOn_id.mul (hlog.pow 2)) hden
  have hcoordMaps : MapsTo coord (uIcc w z) (Icc s s0) := by
    intro x hx
    rw [huIcc] at hx
    have hrange := buchstabArgument_mem_Icc_realEndpoints
      hlevelOne hzOne hsPos hs hss0 hx
    dsimp [coord]
    constructor <;> linarith [hrange.1, hrange.2]
  have hG : ContinuousOn G (coord '' uIcc w z) := by
    have hkernel' : ContinuousOn (kernel (Real.log level)) (Icc s s0) :=
      (hkernel hL).mono (by
        intro t ht
        change 1 < t
        exact hsOne.trans_le ht.1)
    have hGbase : ContinuousOn G (Icc s s0) := by
      dsimp [G]
      apply hkernel'.div continuousOn_id
      intro t ht
      exact ne_of_gt (hsPos.trans_le ht.1)
    exact hGbase.mono (by
      intro t ht
      rcases ht with ⟨x, hx, rfl⟩
      exact hcoordMaps hx)
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (f := coord) (f' := derivative) (g := G)
    hderiv hderivCont hG
  have hintegrand : forall x : Real, x ∈ uIcc w z ->
      kernel (Real.log level) (buchstabArgument level x + 1) /
          (x * Real.log x) =
        -((G ∘ coord) x * derivative x) := by
    intro x hx
    have hxOne' := hxOne x hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hxOne')
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hxOne')
    dsimp [G, coord, derivative, Function.comp_apply]
    rw [show buchstabArgument level x + 1 =
      Real.log level / Real.log x by
        dsimp [buchstabArgument]
        ring]
    field_simp [hL.ne', hx0, hlogx]
  have hcoordw : coord w = s0 := by
    dsimp [coord, w]
    rw [buchstabArgument_rpow_one_div hlevelOne hs0Pos]
    ring
  have hcoordz : coord z = s := by
    dsimp [coord]
    rw [buchstabArgument_eq_sub_one_of_log_ratio hs]
    ring
  change (∫ x in w..z,
      kernel (Real.log level) (buchstabArgument level x + 1) /
        (x * Real.log x)) = _
  calc
    (∫ x in w..z,
        kernel (Real.log level) (buchstabArgument level x + 1) /
          (x * Real.log x)) =
        ∫ x in w..z, -((G ∘ coord) x * derivative x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hintegrand x hx
    _ = -(∫ x in w..z, (G ∘ coord) x * derivative x) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ t in coord w..coord z, G t) := by rw [hsubst]
    _ = ∫ t in coord z..coord w, G t := by
      exact (intervalIntegral.integral_symm
        (f := G) (a := coord w) (b := coord z)).symm
    _ = ∫ t in s..s0, kernel (Real.log level) t / t := by
      rw [hcoordz, hcoordw]

/-- The target-plus second weight transforms to its source kernel on the
natural second-recurrence domain. -/
theorem integral_dimensionOneRosserPlusSecondWeight_div_eq_of_two_le
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsTwo : 2 <= s) (hss0 : s < s0) :
    (∫ x in (level ^ (1 / s0))..z,
        dimensionOneRosserPlusSecondWeight level x /
          (x * Real.log x)) =
      ∫ t in s..s0,
        dimensionOneRosserPlusSecondKernel (Real.log level) t / t := by
  exact integral_secondWeight_div_eq
    dimensionOneRosserPlusSecondKernel
    dimensionOneRosserPlusSecondKernel_continuousOn
    hlevel hz hs hsTwo hss0

/-- Large-domain compatibility form of the target-plus log substitution. -/
theorem integral_dimensionOneRosserPlusSecondWeight_div_eq
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0) :
    (∫ x in (level ^ (1 / s0))..z,
        dimensionOneRosserPlusSecondWeight level x /
          (x * Real.log x)) =
      ∫ t in s..s0,
        dimensionOneRosserPlusSecondKernel (Real.log level) t / t := by
  apply integral_dimensionOneRosserPlusSecondWeight_div_eq_of_two_le
    hlevel hz hs _ hss0
  have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
  linarith

/-- The target-minus second weight transforms to its source kernel on the
natural second-recurrence domain. -/
theorem integral_dimensionOneRosserMinusSecondWeight_div_eq_of_two_le
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsTwo : 2 <= s) (hss0 : s < s0) :
    (∫ x in (level ^ (1 / s0))..z,
        dimensionOneRosserMinusSecondWeight level x /
          (x * Real.log x)) =
      ∫ t in s..s0,
        dimensionOneRosserMinusSecondKernel (Real.log level) t / t := by
  exact integral_secondWeight_div_eq
    dimensionOneRosserMinusSecondKernel
    dimensionOneRosserMinusSecondKernel_continuousOn
    hlevel hz hs hsTwo hss0

/-- Large-domain compatibility form of the target-minus log substitution. -/
theorem integral_dimensionOneRosserMinusSecondWeight_div_eq
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0) :
    (∫ x in (level ^ (1 / s0))..z,
        dimensionOneRosserMinusSecondWeight level x /
          (x * Real.log x)) =
      ∫ t in s..s0,
        dimensionOneRosserMinusSecondKernel (Real.log level) t / t := by
  apply integral_dimensionOneRosserMinusSecondWeight_div_eq_of_two_le
    hlevel hz hs _ hss0
  have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
  linarith

end PrimesRestrictedDigits
