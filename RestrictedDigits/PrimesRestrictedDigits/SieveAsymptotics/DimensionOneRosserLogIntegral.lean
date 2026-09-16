import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Generic logarithmic integral for dimension-one Rosser weights

This file isolates the decreasing Buchstab-coordinate substitution used by the first
transformed recurrence term. See `IWANIEC-ROSSER-SIEVE-1980`, Section 8, Eqs. (8.8)--(8.9).
-/

open MeasureTheory Set
open scoped Interval Topology

namespace PrimesRestrictedDigits

/-- The decreasing Buchstab coordinate transforms a continuous numerator,
with the logarithmic Jacobian and reversed endpoints made explicit. -/
theorem log_mul_integral_buchstabWeight_eq
    {F : Real -> Real} {level w z s s0 lower : Real}
    (hlevel : 0 < level) (hw : 1 < w) (hwz : w <= z)
    (hlower : 0 < lower)
    (harg : ∀ x ∈ Icc w z, lower <= buchstabArgument level x)
    (hargw : buchstabArgument level w = s0 - 1)
    (hargz : buchstabArgument level z = s - 1)
    (hF : ContinuousOn F (Ici lower)) :
    Real.log level *
        (∫ x in w..z,
          (F (buchstabArgument level x) / Real.log (level / x)) /
            (x * Real.log x)) =
      ∫ t in (s - 1)..(s0 - 1), F t / t := by
  let derivative : Real -> Real := fun x =>
    -Real.log level / (x * Real.log x ^ 2)
  let G : Real -> Real := fun t => F t / t
  have huIcc : uIcc w z = Icc w z := uIcc_of_le hwz
  have hx1 : ∀ x ∈ uIcc w z, 1 < x := by
    intro x hx
    rw [huIcc] at hx
    exact hw.trans_le hx.1
  have hderiv : ∀ x ∈ uIcc w z,
      HasDerivAt (buchstabArgument level) (derivative x) x := by
    intro x hx
    exact hasDerivAt_buchstabArgument (hx1 x hx)
  have hlog : ContinuousOn Real.log (uIcc w z) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (zero_lt_one.trans (hx1 x hx))
  have hden : ∀ x ∈ uIcc w z, x * Real.log x ^ 2 ≠ 0 := by
    intro x hx
    exact mul_ne_zero (ne_of_gt (zero_lt_one.trans (hx1 x hx)))
      (pow_ne_zero _ (ne_of_gt (Real.log_pos (hx1 x hx))))
  have hderivCont : ContinuousOn derivative (uIcc w z) := by
    dsimp [derivative]
    exact continuousOn_const.div
      (continuousOn_id.mul (hlog.pow 2)) hden
  have hGbase : ContinuousOn G (Ici lower) := by
    dsimp [G]
    exact hF.div continuousOn_id (fun x hx => by
      simp only [mem_Ici] at hx
      linarith)
  have hG : ContinuousOn G
      (buchstabArgument level '' uIcc w z) := by
    apply hGbase.mono
    intro u hu
    rcases hu with ⟨x, hx, rfl⟩
    apply harg x
    rwa [huIcc] at hx
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (f := buchstabArgument level) (f' := derivative) (g := G)
    hderiv hderivCont hG
  have hintegrand : ∀ x ∈ uIcc w z,
      Real.log level *
          ((F (buchstabArgument level x) / Real.log (level / x)) /
            (x * Real.log x)) =
        -((G ∘ buchstabArgument level) x * derivative x) := by
    intro x hx
    have hx1' := hx1 x hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1')
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1')
    have hargLower : lower <= buchstabArgument level x := by
      apply harg x
      rwa [huIcc] at hx
    have harg0 : buchstabArgument level x ≠ 0 := by linarith
    have hlogdiv := log_div_eq_buchstabArgument_mul_log hlevel hx1'
    have hlogdiv0 : Real.log (level / x) ≠ 0 := by
      rw [hlogdiv]
      exact mul_ne_zero harg0 hlogx
    dsimp [G, derivative, Function.comp_apply]
    rw [hlogdiv]
    field_simp
  calc
    Real.log level *
        (∫ x in w..z,
          (F (buchstabArgument level x) / Real.log (level / x)) /
            (x * Real.log x)) =
        ∫ x in w..z,
          Real.log level *
            ((F (buchstabArgument level x) / Real.log (level / x)) /
              (x * Real.log x)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ x in w..z,
        -((G ∘ buchstabArgument level) x * derivative x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hintegrand x hx
    _ = -(∫ x in w..z,
        (G ∘ buchstabArgument level) x * derivative x) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ t in buchstabArgument level w..
        buchstabArgument level z, G t) := by
      rw [hsubst]
    _ = ∫ t in buchstabArgument level z..
        buchstabArgument level w, G t := by
      exact (intervalIntegral.integral_symm
        (f := G) (a := buchstabArgument level w)
          (b := buchstabArgument level z)).symm
    _ = ∫ t in (s - 1)..(s0 - 1), F t / t := by
      rw [hargz, hargw]

end PrimesRestrictedDigits
