import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The derivative of Buchstab's function

This file recovers the corrected delay derivative from Eq. (7.39) and proves
the elementary derivative bound from `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 7,
p. 216.
-/

open MeasureTheory

namespace PrimesRestrictedDigits

/-- The product form of the Buchstab delay equation, Eq. (7.38). -/
theorem hasDerivAt_mul_buchstabFunction
    {u : Real} (hu : 2 < u) :
    HasDerivAt
      (fun t : Real => t * buchstabFunction t)
      (buchstabFunction (u - 1)) u := by
  have hendpoint : (1 : Real) < u - 1 := by linarith
  have hcontIoi : ContinuousOn buchstabFunction (Set.Ioi 1) :=
    continuousOn_buchstabFunction.mono Set.Ioi_subset_Ici_self
  have hcont : ContinuousAt buchstabFunction (u - 1) :=
    continuousOn_buchstabFunction.continuousAt (Ici_mem_nhds hendpoint)
  have hint : IntervalIntegrable buchstabFunction volume 1 (u - 1) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_buchstabFunction.mono
    intro v hv
    rw [Set.uIcc_of_le hendpoint.le] at hv
    exact hv.1
  have hmeas : StronglyMeasurableAtFilter buchstabFunction
      (nhds (u - 1)) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hcontIoi _ hendpoint
  have hFTC := intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  have hshift : HasDerivAt (fun t : Real => t - 1) 1 u :=
    (hasDerivAt_id u).sub_const 1
  have hRhs : HasDerivAt
      (fun t : Real => 1 + ∫ v in (1 : Real)..t - 1, buchstabFunction v)
      (buchstabFunction (u - 1)) u := by
    simpa only [Function.comp_apply, mul_one] using
      (hFTC.comp u hshift).const_add 1
  have heq : (fun t : Real => t * buchstabFunction t) =ᶠ[nhds u]
      fun t => 1 + ∫ v in (1 : Real)..t - 1, buchstabFunction v := by
    filter_upwards [Ioi_mem_nhds hu] with t ht
    exact mul_buchstabFunction_eq ht.le
  exact hRhs.congr_of_eventuallyEq heq

/-- The corrected solved form of the Buchstab derivative. -/
theorem hasDerivAt_buchstabFunction
    {u : Real} (hu : 2 < u) :
    HasDerivAt buchstabFunction
      ((buchstabFunction (u - 1) - buchstabFunction u) / u) u := by
  have hu0 : 0 < u := by linarith
  have hquot : HasDerivAt
      (fun t : Real => (t * buchstabFunction t) / t)
      ((buchstabFunction (u - 1) * u - (u * buchstabFunction u) * 1) /
        u ^ 2) u := by
    simpa only [id_eq] using
      (hasDerivAt_mul_buchstabFunction hu).fun_div
        (hasDerivAt_id u) hu0.ne'
  have hcoeff :
      (buchstabFunction (u - 1) * u - (u * buchstabFunction u) * 1) /
          u ^ 2 =
        (buchstabFunction (u - 1) - buchstabFunction u) / u := by
    field_simp
  have hquot' : HasDerivAt
      (fun t : Real => (t * buchstabFunction t) / t)
      ((buchstabFunction (u - 1) - buchstabFunction u) / u) u := by
    rw [← hcoeff]
    exact hquot
  have heq : buchstabFunction =ᶠ[nhds u]
      fun t : Real => (t * buchstabFunction t) / t := by
    filter_upwards [Ioi_mem_nhds hu0] with t ht
    change (0 : Real) < t at ht
    calc
      buchstabFunction t = buchstabFunction t * t / t :=
        (mul_div_cancel_right₀ _ ht.ne').symm
      _ = t * buchstabFunction t / t := by rw [mul_comm]
  exact hquot'.congr_of_eventuallyEq heq

theorem deriv_buchstabFunction
    {u : Real} (hu : 2 < u) :
    deriv buchstabFunction u =
      (buchstabFunction (u - 1) - buchstabFunction u) / u :=
  (hasDerivAt_buchstabFunction hu).deriv

theorem abs_deriv_buchstabFunction_le
    {u : Real} (hu : 2 < u) :
    |deriv buchstabFunction u| <= 1 / (2 * u) := by
  have hu0 : 0 < u := by linarith
  have hBounds := buchstabFunction_mem_Icc (by linarith : (1 : Real) <= u)
  have hPrev :=
    buchstabFunction_mem_Icc (by linarith : (1 : Real) <= u - 1)
  have hdiff : |buchstabFunction (u - 1) - buchstabFunction u| <=
      (1 / 2 : Real) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hBounds.1, hBounds.2, hPrev.1, hPrev.2]
  rw [deriv_buchstabFunction hu, abs_div, abs_of_pos hu0]
  calc
    |buchstabFunction (u - 1) - buchstabFunction u| / u <=
        (1 / 2 : Real) / u :=
      (div_le_div_iff_of_pos_right hu0).2 hdiff
    _ = 1 / (2 * u) := by field_simp

end PrimesRestrictedDigits
