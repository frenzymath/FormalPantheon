import PrimesRestrictedDigits.BasicEstimates.BuchstabSlab
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The main integral in the Buchstab induction

This file verifies the change of variables and Eq. (7.39) evaluation following
Eq. (7.45) in `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 7, p. 218.
-/

open MeasureTheory Set
open scoped Interval Topology

namespace PrimesRestrictedDigits

private lemma integral_buchstabFunction_slab_eq
    {m : Nat} {u : Real} (hm : 2 ≤ m) (hmu : (m : Real) ≤ u) :
    (∫ v in ((m : Real) - 1)..(u - 1), buchstabFunction v) =
      u * buchstabFunction u -
        (m : Real) * buchstabFunction (m : Real) := by
  have hmreal : (2 : Real) ≤ m := by exact_mod_cast hm
  have hu : 2 ≤ u := hmreal.trans hmu
  have hcont_u : ContinuousOn buchstabFunction (Set.uIcc 1 (u - 1)) := by
    apply continuousOn_buchstabFunction.mono
    intro v hv
    rw [Set.uIcc_of_le (by linarith : (1 : Real) ≤ u - 1)] at hv
    exact hv.1
  have hcont_m : ContinuousOn buchstabFunction
      (Set.uIcc 1 ((m : Real) - 1)) := by
    apply continuousOn_buchstabFunction.mono
    intro v hv
    rw [Set.uIcc_of_le (by linarith : (1 : Real) ≤ m - 1)] at hv
    exact hv.1
  have hint_u : IntervalIntegrable buchstabFunction volume 1 (u - 1) :=
    hcont_u.intervalIntegrable
  have hint_m : IntervalIntegrable buchstabFunction volume 1 ((m : Real) - 1) :=
    hcont_m.intervalIntegrable
  have hsplit := intervalIntegral.integral_interval_sub_left hint_u hint_m
  have hu_eq := mul_buchstabFunction_eq hu
  have hm_eq := mul_buchstabFunction_eq hmreal
  calc
    (∫ v in ((m : Real) - 1)..(u - 1), buchstabFunction v) =
        (∫ v in (1 : Real)..u - 1, buchstabFunction v) -
          ∫ v in (1 : Real)..(m : Real) - 1, buchstabFunction v :=
      hsplit.symm
    _ = u * buchstabFunction u -
        (m : Real) * buchstabFunction (m : Real) := by
      rw [hu_eq, hm_eq]
      ring

/-- The decreasing logarithmic argument transforms the main prime-weight
integral into the source Buchstab integral. -/
theorem integral_buchstabPrimeWeight_div_log_eq_buchstabIntegral
    {m : Nat} {x u : Real} (hx : 1 < x) (hm : 2 ≤ m)
    (hmu : (m : Real) ≤ u) :
    (∫ t in (x ^ (1 / u))..(x ^ (1 / (m : Real))),
      buchstabPrimeWeight x t / Real.log t) =
        x / Real.log x *
          ∫ v in ((m : Real) - 1)..(u - 1), buchstabFunction v := by
  let a := x ^ (1 / u)
  let b := x ^ (1 / (m : Real))
  let g' : Real → Real := fun t =>
    -Real.log x / (t * Real.log t ^ 2)
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hm0 : 0 < (m : Real) := by positivity
  have hu0 : 0 < u := hm0.trans_le hmu
  have hab : a ≤ b := by
    apply Real.rpow_le_rpow_of_exponent_le hx.le
    exact one_div_le_one_div_of_le hm0 hmu
  have ha1 : 1 < a := by
    dsimp [a]
    exact Real.one_lt_rpow hx (by positivity)
  have ht1 : ∀ t ∈ Set.uIcc a b, 1 < t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ha1.trans_le ht.1
  have hg_deriv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (buchstabArgument x) (g' t) t := by
    intro t ht
    exact hasDerivAt_buchstabArgument (ht1 t ht)
  have hlog : ContinuousOn Real.log (Set.uIcc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (zero_lt_one.trans (ht1 t ht))
  have hden : ∀ t ∈ Set.uIcc a b, t * Real.log t ^ 2 ≠ 0 := by
    intro t ht
    exact mul_ne_zero (ne_of_gt (zero_lt_one.trans (ht1 t ht)))
      (pow_ne_zero _ (ne_of_gt (Real.log_pos (ht1 t ht))))
  have hg'_cont : ContinuousOn g' (Set.uIcc a b) := by
    dsimp [g']
    exact continuousOn_const.div
      (continuousOn_id.mul (hlog.pow 2)) hden
  have homega : ContinuousOn buchstabFunction
      (buchstabArgument x '' Set.uIcc a b) := by
    apply continuousOn_buchstabFunction.mono
    intro v hv
    rcases hv with ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le hab] at ht
    have hrange := buchstabArgument_mem_Icc_powerInterval
      hx (by omega) hmu ht
    have hmreal : (2 : Real) ≤ m := by exact_mod_cast hm
    exact by
      change (1 : Real) ≤ buchstabArgument x t
      linarith [hrange.1]
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (f := buchstabArgument x) (f' := g') (g := buchstabFunction)
    hg_deriv hg'_cont homega
  have harg_a : buchstabArgument x a = u - 1 := by
    dsimp [a, buchstabArgument]
    rw [Real.log_rpow hx0]
    field_simp
  have harg_b : buchstabArgument x b = (m : Real) - 1 := by
    dsimp [b, buchstabArgument]
    rw [Real.log_rpow hx0]
    field_simp
  have hintegrand :
      (∫ t in a..b, buchstabPrimeWeight x t / Real.log t) =
        ∫ t in a..b,
          (-x / Real.log x) *
            ((buchstabFunction ∘ buchstabArgument x) t * g' t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht1' := ht1 t ht
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht1')
    have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1')
    dsimp [g', Function.comp_apply]
    unfold buchstabPrimeWeight
    field_simp [hlogx.ne', hlogt, ht0]
  change (∫ t in a..b, buchstabPrimeWeight x t / Real.log t) = _
  calc
    (∫ t in a..b, buchstabPrimeWeight x t / Real.log t) =
        ∫ t in a..b,
          (-x / Real.log x) *
            ((buchstabFunction ∘ buchstabArgument x) t * g' t) :=
      hintegrand
    _ = (-x / Real.log x) *
        ∫ t in a..b,
          (buchstabFunction ∘ buchstabArgument x) t * g' t := by
      rw [intervalIntegral.integral_const_mul]
    _ = (-x / Real.log x) *
        ∫ v in (u - 1)..((m : Real) - 1), buchstabFunction v := by
      rw [hsubst, harg_a, harg_b]
    _ = x / Real.log x *
        ∫ v in ((m : Real) - 1)..(u - 1), buchstabFunction v := by
      rw [intervalIntegral.integral_symm]
      ring

/-- Eq. (7.39) evaluates the transformed main integral by its endpoints. -/
theorem integral_buchstabPrimeWeight_div_log_eq_buchstabDifference
    {m : Nat} {x u : Real} (hx : 1 < x) (hm : 2 ≤ m)
    (hmu : (m : Real) ≤ u) :
    (∫ t in (x ^ (1 / u))..(x ^ (1 / (m : Real))),
      buchstabPrimeWeight x t / Real.log t) =
        x / Real.log x *
          (u * buchstabFunction u -
            (m : Real) * buchstabFunction (m : Real)) := by
  rw [integral_buchstabPrimeWeight_div_log_eq_buchstabIntegral hx hm hmu,
    integral_buchstabFunction_slab_eq hm hmu]

end PrimesRestrictedDigits
