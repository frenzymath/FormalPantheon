import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A finite Dirichlet sine-integral tail bound

This is the integration-by-parts estimate used in the proof of the truncated
Perron formula.  See `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5, Eq. (5.6), p. 139.
-/

open MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/-- The finite Dirichlet sine tail is bounded uniformly by twice its lower
endpoint's reciprocal. -/
theorem abs_dirichletSineIntegral_le_two_div
    {A B : Real} (hA : 0 < A) (hAB : A <= B) :
    abs (∫ u in A..B, Real.sinc u) <= 2 / A := by
  have hB : 0 < B := hA.trans_le hAB
  have hpos : forall x, x ∈ [[A, B]] -> 0 < x := by
    intro x hx
    exact hA.trans_le (uIcc_of_le hAB ▸ hx).1
  have hne : forall x, x ∈ [[A, B]] -> x ≠ 0 := fun x hx => (hpos x hx).ne'
  have hinv_deriv : forall x, x ∈ [[A, B]] ->
      HasDerivAt (fun y : Real => y⁻¹) (-(x ^ 2)⁻¹) x := by
    intro x hx
    exact hasDerivAt_inv (hne x hx)
  have hneg_cos_deriv : forall x, x ∈ [[A, B]] ->
      HasDerivAt (-Real.cos) (Real.sin x) x := by
    intro x _
    simpa only [neg_neg] using (Real.hasDerivAt_cos x).neg
  have hinv_sq_integrable :
      IntervalIntegrable (fun x : Real => -(x ^ 2)⁻¹) volume A B := by
    apply ContinuousOn.intervalIntegrable
    exact ((continuousOn_id.pow 2).inv₀ (fun x hx =>
      pow_ne_zero 2 (hne x hx))).neg
  have hsin_integrable :
      IntervalIntegrable (fun x : Real => Real.sin x) volume A B :=
    Real.continuous_sin.intervalIntegrable A B
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hinv_deriv hneg_cos_deriv hinv_sq_integrable hsin_integrable
  have hsinc_eq :
      (∫ u in A..B, Real.sinc u) =
        ∫ u in A..B, u⁻¹ * Real.sin u := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Real.sinc_of_ne_zero (hne x hx)]
    ring
  have hresidual_eq :
      (∫ u in A..B, -(u ^ 2)⁻¹ * (-Real.cos) u) =
        ∫ u in A..B, Real.cos u / u ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Pi.neg_apply, neg_mul_neg, div_eq_mul_inv]
    ring
  have hidentity :
      (∫ u in A..B, Real.sinc u) =
        Real.cos A / A - Real.cos B / B -
          ∫ u in A..B, Real.cos u / u ^ 2 := by
    rw [hsinc_eq, hparts, hresidual_eq]
    simp only [Pi.neg_apply]
    ring
  have hA_endpoint : abs (Real.cos A / A) <= 1 / A := by
    rw [abs_div, abs_of_pos hA]
    exact (div_le_div_iff_of_pos_right hA).2 (Real.abs_cos_le_one A)
  have hB_endpoint : abs (Real.cos B / B) <= 1 / B := by
    rw [abs_div, abs_of_pos hB]
    exact (div_le_div_iff_of_pos_right hB).2 (Real.abs_cos_le_one B)
  have hone_div_sq_integrable :
      IntervalIntegrable (fun x : Real => 1 / x ^ 2) volume A B := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (continuousOn_id.pow 2) fun x hx =>
      pow_ne_zero 2 (hne x hx)
  have hcos_div_sq_integrable :
      IntervalIntegrable (fun x : Real => abs (Real.cos x / x ^ 2)) volume A B := by
    apply ContinuousOn.intervalIntegrable
    exact ((Real.continuous_cos.continuousOn.div (continuousOn_id.pow 2) fun x hx =>
      pow_ne_zero 2 (hne x hx)).abs)
  have hintegral_bound :
      abs (∫ u in A..B, Real.cos u / u ^ 2) <=
        ∫ u in A..B, 1 / u ^ 2 := by
    calc
      abs (∫ u in A..B, Real.cos u / u ^ 2) <=
          ∫ u in A..B, abs (Real.cos u / u ^ 2) :=
        intervalIntegral.abs_integral_le_integral_abs hAB
      _ <= ∫ u in A..B, 1 / u ^ 2 := by
        apply intervalIntegral.integral_mono_on hAB hcos_div_sq_integrable
          hone_div_sq_integrable
        intro x hx
        have hxpos : 0 < x := hpos x (uIcc_of_le hAB ▸ hx)
        rw [abs_div, abs_of_nonneg (sq_nonneg x)]
        exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hxpos)).2
          (Real.abs_cos_le_one x)
  have hintegral_one_div_sq :
      (∫ u in A..B, 1 / u ^ 2) = 1 / A - 1 / B := by
    have hinv_integral :
        (∫ u in A..B, -(u ^ 2)⁻¹) = B⁻¹ - A⁻¹ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hinv_deriv hinv_sq_integrable
    calc
      (∫ u in A..B, 1 / u ^ 2) =
          ∫ u in A..B, -(-(u ^ 2)⁻¹) := by
        apply intervalIntegral.integral_congr
        intro x _
        simp only [one_div, neg_neg]
      _ = -(∫ u in A..B, -(u ^ 2)⁻¹) := intervalIntegral.integral_neg
      _ = 1 / A - 1 / B := by rw [hinv_integral]; ring
  rw [hidentity]
  calc
    abs (Real.cos A / A - Real.cos B / B -
        ∫ u in A..B, Real.cos u / u ^ 2) <=
        abs (Real.cos A / A) + abs (Real.cos B / B) +
          abs (∫ u in A..B, Real.cos u / u ^ 2) := by
      calc
        _ <= abs (Real.cos A / A - Real.cos B / B) +
            abs (∫ u in A..B, Real.cos u / u ^ 2) := abs_sub _ _
        _ <= (abs (Real.cos A / A) + abs (Real.cos B / B)) +
            abs (∫ u in A..B, Real.cos u / u ^ 2) :=
          add_le_add (abs_sub _ _) le_rfl
    _ <= 1 / A + 1 / B + (1 / A - 1 / B) :=
      add_le_add (add_le_add hA_endpoint hB_endpoint)
        (hintegral_bound.trans_eq hintegral_one_div_sq)
    _ = 2 / A := by ring

end PrimesRestrictedDigits
