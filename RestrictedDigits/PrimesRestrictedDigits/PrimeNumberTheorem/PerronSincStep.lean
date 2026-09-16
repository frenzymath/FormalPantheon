import PrimesRestrictedDigits.PrimeNumberTheorem.PerronSincLimit
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The finite sinc primitive as a step approximation

This is the quantitative step-function form of the sine-integral estimate in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5, Eqs. (5.6)--(5.9), pp. 138--140.
The integral remains finite and oriented throughout.
-/

open MeasureTheory
open scoped Interval

namespace PrimesRestrictedDigits

private theorem abs_half_add_sincIntegral_sub_one_le
    {A : Real} (hA : 0 < A) :
    abs (1 / 2 +
        (∫ u in (0 : Real)..A, Real.sinc u) / Real.pi - 1) <=
      min 1 (1 / A) := by
  let S : Real := ∫ u in (0 : Real)..A, Real.sinc u
  have hreform : 1 / 2 + S / Real.pi - 1 =
      (S - Real.pi / 2) / Real.pi := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hreform, abs_div, abs_of_pos Real.pi_pos]
  by_cases hlarge : 1 <= A
  · rw [min_eq_right]
    · have htail := abs_dirichletSineIntegral_sub_pi_div_two_le_two_div hA
      change abs (S - Real.pi / 2) <= 2 / A at htail
      have htwo_pi : 2 / Real.pi <= 1 := by
        rw [div_le_one Real.pi_pos]
        linarith [Real.pi_gt_three]
      have hinvA : 0 <= 1 / A := by positivity
      calc
        abs (S - Real.pi / 2) / Real.pi <= (2 / A) / Real.pi :=
          div_le_div_of_nonneg_right htail Real.pi_pos.le
        _ = (2 / Real.pi) * (1 / A) := by
          field_simp [Real.pi_ne_zero, hA.ne']
        _ <= 1 * (1 / A) := mul_le_mul_of_nonneg_right htwo_pi hinvA
        _ = 1 / A := one_mul _
    · exact (div_le_one hA).2 hlarge
  · have hAle : A <= 1 := le_of_not_ge hlarge
    rw [min_eq_left]
    · have hS : abs S <= A := by
        have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : Real)) (b := A) (C := (1 : Real))
          (f := Real.sinc) (fun u _hu => by
            simpa [Real.norm_eq_abs] using Real.abs_sinc_le_one u)
        simpa [S, Real.norm_eq_abs, abs_of_pos hA] using hbound
      have hApi : A / Real.pi <= 1 / Real.pi :=
        div_le_div_of_nonneg_right hAle Real.pi_pos.le
      have hinvpi : 1 / Real.pi <= 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) Real.pi_gt_three.le
      calc
        abs (S - Real.pi / 2) / Real.pi <=
            (abs S + abs (Real.pi / 2)) / Real.pi := by
          gcongr
          exact abs_sub _ _
        _ = abs S / Real.pi + 1 / 2 := by
          rw [abs_div, abs_of_pos Real.pi_pos]
          field_simp [Real.pi_ne_zero]
          ring
        _ <= A / Real.pi + 1 / 2 := by gcongr
        _ <= 1 := by linarith
    · rw [le_div_iff₀ hA]
      simpa using hAle

private theorem integral_sinc_zero_neg (A : Real) :
    (∫ u in (0 : Real)..(-A), Real.sinc u) =
      -(∫ u in (0 : Real)..A, Real.sinc u) := by
  have hcomp := intervalIntegral.integral_comp_neg
    (f := Real.sinc) (a := (0 : Real)) (b := -A)
  calc
    (∫ u in (0 : Real)..(-A), Real.sinc u) =
        ∫ u in A..(0 : Real), Real.sinc u := by
      simpa [Real.sinc_neg] using hcomp
    _ = -(∫ u in (0 : Real)..A, Real.sinc u) :=
      intervalIntegral.integral_symm 0 A

/-- Away from its jump, the normalized oriented sinc primitive approximates
the corresponding zero-one step with explicit error `min 1 (1 / |A|)`. -/
theorem abs_half_add_sincIntegral_sub_step_le
    {A : Real} (hA : A ≠ 0) :
    abs (1 / 2 +
        (∫ u in (0 : Real)..A, Real.sinc u) / Real.pi -
          (if 0 < A then 1 else 0)) <=
      min 1 (1 / abs A) := by
  by_cases hpos : 0 < A
  · simpa [hpos, abs_of_pos hpos] using
      abs_half_add_sincIntegral_sub_one_le hpos
  · have hneg : A < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hA
    have hposneg : 0 < -A := neg_pos.mpr hneg
    have hbound := abs_half_add_sincIntegral_sub_one_le hposneg
    have hs := integral_sinc_zero_neg A
    rw [if_neg hpos, abs_of_neg hneg]
    calc
      abs (1 / 2 + (∫ u in (0 : Real)..A, Real.sinc u) / Real.pi - 0) =
          abs (1 / 2 +
            (∫ u in (0 : Real)..(-A), Real.sinc u) / Real.pi - 1) := by
        rw [hs]
        rw [show 1 / 2 +
            (-(∫ u in (0 : Real)..A, Real.sinc u)) / Real.pi - 1 =
            -(1 / 2 +
              (∫ u in (0 : Real)..A, Real.sinc u) / Real.pi - 0) by ring,
          abs_neg]
      _ <= min 1 (1 / -A) := hbound

end PrimesRestrictedDigits
