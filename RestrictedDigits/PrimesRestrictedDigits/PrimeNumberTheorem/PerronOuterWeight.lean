import PrimesRestrictedDigits.PrimeNumberTheorem.PerronHighBase
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronWeight
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Outer and endpoint Perron bounds against the starred weight

This file packages the two outer cases and the exact jump case of
`MONTGOMERY-VAUGHAN-MNT-I`, Theorem 5.2 and Eq. (5.9), pp. 139--140.
-/

namespace PrimesRestrictedDigits

private theorem one_lt_pi_mul_log_two :
    (1 : Real) < Real.pi * Real.log 2 := by
  have hmul : (3 : Real) * 0.6931471803 < Real.pi * Real.log 2 :=
    mul_lt_mul Real.pi_gt_three Real.log_two_gt_d9.le
      (by norm_num) Real.pi_pos.le
  exact (by norm_num : (1 : Real) < 3 * 0.6931471803).trans hmul

/-- On the complement of the strict central range, the one-term Perron error
is bounded by the source ratio power divided by the truncation height. -/
theorem norm_perronKernel_div_natCast_sub_perronWeight_outer_le
    {x sigma T : Real} {n : Nat} (hx : 0 < x) (hn : 0 < n)
    (houter : (n : Real) <= x / 2 ∨ 2 * x <= (n : Real))
    (hsigma : 0 < sigma) (hT : 0 < T) :
    ‖perronKernel (x / (n : Real)) sigma T - (perronWeight x n : Complex)‖ <=
      (x / (n : Real)) ^ sigma / T := by
  have hn' : (0 : Real) < n := by exact_mod_cast hn
  let y : Real := x / (n : Real)
  have hy : 0 < y := div_pos hx hn'
  rcases houter with hhigh | hlow
  · have hytwo : 2 <= y := by
      dsimp [y]
      rw [le_div_iff₀ hn']
      nlinarith [hhigh]
    have hnx : (n : Real) < x := by nlinarith [hhigh, hx]
    have hlogtwo : Real.log 2 <= Real.log y :=
      Real.log_le_log (by norm_num) hytwo
    have hdenone : 1 <= Real.pi * Real.log y := calc
      (1 : Real) <= Real.pi * Real.log 2 := one_lt_pi_mul_log_two.le
      _ <= Real.pi * Real.log y :=
        mul_le_mul_of_nonneg_left hlogtwo Real.pi_pos.le
    have hden : T <= Real.pi * T * Real.log y := calc
      T = T * 1 := by ring
      _ <= T * (Real.pi * Real.log y) :=
        mul_le_mul_of_nonneg_left hdenone hT.le
      _ = Real.pi * T * Real.log y := by ring
    have hsharp := norm_perronKernel_sub_one_highBase_le hytwo hsigma hT
    have hcoarse : ‖perronKernel y sigma T - 1‖ <= y ^ sigma / T :=
      hsharp.trans <| div_le_div_of_nonneg_left
        (Real.rpow_nonneg hy.le sigma) hT hden
    simpa [y, perronWeight_eq_one_of_lt hnx] using hcoarse
  · have hyhalf : y <= (1 / 2 : Real) := by
      dsimp [y]
      rw [div_le_iff₀ hn']
      nlinarith [hlow]
    have hxn : x < (n : Real) := by nlinarith [hlow, hx]
    have hloghalf : Real.log y <= -Real.log 2 := calc
      Real.log y <= Real.log (1 / 2 : Real) :=
        Real.log_le_log hy hyhalf
      _ = -Real.log 2 := by
        rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
    have hminus : Real.log 2 <= -Real.log y := by linarith
    have hdenone : 1 <= Real.pi * (-Real.log y) := calc
      (1 : Real) <= Real.pi * Real.log 2 := one_lt_pi_mul_log_two.le
      _ <= Real.pi * (-Real.log y) :=
        mul_le_mul_of_nonneg_left hminus Real.pi_pos.le
    have hden : T <= Real.pi * T * (-Real.log y) := calc
      T = T * 1 := by ring
      _ <= T * (Real.pi * (-Real.log y)) :=
        mul_le_mul_of_nonneg_left hdenone hT.le
      _ = Real.pi * T * (-Real.log y) := by ring
    have hsharp := norm_perronKernel_lowBase_le hy hyhalf hsigma hT
    have hcoarse : ‖perronKernel y sigma T‖ <= y ^ sigma / T :=
      hsharp.trans <| div_le_div_of_nonneg_left
        (Real.rpow_nonneg hy.le sigma) hT hden
    simpa [y, perronWeight_eq_zero_of_lt hxn] using hcoarse

/-- At an integer cutoff, the kernel is compared only with the exact
half-weight and retains its explicit arctangent error. -/
theorem norm_perronKernel_div_natCast_sub_perronWeight_eq_le
    {x sigma T : Real} {n : Nat} (hn : 0 < n) (hnx : (n : Real) = x)
    (hsigma : 0 < sigma) (hT : 0 < T) :
    ‖perronKernel (x / (n : Real)) sigma T - (perronWeight x n : Complex)‖ <=
      sigma / (Real.pi * T) := by
  have hn' : (0 : Real) < n := by exact_mod_cast hn
  have hratio : x / (n : Real) = 1 := by
    rw [← hnx]
    exact div_self hn'.ne'
  simpa [hratio, perronWeight_eq_half_of_eq hnx] using
    norm_perronKernel_one_sub_half_le hsigma hT

end PrimesRestrictedDigits
