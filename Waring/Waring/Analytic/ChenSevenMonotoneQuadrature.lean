import Waring.Analytic.ChenSevenSecant

/-!
# Derivative interface for Chen's monotone-phase quadrature

This file derives the discrete phase-increment hypotheses of the right-sample
quadrature theorem from the positive monotone derivative conditions used in
the fifth-power application.
-/

namespace Waring.Analytic

open MeasureTheory Set
open scoped BigOperators Interval

/-- A positive monotone derivative bounded by `pi` gives the four-unit
right-sample sum-to-integral estimate. -/
theorem norm_sum_range_exp_right_sub_integral_le_four_of_deriv
    {theta : Real → Real} (htheta : ContDiff Real 1 theta) (n : Nat)
    (hmono : MonotoneOn (deriv theta) (Icc 0 n))
    (hpos : ∀ x ∈ Icc (0 : Real) n, 0 < deriv theta x)
    (htop : deriv theta n ≤ Real.pi) :
    ‖(∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * (theta (i + 1) : Complex))) -
      (∫ x in (0 : Real)..n,
        Complex.exp (Complex.I * (theta x : Complex)))‖ ≤ 4 := by
  have hconv : ConvexOn Real (Icc (0 : Real) n) theta := by
    apply (hmono.mono interior_subset).convexOn_of_deriv
      (convex_Icc (0 : Real) n)
    · exact htheta.continuous.continuousOn
    · exact (htheta.differentiable one_ne_zero).differentiableOn
  have hincrPos : ∀ i, i < n → 0 < theta (i + 1) - theta i := by
    intro i hi
    have hiTop : (i : Real) + 1 ≤ n := by
      exact_mod_cast Nat.succ_le_of_lt hi
    have hai : (i : Real) ∈ Icc (0 : Real) n :=
      ⟨Nat.cast_nonneg i,
        (le_add_of_nonneg_right (by norm_num)).trans hiTop⟩
    have hbi : (i : Real) + 1 ∈ Icc (0 : Real) n :=
      ⟨by positivity, hiTop⟩
    have hslope := hconv.deriv_le_slope hai hbi (by linarith)
      (htheta.differentiable one_ne_zero (i : Real))
    have hle : deriv theta i ≤ theta (i + 1) - theta i := by
      simpa only [slope_def_field, add_sub_cancel_left, div_one] using hslope
    exact (hpos i hai).trans_le hle
  have hincrPi : ∀ i, i < n → theta (i + 1) - theta i ≤ Real.pi := by
    intro i hi
    have hiTop : (i : Real) + 1 ≤ n := by
      exact_mod_cast Nat.succ_le_of_lt hi
    have hai : (i : Real) ∈ Icc (0 : Real) n :=
      ⟨Nat.cast_nonneg i,
        (le_add_of_nonneg_right (by norm_num)).trans hiTop⟩
    have hbi : (i : Real) + 1 ∈ Icc (0 : Real) n :=
      ⟨by positivity, hiTop⟩
    have hslope := hconv.slope_le_deriv hai hbi (by linarith)
      (htheta.differentiable one_ne_zero ((i : Real) + 1))
    have hle :
        theta (i + 1) - theta i ≤ deriv theta ((i : Real) + 1) := by
      simpa only [slope_def_field, add_sub_cancel_left, div_one] using hslope
    exact hle.trans ((hmono hbi ⟨by positivity, le_rfl⟩ hiTop).trans htop)
  have hincrMono : ∀ i, i + 1 < n →
      theta (i + 1) - theta i ≤ theta (i + 2) - theta (i + 1) := by
    intro i hi
    have hiTwoTop : (i : Real) + 2 ≤ n := by
      have hNat : i + 2 ≤ n := by omega
      exact_mod_cast hNat
    have hai : (i : Real) ∈ Icc (0 : Real) n :=
      ⟨Nat.cast_nonneg i, by linarith⟩
    have hbi : (i : Real) + 1 ∈ Icc (0 : Real) n :=
      ⟨by positivity, by linarith⟩
    have hci : (i : Real) + 2 ∈ Icc (0 : Real) n :=
      ⟨by positivity, hiTwoTop⟩
    have hleft := hconv.slope_le_deriv hai hbi (by linarith)
      (htheta.differentiable one_ne_zero ((i : Real) + 1))
    have hright := hconv.deriv_le_slope hbi hci (by linarith)
      (htheta.differentiable one_ne_zero ((i : Real) + 1))
    simp only [slope_def_field, add_sub_cancel_left, div_one] at hleft
    have hden : (i : Real) + 2 - ((i : Real) + 1) = 1 := by ring
    rw [slope_def_field, hden, div_one] at hright
    exact hleft.trans hright
  apply norm_sum_range_exp_right_sub_integral_le_four htheta n
    hincrPos hincrPi hincrMono hmono
  have hnmem : (n : Real) ∈ Icc (0 : Real) n := ⟨by positivity, le_rfl⟩
  have h0mem : (0 : Real) ∈ Icc (0 : Real) n := ⟨le_rfl, by positivity⟩
  linarith [hpos 0 h0mem]

end Waring.Analytic
