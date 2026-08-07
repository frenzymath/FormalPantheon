import BoundedGaps.BombieriVinogradov.Analytic.ExceptionalZeroAbsorption
import BoundedGaps.BombieriVinogradov.Analytic.RegularizedProductExceptionalZero

/-!
# Exceptional-zero denominator control

This file closes the denominator left open by SEM-465. A zero of the entire
regularized character product in the SEM-494 near-one region is real and at
least one half, so its inverse costs at most a factor two. The final theorem
composes this bound with the Siegel-shaped scalar absorption from SEM-465.

The dominant scalar quotient in the corrected exceptional main term is
`x^beta / beta`; Koukoulopoulos Theorem 12.4 omits this denominator, while
its proof, Exercise 12.2(a), and Davenport Ch. 22 equation (5) retain it.
Semantic review: `SEM-495`.
-/

noncomputable section

namespace BoundedGaps.Maynard

/-- The synchronized near-one scale puts the real part strictly above one
half. -/
theorem half_lt_re_of_near_one_scale
    {M q : ℕ} [NeZero q] {rho : ℂ} (hM : 2 ≤ M)
    (hnear : 1 - 1 / ((M : ℝ) ^ 2 *
      Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re) :
    (1 / 2 : ℝ) < rho.re := by
  let L : ℝ := Real.log ((q : ℝ) * (|rho.im| + 2))
  have hlog : (1 / 2 : ℝ) < L := by
    have hhalf : (1 / 2 : ℝ) < Real.log 2 :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9
    exact hhalf.trans_le
      (Real.log_le_log zero_lt_two
        (by simpa [L] using two_le_level_height (q := q) rho.im))
  have hMcast : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMsquare : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hMpos : (0 : ℝ) < M := zero_lt_two.trans_le hMcast
  have hden : (2 : ℝ) < (M : ℝ) ^ 2 * L := by
    calc
      (2 : ℝ) = 4 * (1 / 2 : ℝ) := by norm_num
      _ ≤ (M : ℝ) ^ 2 * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hMsquare (by norm_num)
      _ < (M : ℝ) ^ 2 * L :=
        mul_lt_mul_of_pos_left hlog (sq_pos_of_pos hMpos)
  have hinv : 1 / ((M : ℝ) ^ 2 * L) < (1 / 2 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) hden
  dsimp [L] at hinv
  linarith

/-- A qualifying regularized-product zero is real and its real denominator
is uniformly bounded away from zero. -/
theorem exists_nat_regularizedDirichletLFunctionProduct_zero_denominator_bound :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q] (rho : ℂ),
        1 - 1 / ((M : ℝ) ^ 2 *
          Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re →
          regularizedDirichletLFunctionProduct q rho = 0 →
            rho.im = 0 ∧
              (1 / 2 : ℝ) ≤ rho.re ∧ (rho.re)⁻¹ ≤ 2 := by
  obtain ⟨M, hM, hstructure⟩ :=
    exists_nat_regularizedDirichletLFunctionProduct_zero_structure
  refine ⟨M, hM, ?_⟩
  intro q _ rho hnear hzero
  have hhalf := half_lt_re_of_near_one_scale hM hnear
  obtain ⟨_, _, _, _, him, _, _⟩ := hstructure q rho hnear hzero
  have hrhoPos : 0 < rho.re := by linarith
  have hinv : (rho.re)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ hrhoPos zero_lt_two]
    norm_num
    exact hhalf.le
  exact ⟨him, hhalf.le, hinv⟩

/-- A positive exceptional denominator costs at most a factor two. -/
theorem rpow_div_le_two_mul_rpow_of_half_le
    {x beta : ℝ} (hx : 0 ≤ x) (hbeta : (1 / 2 : ℝ) ≤ beta) :
    x ^ beta / beta ≤ 2 * x ^ beta := by
  have hbetaPos : 0 < beta :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hbeta
  have hinv : beta⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ hbetaPos zero_lt_two]
    norm_num
    exact hbeta
  rw [div_eq_mul_inv]
  calc
    x ^ beta * beta⁻¹ ≤ x ^ beta * 2 :=
      mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hx beta)
    _ = 2 * x ^ beta := by ring

/-- SEM-465's exceptional numerator estimate absorbs the full quotient once
the exceptional zero is at least one half. -/
theorem exceptionalZeroRpow_div_lt_two_mul_exp_neg_sqrtLog
    {D c x q beta : ℝ} (hD : 0 < D) (hc : 0 < c)
    (hx : 0 < x) (hxlog : 1 ≤ Real.log x)
    (hq : 1 ≤ q) (hqlog : q ≤ Real.log x ^ D)
    (hbetaHalf : (1 / 2 : ℝ) ≤ beta)
    (hbetaGap : beta < 1 - c * q ^ (-(2 * D)⁻¹)) :
    x ^ beta / beta <
      2 * (x * Real.exp (-c * Real.sqrt (Real.log x))) := by
  exact (rpow_div_le_two_mul_rpow_of_half_le hx.le hbetaHalf).trans_lt
    (mul_lt_mul_of_pos_left
      (exceptionalZeroPower_lt_exp_neg_sqrtLog
        hD hc hx hxlog hq hqlog hbetaGap) zero_lt_two)

end BoundedGaps.Maynard
