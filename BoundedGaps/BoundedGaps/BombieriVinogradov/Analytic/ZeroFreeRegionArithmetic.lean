import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Arithmetic for logarithmic zero-free regions

Elementary height-scale and reciprocal-gap inequalities shared by the
square-nonprincipal and square-principal branches of the Dirichlet
L-function zero-free region.

Sources: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 119--121,
especially (12.2)--(12.3), and `ElkiesM229NearlyZeroFree2018`, pp. 1--3.
Semantic reviews: `SEM-484` and `SEM-486`.
-/

namespace BoundedGaps.Maynard

lemma two_le_level_height
    {q : ℕ} [NeZero q] (t : ℝ) :
    (2 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast NeZero.pos q
  have ht : (2 : ℝ) ≤ |t| + 2 := by
    linarith [abs_nonneg t]
  simpa using mul_le_mul hq ht (by norm_num : (0 : ℝ) ≤ 2)
    (zero_le_one.trans hq)

lemma doubled_height_scale_le_sq
    {q : ℕ} [NeZero q] (t : ℝ) :
    (q : ℝ) * (|2 * t| + 2) ≤
      ((q : ℝ) * (|t| + 2)) ^ 2 := by
  let Q : ℝ := (q : ℝ) * (|t| + 2)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hQ2 : (2 : ℝ) ≤ Q := by
    simpa [Q] using two_le_level_height (q := q) t
  have hfirst : (q : ℝ) * (|2 * t| + 2) ≤ 2 * Q := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp [Q]
    nlinarith
  have hsecond : 2 * Q ≤ Q ^ 2 := by
    have hprod : 0 ≤ Q * (Q - 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  exact hfirst.trans hsecond

lemma log_doubled_height_le_two_mul_log
    {q : ℕ} [NeZero q] (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤
      2 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast NeZero.pos q
  have hleftpos : (0 : ℝ) < (q : ℝ) * (|2 * t| + 2) :=
    mul_pos hqpos (by linarith [abs_nonneg (2 * t)])
  calc
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤
        Real.log (((q : ℝ) * (|t| + 2)) ^ 2) :=
      Real.log_le_log hleftpos (doubled_height_scale_le_sq (q := q) t)
    _ = 2 * Real.log ((q : ℝ) * (|t| + 2)) := by
      rw [Real.log_pow]
      norm_num

lemma mul_sub_one_le_inv_one_add_inv_sub
    {m L beta : ℝ} (hm : 2 ≤ m) (hL : 0 < L)
    (hbeta : 1 - 1 / (m ^ 2 * L) ≤ beta) (hbeta_one : beta < 1) :
    (m - 1) * L ≤ (1 + 1 / (m * L) - beta)⁻¹ := by
  have hmpos : 0 < m := by linarith
  have hm_sub_pos : 0 < (m - 1) * L :=
    mul_pos (by linarith) hL
  have hden1 : 0 < m * L := mul_pos hmpos hL
  have hdelta : 0 < 1 + 1 / (m * L) - beta := by
    have hinvpos : 0 < 1 / (m * L) := one_div_pos.mpr hden1
    linarith
  have hrecip_add :
      1 / (m * L) + 1 / (m ^ 2 * L) =
        (m + 1) / (m ^ 2 * L) := by
    field_simp [hmpos.ne', hL.ne']
  have hdelta_le :
      1 + 1 / (m * L) - beta ≤ (m + 1) / (m ^ 2 * L) := by
    calc
      1 + 1 / (m * L) - beta =
          1 / (m * L) + (1 - beta) := by ring
      _ ≤ 1 / (m * L) + 1 / (m ^ 2 * L) := by linarith
      _ = (m + 1) / (m ^ 2 * L) := hrecip_add
  have hprod :
      (m + 1) / (m ^ 2 * L) * ((m - 1) * L) < 1 := by
    have heq :
        (m + 1) / (m ^ 2 * L) * ((m - 1) * L) =
          1 - 1 / m ^ 2 := by
      field_simp [hmpos.ne', hL.ne']
      ring
    rw [heq]
    have : 0 < 1 / m ^ 2 := one_div_pos.mpr (sq_pos_of_pos hmpos)
    linarith
  have hbound :
      (m + 1) / (m ^ 2 * L) ≤ ((m - 1) * L)⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hm_sub_pos).2 hprod.le
  exact (le_inv_comm₀ hm_sub_pos hdelta).2 (hdelta_le.trans hbound)

end BoundedGaps.Maynard
