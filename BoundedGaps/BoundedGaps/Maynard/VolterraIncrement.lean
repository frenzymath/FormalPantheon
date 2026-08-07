import BoundedGaps.Maynard.WirsingCumulativeVolterra

noncomputable section

/-!
# Discrete logarithmic Volterra increments

This packages the finite logarithmic increment sum and its elementary
one-step and positivity properties for the `kappa = 1` Wirsing recurrence.
-/

open scoped BigOperators

namespace BoundedGaps.Maynard

def abstractVolterraIncrement (M : ℕ → ℝ) (Q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range Q,
    (Real.log (i + 1) - Real.log i) * M i

theorem log_increment_nonneg (n : ℕ) :
    0 ≤ Real.log (n + 1) - Real.log n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_ne_zero hn
    have hsucc : (0 : ℝ) < n + 1 := by positivity
    have hle : (n : ℝ) ≤ n + 1 := by norm_num
    exact sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn hnpos hsucc hle)

theorem log_increment_le_log_two {n : ℕ} (hn : 0 < n) :
    Real.log (n + 1) - Real.log n ≤ Real.log 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsuccR : (0 : ℝ) < n + 1 := by positivity
  have hratio : Real.log (n + 1) - Real.log n =
      Real.log (((n + 1 : ℕ) : ℝ) / n) := by
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← Real.log_div hsuccR.ne' hnR.ne']
  rw [hratio]
  apply Real.strictMonoOn_log.monotoneOn
  · exact div_pos (by positivity) hnR
  · norm_num
  · have hnat : n + 1 ≤ 2 * n := by omega
    have hreal : ((n + 1 : ℕ) : ℝ) ≤ 2 * n := by exact_mod_cast hnat
    exact (div_le_iff₀ hnR).2 (by simpa [mul_comm] using hreal)

theorem abstractVolterraIncrement_succ (M : ℕ → ℝ) (n : ℕ) :
    abstractVolterraIncrement M (n + 1) =
      abstractVolterraIncrement M n +
        (Real.log (n + 1) - Real.log n) * M n := by
  unfold abstractVolterraIncrement
  rw [Finset.sum_range_succ]

end BoundedGaps.Maynard
