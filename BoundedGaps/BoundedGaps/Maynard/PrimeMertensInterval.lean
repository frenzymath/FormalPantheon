import BoundedGaps.Maynard.PrimeMertens

noncomputable section

/-!
# The bounded prime Mertens estimate on intervals

The natural interval `w <= p <= z` is represented by subtracting primes at
most `w - 1`.  Its logarithmic main term differs from the corresponding
difference of initial logarithms by one uniformly bounded adjacent-log term.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real

noncomputable def primeLogIntervalSum (w z : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE z \ Nat.primesLE (w - 1),
    Real.log p / (p : ℝ)

theorem primeLogIntervalSum_eq_sub
    {w z : ℕ} (hwz : w ≤ z) :
    primeLogIntervalSum w z =
      primeLogHarmonicSum z - primeLogHarmonicSum (w - 1) := by
  unfold primeLogIntervalSum primeLogHarmonicSum
  apply Finset.sum_sdiff_eq_sub
  exact Nat.primesLE_mono ((Nat.sub_le w 1).trans hwz)

theorem log_sub_log_pred_mem_Icc {w : ℕ} (hw : 2 ≤ w) :
    0 ≤ Real.log (w : ℝ) - Real.log (w - 1 : ℕ) ∧
      Real.log (w : ℝ) - Real.log (w - 1 : ℕ) ≤ Real.log 2 := by
  have hpredPos : (0 : ℝ) < (w - 1 : ℕ) := by
    exact_mod_cast (show 0 < w - 1 by omega)
  have hwPos : (0 : ℝ) < w := by positivity
  have hpredLe : w - 1 ≤ w := Nat.sub_le w 1
  have hwLe : w ≤ 2 * (w - 1) := by omega
  constructor
  · exact sub_nonneg.mpr <| Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact hpredPos)
      (by simp only [Set.mem_Ioi]; exact hwPos)
      (by exact_mod_cast hpredLe)
  · have hratioLe : (w : ℝ) / (w - 1 : ℕ) ≤ 2 := by
      apply (div_le_iff₀ hpredPos).2
      exact_mod_cast hwLe
    have hratioPos : (0 : ℝ) < (w : ℝ) / (w - 1 : ℕ) :=
      div_pos hwPos hpredPos
    have hlogLe : Real.log ((w : ℝ) / (w - 1 : ℕ)) ≤ Real.log 2 :=
      Real.strictMonoOn_log.monotoneOn
        (by simp only [Set.mem_Ioi]; exact hratioPos)
        (by simp only [Set.mem_Ioi]; norm_num)
        hratioLe
    rw [Real.log_div hwPos.ne' hpredPos.ne'] at hlogLe
    exact hlogLe

theorem exists_uniform_abs_primeLogIntervalSum_sub_log_div :
    ∃ C : ℝ, ∀ {w z : ℕ}, 2 ≤ w → w ≤ z →
      |primeLogIntervalSum w z -
        Real.log ((z : ℝ) / (w : ℝ))| ≤ C := by
  obtain ⟨C, hC⟩ := exists_uniform_abs_primeLogHarmonicSum_sub_log
  refine ⟨2 * C + Real.log 2, fun {w z} hw hwz => ?_⟩
  have hzPos : (0 : ℝ) < z := by
    exact_mod_cast (show 0 < z by omega)
  have hwPos : (0 : ℝ) < w := by positivity
  have hpredPos : (0 : ℝ) < (w - 1 : ℕ) := by
    exact_mod_cast (show 0 < w - 1 by omega)
  have hinterval := primeLogIntervalSum_eq_sub hwz
  have hadj := log_sub_log_pred_mem_Icc hw
  have hEz := hC z
  have hEw := hC (w - 1)
  rw [hinterval, Real.log_div hzPos.ne' hwPos.ne']
  have heq :
      (primeLogHarmonicSum z - primeLogHarmonicSum (w - 1)) -
          (Real.log (z : ℝ) - Real.log (w : ℝ)) =
        (primeLogHarmonicSum z - Real.log z) -
          (primeLogHarmonicSum (w - 1) - Real.log (w - 1 : ℕ)) +
            (Real.log (w : ℝ) - Real.log (w - 1 : ℕ)) := by
    ring
  rw [heq]
  calc
    |(primeLogHarmonicSum z - Real.log z) -
        (primeLogHarmonicSum (w - 1) - Real.log (w - 1 : ℕ)) +
          (Real.log (w : ℝ) - Real.log (w - 1 : ℕ))| ≤
        |primeLogHarmonicSum z - Real.log z| +
          |primeLogHarmonicSum (w - 1) - Real.log (w - 1 : ℕ)| +
            |Real.log (w : ℝ) - Real.log (w - 1 : ℕ)| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ C + C + Real.log 2 := by
      rw [abs_of_nonneg hadj.1]
      linarith
    _ = 2 * C + Real.log 2 := by ring

end BoundedGaps.Maynard
