import BoundedGaps.Maynard.VolterraStability

noncomputable section

/-!
# Global stability of the discrete Wirsing Volterra recurrence

SEM-384 extends the large-endpoint SEM-382 estimate to every natural endpoint.
Monotonicity controls the finite initial segment through one explicit ceiling
endpoint; the resulting constant ten is proved here and is not quoted from
FordSieve2023.
-/

open scoped Topology
open Filter

namespace BoundedGaps.Maynard

theorem abstractVolterra_stability_all
    (M : ℕ → ℝ) (δ E : ℝ)
    (hδ : 0 < δ) (hE : 0 < E)
    (hMnonneg : ∀ n, 0 ≤ M n)
    (hMmono : Monotone M)
    (hbal : ∀ {n : ℕ}, 0 < n →
      |Real.log n * M n - 2 * abstractVolterraIncrement M n| ≤ E * M n)
    (hnorm : Tendsto (fun n : ℕ => M n / Real.log n) atTop (𝓝 δ)) :
    ∀ n : ℕ,
      |M n - δ * Real.log n| ≤ 10 * δ * (E + Real.log 2) := by
  let F : ℝ := E + Real.log 2
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hF : 0 < F := by dsimp [F]; linarith
  have hδF : 0 < δ * F := mul_pos hδ hF
  have hlarge : ∀ {n : ℕ}, 2 * F ≤ Real.log n →
      |M n - δ * Real.log n| ≤ 7 * δ * F := by
    intro n hn
    exact abstractVolterra_stability_large M δ E hδ hE hMnonneg hbal hnorm
      (n := n) (by simpa [F] using hn)
  intro n
  by_cases hnlarge : 2 * F ≤ Real.log n
  · have hnBound := hlarge (n := n) hnlarge
    calc
      |M n - δ * Real.log n| ≤ 7 * δ * F := hnBound
      _ ≤ 10 * δ * F := by nlinarith
      _ = 10 * δ * (E + Real.log 2) := by rfl
  · have hnsmall : Real.log n < 2 * F := lt_of_not_ge hnlarge
    let N : ℕ := ⌈Real.exp (2 * F)⌉₊
    have hNlower : Real.exp (2 * F) ≤ (N : ℝ) := by
      simpa [N] using (Nat.le_ceil (Real.exp (2 * F)))
    have hNpos : (0 : ℝ) < N := (Real.exp_pos _).trans_le hNlower
    have hNlarge : 2 * F ≤ Real.log N := by
      have hlog := Real.strictMonoOn_log.monotoneOn
        (Real.exp_pos _) hNpos hNlower
      simpa using hlog
    have hNupper : Real.log N ≤ 2 * F + Real.log 2 := by
      have hexpOne : (1 : ℝ) ≤ Real.exp (2 * F) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by positivity)
      have hNlt : (N : ℝ) < Real.exp (2 * F) + 1 := by
        simpa [N] using Nat.ceil_lt_add_one (Real.exp_pos (2 * F)).le
      have hNtwo : (N : ℝ) ≤ 2 * Real.exp (2 * F) := by
        linarith
      have hlog := Real.strictMonoOn_log.monotoneOn hNpos
        (mul_pos (by norm_num) (Real.exp_pos _)) hNtwo
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (Real.exp_ne_zero _), Real.log_exp] at hlog
      linarith
    have hnN : n ≤ N := by
      by_cases hn0 : n = 0
      · simp [hn0]
      · have hnpos : (0 : ℝ) < n := by
          exact_mod_cast Nat.pos_of_ne_zero hn0
        have hnExp : (n : ℝ) < Real.exp (2 * F) := by
          rw [← Real.exp_log hnpos]
          exact Real.exp_lt_exp.mpr hnsmall
        exact_mod_cast hnExp.le.trans hNlower
    have hNBound := hlarge (n := N) hNlarge
    have hMNupper : M N ≤ δ * Real.log N + 7 * δ * F := by
      have := (abs_le.mp hNBound).2
      linarith
    have hMnbound : M n ≤ 10 * δ * F := by
      have hmono := hMmono hnN
      have hlog2F : Real.log 2 ≤ F := by dsimp [F]; linarith
      nlinarith
    have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hMn := hMnonneg n
    rw [abs_le]
    constructor <;> nlinarith

end BoundedGaps.Maynard
