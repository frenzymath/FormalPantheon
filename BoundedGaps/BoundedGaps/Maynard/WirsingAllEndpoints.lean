import BoundedGaps.Maynard.VolterraStabilityGlobal
import BoundedGaps.Maynard.WirsingFixedModulusNormalization

noncomputable section

/-!
# All-endpoint squarefree reciprocal-totient estimate

SEM-385 instantiates the global Volterra stability theorem. The constant is
uniform in the primorial cutoff, augmented modulus, and endpoint. Its
`K = K₀ + 1` choice retains FordSieve2023's corrected `kappa = 1` error term.
-/

namespace BoundedGaps.Maynard

open Filter
open scoped Topology

theorem exists_uniform_abs_squarefreeCoprimeInvTotientMean_sub_density_log_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ {D P Q : ℕ}, 0 < P →
        Squarefree (primorial D * P) →
        |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
            coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
          10 * coprimeHarmonicDensity (primorial D * P) *
            (K + Real.log D + primeLogDivisorMass P + Real.log 2) := by
  obtain ⟨K₀, hK₀, hbalance⟩ :=
    exists_uniform_abs_log_mul_mean_sub_two_increment_sum_le
  let K : ℝ := K₀ + 1
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro D P Q hP hSq
  let W : ℕ := primorial D * P
  let M : ℕ → ℝ := fun n => squarefreeCoprimeInvTotientMean W n
  let δ : ℝ := coprimeHarmonicDensity W
  let E : ℝ := K + Real.log D + primeLogDivisorMass P
  have hW : 0 < W := by
    dsimp [W]
    exact Nat.mul_pos (primorial_pos D) hP
  have hlogD : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hmass : 0 ≤ primeLogDivisorMass P := by
    unfold primeLogDivisorMass
    positivity
  have hE : 0 < E := by dsimp [E]; linarith
  have hδ : 0 < δ := by
    unfold δ coprimeHarmonicDensity
    exact div_pos
      (by exact_mod_cast Nat.totient_pos.mpr hW)
      (by exact_mod_cast hW)
  have hMmono : Monotone M := by
    simpa [M] using
      (squarefreeCoprimeInvTotientMean_mono_cutoff (W := W))
  have hMzero : M 0 = 0 := by
    simp [M, squarefreeCoprimeInvTotientMean]
  have hMnonneg : ∀ n, 0 ≤ M n := by
    intro n
    rw [← hMzero]
    exact hMmono (Nat.zero_le n)
  have hbal : ∀ {n : ℕ}, 0 < n →
      |Real.log n * M n - 2 * abstractVolterraIncrement M n| ≤
        E * M n := by
    intro n hn
    have h₀ := hbalance (D := D) (P := P) (Q := n) hP hn
    have hM : 0 ≤ squarefreeCoprimeInvTotientMean W n := hMnonneg n
    have hKle : K₀ + Real.log D + primeLogDivisorMass P ≤ E := by
      dsimp [E, K]
      linarith
    have h₁ := h₀.trans (mul_le_mul_of_nonneg_right hKle hM)
    simpa [M, E, W, abstractVolterraIncrement,
      squarefreeCoprimeInvTotientLogIncrementSum] using h₁
  have hnorm : Tendsto (fun n : ℕ => M n / Real.log n)
      atTop (nhds δ) := by
    simpa [M, δ, W] using
      tendsto_squarefreeCoprimeInvTotientMean_div_log hW hSq
  have h := abstractVolterra_stability_all M δ E hδ hE hMnonneg hMmono
    hbal hnorm Q
  simpa [M, δ, E, W] using h

end BoundedGaps.Maynard
