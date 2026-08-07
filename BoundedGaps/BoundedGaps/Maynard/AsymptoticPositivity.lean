import BoundedGaps.Maynard.ImprovedGPY.SieveSums
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Normalized sieve asymptotics imply positive excess

The source's Proposition `MainProp` supplies normalized limits for `S₁` and
`S₂`. This module proves the exact order-theoretic composition from those
limits to eventual positivity of the finite sieve excess, while leaving the
analytic asymptotic estimates as explicit hypotheses.
-/

namespace BoundedGaps.Maynard

open Filter Set

theorem tendsto_normalized_sum_of_error
    (s main scale : ℕ → ℝ) (I : ℝ)
    (hscale : ∀ᶠ N : ℕ in atTop, scale N ≠ 0)
    (hmain : Tendsto (fun N => main N / scale N) atTop (nhds I))
    (herr : Tendsto (fun N => (s N - main N) / scale N)
      atTop (nhds 0)) :
    Tendsto (fun N => s N / scale N) atTop (nhds I) := by
  have hsum : Tendsto
      (fun N => main N / scale N + (s N - main N) / scale N)
      atTop (nhds I) := by
    simpa using hmain.add herr
  apply hsum.congr'
  filter_upwards [hscale] with N hN
  field_simp
  ring

theorem eventually_sieveExcess_pos_of_normalized_asymptotics
    {H : Finset ℕ} {rho I J : ℝ}
    (weights : ℕ → ℕ → ℝ) (scale : ℕ → ℝ)
    (hmargin : 0 < J - rho * I)
    (hscale : ∀ᶠ N : ℕ in atTop, 0 < scale N)
    (hS1 : Tendsto
      (fun N : ℕ => sieveWeightSum N (weights N) / scale N)
      atTop (nhds I))
    (hS2 : Tendsto
      (fun N : ℕ => primeWeightedSieveSum H N (weights N) / scale N)
      atTop (nhds J)) :
    ∀ᶠ N : ℕ in atTop, 0 < sieveExcess H N rho (weights N) := by
  have hscaledS1 : Tendsto
      (fun N : ℕ => rho * (sieveWeightSum N (weights N) / scale N))
      atTop (nhds (rho * I)) := by
    simpa using (tendsto_const_nhds.mul hS1)
  have hdiff : Tendsto
      (fun N : ℕ =>
        primeWeightedSieveSum H N (weights N) / scale N -
          rho * (sieveWeightSum N (weights N) / scale N))
      atTop (nhds (J - rho * I)) := hS2.sub hscaledS1
  have hdiff_pos : ∀ᶠ N : ℕ in atTop,
      0 < primeWeightedSieveSum H N (weights N) / scale N -
          rho * (sieveWeightSum N (weights N) / scale N) := by
    exact hdiff.eventually (isOpen_Ioi.mem_nhds hmargin)
  filter_upwards [hscale, hdiff_pos] with N hscaleN hdiffN
  rw [sieveExcess]
  have hscale_ne : scale N ≠ 0 := ne_of_gt hscaleN
  rw [show primeWeightedSieveSum H N (weights N) -
        rho * sieveWeightSum N (weights N) =
      scale N *
        (primeWeightedSieveSum H N (weights N) / scale N -
          rho * (sieveWeightSum N (weights N) / scale N)) by
    field_simp]
  exact mul_pos hscaleN hdiffN

theorem hasEventuallyPositiveSieveExcess_of_normalized_asymptotics
    {H : Finset ℕ} {rho I J : ℝ}
    (weights : ℕ → ℕ → ℝ) (scale : ℕ → ℝ)
    (hmargin : 0 < J - rho * I)
    (hscale : ∀ᶠ N : ℕ in atTop, 0 < scale N)
    (hweights : ∀ᶠ N : ℕ in atTop,
      ∀ n ∈ Finset.Ico N (2 * N), 0 ≤ weights N n)
    (hS1 : Tendsto
      (fun N : ℕ => sieveWeightSum N (weights N) / scale N)
      atTop (nhds I))
    (hS2 : Tendsto
      (fun N : ℕ => primeWeightedSieveSum H N (weights N) / scale N)
      atTop (nhds J)) :
    HasEventuallyPositiveSieveExcess H rho := by
  have hpos := eventually_sieveExcess_pos_of_normalized_asymptotics
    weights scale hmargin hscale hS1 hS2
  have hevent : ∀ᶠ N : ℕ in atTop,
      (∀ n ∈ Finset.Ico N (2 * N), 0 ≤ weights N n) ∧
        0 < sieveExcess H N rho (weights N) := hweights.and hpos
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N₀, hN₀⟩ := hevent
  exact ⟨N₀, fun N hN => ⟨weights N, (hN₀ N hN).1, (hN₀ N hN).2⟩⟩

theorem hasEventuallyPositiveSquareDivisorSieveExcess_of_normalized_asymptotics
    {H : Finset ℕ} {rho I J : ℝ}
    (D : ℕ → Finset (H → ℕ))
    (lambda : ℕ → (H → ℕ) → ℝ) (scale : ℕ → ℝ)
    (hmargin : 0 < J - rho * I)
    (hscale : ∀ᶠ N : ℕ in atTop, 0 < scale N)
    (hS1 : Tendsto
      (fun N : ℕ =>
        sieveWeightSum N (squareDivisorWeight H (D N) (lambda N)) /
          scale N)
      atTop (nhds I))
    (hS2 : Tendsto
      (fun N : ℕ =>
        primeWeightedSieveSum H N
          (squareDivisorWeight H (D N) (lambda N)) / scale N)
      atTop (nhds J)) :
    HasEventuallyPositiveSquareDivisorSieveExcess H rho := by
  have hpos := eventually_sieveExcess_pos_of_normalized_asymptotics
    (weights := fun N n => squareDivisorWeight H (D N) (lambda N) n)
    (scale := scale) hmargin hscale hS1 hS2
  rw [Filter.eventually_atTop] at hpos
  obtain ⟨N₀, hN₀⟩ := hpos
  refine ⟨N₀, ?_⟩
  intro N hN
  exact ⟨D N, lambda N, hN₀ N hN⟩

theorem hasEventuallyPositivePreSievedSieveExcess_of_normalized_asymptotics
    {H : Finset ℕ} {rho I J : ℝ}
    (D : ℕ → Finset (H → ℕ))
    (lambda : ℕ → (H → ℕ) → ℝ)
    (v W : ℕ → ℕ) (scale : ℕ → ℝ)
    (hmargin : 0 < J - rho * I)
    (hscale : ∀ᶠ N : ℕ in atTop, 0 < scale N)
    (hS1 : Tendsto
      (fun N : ℕ =>
        sieveWeightSum N
          (preSievedSquareDivisorWeight H (D N) (lambda N) (v N) (W N)) /
            scale N)
      atTop (nhds I))
    (hS2 : Tendsto
      (fun N : ℕ =>
        primeWeightedSieveSum H N
          (preSievedSquareDivisorWeight H (D N) (lambda N) (v N) (W N)) /
            scale N)
      atTop (nhds J)) :
    HasEventuallyPositiveSieveExcess H rho := by
  apply hasEventuallyPositiveSieveExcess_of_normalized_asymptotics
    (weights := fun N n =>
      preSievedSquareDivisorWeight H (D N) (lambda N) (v N) (W N) n)
    (scale := scale) hmargin hscale
  · filter_upwards [] with N n hn
    exact preSievedSquareDivisorWeight_nonneg
      H (D N) (lambda N) (v N) (W N) n
  · exact hS1
  · exact hS2

end BoundedGaps.Maynard
