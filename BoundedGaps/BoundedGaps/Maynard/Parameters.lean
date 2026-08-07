import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

import BoundedGaps.Maynard.ImprovedGPY.PairSum

noncomputable section

/-!
# The natural triple-log pre-sieving cutoff

Maynard2013v3, Section 5 outline (source lines 193--196), chooses
`D₀ = log log log N` and `W` as the product of primes up to `D₀`.  This file
records the natural floor convention and its eventual finite consequences.
-/

namespace BoundedGaps.Maynard

def tripleLogCutoff (N : ℕ) : ℕ :=
  ⌊Real.log (Real.log (Real.log (N : ℝ)))⌋₊

theorem exists_tripleLogCutoff_ge (K : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → K ≤ tripleLogCutoff N := by
  have hlog : Filter.Tendsto
      (fun x : ℝ => Real.log (Real.log (Real.log x)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have hnat : Filter.Tendsto
      (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))))
      Filter.atTop Filter.atTop :=
    hlog.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfloor : Filter.Tendsto tripleLogCutoff Filter.atTop Filter.atTop := by
    change Filter.Tendsto
      (fun N : ℕ => ⌊Real.log (Real.log (Real.log (N : ℝ)))⌋₊)
      Filter.atTop Filter.atTop
    exact tendsto_nat_floor_atTop.comp hnat
  have hev := hfloor.eventually (Filter.eventually_ge_atTop K)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  exact ⟨N₀, hN₀⟩

theorem eventually_engelsma_primorial_coverage :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple
        (primorial (tripleLogCutoff N)) := by
  obtain ⟨N₀, hN₀⟩ := exists_tripleLogCutoff_ge 600
  refine ⟨N₀, ?_⟩
  intro N hN
  apply coversShiftDifferencePrimes_of_diameter
  intro a b hab
  exact (engelsmaTuple_shiftDiameterBound hab).trans (hN₀ N hN)

end BoundedGaps.Maynard
