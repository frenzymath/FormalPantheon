import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic

import Lean.Elab.Tactic.Omega

import BoundedGaps.Maynard.Distribution

/-!
# Elementary logarithmic growth bounds

The modulus-count contribution in Maynard2013v3, Section 5, is absorbed by an
arbitrary logarithmic power.  This file extracts that step from Mathlib's
little-o theorem so it can be audited independently of the sieve.
-/

namespace BoundedGaps.Maynard

theorem modulusCutoff_mono {θ : ℝ} (hθ : 0 ≤ θ) :
    Monotone (modulusCutoff θ) := by
  intro x y hxy
  apply Nat.floor_mono
  exact Real.rpow_le_rpow (by positivity)
    (by exact_mod_cast hxy) hθ

theorem exists_log_rpow_le_rpow {θ A : ℝ} (hθ : θ < 1) (_hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      Real.rpow (Real.log (N : ℝ)) A ≤ Real.rpow (N : ℝ) (1 - θ) := by
  have hs : 0 < 1 - θ := sub_pos.mpr hθ
  have hlittle := isLittleO_log_rpow_rpow_atTop A hs
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    hlittle.eventuallyLE
  rw [Filter.eventually_atTop] at hnat
  obtain ⟨N₀, hN₀⟩ := hnat
  refine ⟨max 3 N₀, le_max_left _ _, ?_⟩
  intro N hN
  have hNbase : N₀ ≤ N := le_trans (le_max_right 3 N₀) hN
  have hraw := hN₀ N hNbase
  have hN3 : 3 ≤ N := le_trans (le_max_left 3 N₀) hN
  have hNpos : 0 < (N : ℝ) := by positivity
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlog_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg (le_of_lt hNpos) _)] using hraw

theorem exists_modulus_count_mul_log_rpow_le {θ A : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ((Finset.Icc 1 (modulusCutoff θ (N - 1))).card : ℝ) *
          Real.rpow (Real.log (N : ℝ)) A ≤ (N : ℝ) := by
  obtain ⟨N₀, hN₀, hlog⟩ := exists_log_rpow_le_rpow hθ₁ hA
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  have hN3 : 3 ≤ N := le_trans hN₀ hN
  have hNpos : 0 < (N : ℝ) := by positivity
  have hN1 : 1 ≤ N := by omega
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hcut_nonneg : 0 ≤
      Real.rpow ((N - 1 : ℕ) : ℝ) θ :=
    Real.rpow_nonneg (by positivity) _
  have hcut_floor :
      ((modulusCutoff θ (N - 1) : ℕ) : ℝ) ≤
        Real.rpow ((N - 1 : ℕ) : ℝ) θ := by
    exact Nat.floor_le hcut_nonneg
  have hcast_sub_le : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.sub_le N 1)
  have hcut_le :
      ((modulusCutoff θ (N - 1) : ℕ) : ℝ) ≤
        Real.rpow (N : ℝ) θ :=
    hcut_floor.trans (Real.rpow_le_rpow (by positivity) hcast_sub_le hθ₀)
  have hcard :
      ((Finset.Icc 1 (modulusCutoff θ (N - 1))).card : ℝ) =
        (modulusCutoff θ (N - 1) : ℝ) := by
    simp [Nat.card_Icc]
  rw [hcard]
  calc
    (modulusCutoff θ (N - 1) : ℝ) *
          Real.rpow (Real.log (N : ℝ)) A ≤
        Real.rpow (N : ℝ) θ * Real.rpow (Real.log (N : ℝ)) A := by
      exact mul_le_mul_of_nonneg_right hcut_le
        (Real.rpow_nonneg hlog_nonneg _)
    _ ≤ Real.rpow (N : ℝ) θ * Real.rpow (N : ℝ) (1 - θ) := by
      exact mul_le_mul_of_nonneg_left (hlog N hN)
        (Real.rpow_nonneg (le_of_lt hNpos) _)
    _ = Real.rpow (N : ℝ) (θ + (1 - θ)) :=
      (Real.rpow_add hNpos θ (1 - θ)).symm
    _ = (N : ℝ) := by simp

end BoundedGaps.Maynard
