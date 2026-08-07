import BoundedGaps.BombieriVinogradov.Statement
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Neutral natural cutoff adapter

The two results below are scalar facts only.  They place the natural cutoff
`floor (x ^ theta)` in the natural-exponent weighted window and establish its
nonzero branch.  This module has no dependence on a Bombieri--Vinogradov
estimate or on a prime-counting/cutoff consumer theorem.
-/

namespace BoundedGaps.BombieriVinogradov

open Filter

/-- The natural cutoff is at least one once the exponent is nonnegative and
the endpoint is positive. -/
theorem one_le_modulusCutoff {theta : ℝ} {x : ℕ}
    (htheta : 0 ≤ theta) (hx : 1 ≤ x) :
    1 ≤ BoundedGaps.Maynard.modulusCutoff theta x := by
  unfold BoundedGaps.Maynard.modulusCutoff
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hx)
  have hpow : (1 : ℝ) ≤ Real.rpow (x : ℝ) theta := by
    rw [← Real.one_rpow theta]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx) htheta
  exact (Nat.one_le_floor_iff _).mpr hpow

/-- Every fixed natural power cutoff strictly below one half is eventually in
the natural-exponent square-root/logarithmic window. -/
theorem exists_modulusCutoff_le_weightedWindow
    (theta : ℝ) (B : ℕ) (htheta : theta < 1 / 2) :
    ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        (BoundedGaps.Maynard.modulusCutoff theta x : ℝ) ≤
          Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B := by
  have hgap : 0 < (1 / 2 : ℝ) - theta := sub_pos.mpr htheta
  have hdom :=
    ((isLittleO_log_rpow_rpow_atTop (B : ℝ) hgap).comp_tendsto
      tendsto_natCast_atTop_atTop).eventuallyLE
  rw [Filter.eventually_atTop] at hdom
  obtain ⟨N, hN⟩ := hdom
  refine ⟨max 4 N, le_max_left _ _, ?_⟩
  intro x hx
  have hNx : N ≤ x := (le_max_right 4 N).trans hx
  have hx4 : 4 ≤ x := (le_max_left 4 N).trans hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x by omega)
  have hscalePos : 0 < (Real.log (x : ℝ)) ^ B := pow_pos hlogpos _
  have hgrowth := hN x hNx
  simp only [Function.comp_apply, Real.norm_eq_abs] at hgrowth
  rw [abs_of_nonneg (Real.rpow_nonneg hlogpos.le (B : ℝ)),
    abs_of_nonneg (Real.rpow_nonneg hxpos.le ((1 / 2 : ℝ) - theta))] at hgrowth
  have hfloor :
      (BoundedGaps.Maynard.modulusCutoff theta x : ℝ) ≤ Real.rpow (x : ℝ) theta := by
    exact Nat.floor_le (Real.rpow_nonneg hxpos.le theta)
  apply (le_div_iff₀ hscalePos).2
  calc
    (BoundedGaps.Maynard.modulusCutoff theta x : ℝ) * (Real.log (x : ℝ)) ^ B ≤
        Real.rpow (x : ℝ) theta * (Real.log (x : ℝ)) ^ B := by
      exact mul_le_mul_of_nonneg_right hfloor (pow_nonneg hlogpos.le _)
    _ = Real.rpow (x : ℝ) theta *
        Real.rpow (Real.log (x : ℝ)) (B : ℝ) := by
      congr 1
      exact (Real.rpow_natCast (Real.log (x : ℝ)) B).symm
    _ ≤ Real.rpow (x : ℝ) theta *
        Real.rpow (x : ℝ) ((1 / 2 : ℝ) - theta) := by
      exact mul_le_mul_of_nonneg_left hgrowth
        (Real.rpow_nonneg hxpos.le _)
    _ = Real.rpow (x : ℝ)
        (theta + ((1 / 2 : ℝ) - theta)) :=
      (Real.rpow_add hxpos theta ((1 / 2 : ℝ) - theta)).symm
    _ = Real.rpow (x : ℝ) (1 / 2 : ℝ) := by ring_nf
    _ = Real.sqrt (x : ℝ) := (Real.sqrt_eq_rpow (x : ℝ)).symm

end BoundedGaps.BombieriVinogradov
