import BoundedGaps.BombieriVinogradov.Analytic.PrimeCountingLogSaving

/-!
# Prime-level cutoff specialization

This file places the frozen natural cutoff `floor(x^theta)` inside SEM-575's
logarithmically reduced square-root range and instantiates the exact
`hasPrimeLevel` proposition. Maynard2013v3, equation
`eq:LevelOfDistribution`, source lines 56--60, fixes the consumer quantifiers;
the scalar cutoff comparison is project-derived. Semantic review: `SEM-576`.
-/

namespace BoundedGaps.Maynard

open Filter

/-- Every fixed power cutoff strictly below one half is eventually inside the
logarithmically reduced square-root range. The scalar statement needs no sign
condition on either `theta` or `A`. -/
theorem exists_modulusCutoff_le_logReducedSqrt
    (theta A : ℝ) (htheta : theta < 1 / 2) :
    ∃ X0 : ℕ, 2 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        (modulusCutoff theta x : ℝ) ≤
          Real.sqrt (x : ℝ) /
            Real.rpow (Real.log (x : ℝ)) (A + 5) := by
  have hgap : 0 < (1 / 2 : ℝ) - theta := sub_pos.mpr htheta
  have hdom :=
    ((isLittleO_log_rpow_rpow_atTop (A + 5) hgap).comp_tendsto
      tendsto_natCast_atTop_atTop).eventuallyLE
  rw [Filter.eventually_atTop] at hdom
  obtain ⟨N, hN⟩ := hdom
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro x hx
  have hNx : N ≤ x := (le_max_right 2 N).trans hx
  have hx2 : 2 ≤ x := (le_max_left 2 N).trans hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x by omega)
  have hgrowth := hN x hNx
  simp only [Function.comp_apply, Real.norm_eq_abs] at hgrowth
  rw [abs_of_nonneg (Real.rpow_nonneg hlogpos.le (A + 5)),
    abs_of_nonneg (Real.rpow_nonneg hxpos.le ((1 / 2 : ℝ) - theta))] at hgrowth
  have hfloor :
      (modulusCutoff theta x : ℝ) ≤ Real.rpow (x : ℝ) theta := by
    exact Nat.floor_le (Real.rpow_nonneg hxpos.le theta)
  have hlogpowpos :
      0 < Real.rpow (Real.log (x : ℝ)) (A + 5) :=
    Real.rpow_pos_of_pos hlogpos _
  apply (le_div_iff₀ hlogpowpos).2
  calc
    (modulusCutoff theta x : ℝ) *
          Real.rpow (Real.log (x : ℝ)) (A + 5) ≤
        Real.rpow (x : ℝ) theta *
          Real.rpow (Real.log (x : ℝ)) (A + 5) :=
      mul_le_mul_of_nonneg_right hfloor
        (Real.rpow_nonneg hlogpos.le _)
    _ ≤ Real.rpow (x : ℝ) theta *
        Real.rpow (x : ℝ) ((1 / 2 : ℝ) - theta) :=
      mul_le_mul_of_nonneg_left hgrowth
        (Real.rpow_nonneg hxpos.le _)
    _ = Real.rpow (x : ℝ)
        (theta + ((1 / 2 : ℝ) - theta)) :=
      (Real.rpow_add hxpos theta ((1 / 2 : ℝ) - theta)).symm
    _ = Real.rpow (x : ℝ) (1 / 2 : ℝ) := by ring_nf
    _ = Real.sqrt (x : ℝ) := (Real.sqrt_eq_rpow (x : ℝ)).symm

/-- Every totalized power cutoff strictly below one half satisfies the exact
prime level proposition. The public Bombieri--Vinogradov export separately
restores the source convention `0 < theta`. -/
theorem hasPrimeLevel_of_lt_half {theta : ℝ}
    (htheta : theta < 1 / 2) :
    hasPrimeLevel theta := by
  intro A hA
  obtain ⟨C, hC, Xsave, hXsave, hsave⟩ :=
    exists_sum_maxProgressionDiscrepancy_le_logSaving_allCutoffs A hA.le
  obtain ⟨Xcut, hXcut, hcut⟩ :=
    exists_modulusCutoff_le_logReducedSqrt theta A htheta
  refine ⟨C, hC, max Xsave Xcut, ?_, ?_⟩
  · exact (show 3 ≤ Xsave by omega).trans (le_max_left _ _)
  · intro x hx
    exact hsave x ((le_max_left Xsave Xcut).trans hx)
      (modulusCutoff theta x)
      (hcut x ((le_max_right Xsave Xcut).trans hx))

end BoundedGaps.Maynard
