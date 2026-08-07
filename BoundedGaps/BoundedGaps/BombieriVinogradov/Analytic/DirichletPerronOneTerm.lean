import BoundedGaps.BombieriVinogradov.Analytic.DirichletPerronCentralNatural
import BoundedGaps.BombieriVinogradov.Analytic.DirichletPerronHighBase

/-!
# A uniform natural-index Perron kernel estimate

This file combines the endpoint, strict central, and closed outer estimates for
the scalar Perron kernel. The near-diagonal term explicitly excludes the jump
`n = x`; that index is controlled by the exact arctangent calculation.

Semantic review: `SEM-533`.
-/

namespace BoundedGaps.Maynard

open Complex

noncomputable section

/-- The reciprocal-distance part of the scalar Perron error. It is supported
only on positive, nonendpoint indices in the strict central range. -/
noncomputable def dirichletPerronNearError
    (x : ℕ) (U : ℝ) (n : ℕ) : ℝ :=
  if 0 < n ∧ (x : ℝ) / 2 < (n : ℝ) ∧
      (n : ℝ) < 2 * x ∧ n ≠ x then
    min 1 (2 * (x : ℝ) /
      (U * |(x : ℝ) - n|))
  else 0

@[simp]
theorem dirichletPerronNearError_zero (x : ℕ) (U : ℝ) :
    dirichletPerronNearError x U 0 = 0 := by
  simp [dirichletPerronNearError]

@[simp]
theorem dirichletPerronNearError_self (x : ℕ) (U : ℝ) :
    dirichletPerronNearError x U x = 0 := by
  simp [dirichletPerronNearError]

private lemma quarter_le_div_rpow
    {x n : ℕ} {alpha : ℝ}
    (hx : 0 < x) (hn : 0 < n)
    (hUpper : (n : ℝ) < 2 * x)
    (halpha : 0 < alpha) (halphaUpper : alpha ≤ 2) :
    (1 / 4 : ℝ) ≤ ((x : ℝ) / n) ^ alpha := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let y : ℝ := (x : ℝ) / n
  have hy : 0 < y := div_pos hxR hnR
  have hyLower : (1 / 2 : ℝ) ≤ y := by
    dsimp [y]
    rw [le_div_iff₀ hnR]
    nlinarith
  by_cases hyOne : y ≤ 1
  · have hsquare : (1 / 4 : ℝ) ≤ y ^ (2 : ℕ) := by
      nlinarith
    have hsquareReal : (1 / 4 : ℝ) ≤ y ^ (2 : ℝ) := by
      simpa [Real.rpow_two] using hsquare
    have hpower : y ^ (2 : ℝ) ≤ y ^ alpha :=
      Real.rpow_le_rpow_of_exponent_ge hy hyOne halphaUpper
    simpa [y] using hsquareReal.trans hpower
  · have hone : (1 : ℝ) ≤ y := le_of_not_ge hyOne
    have hpower : (1 : ℝ) ≤ y ^ alpha :=
      Real.one_le_rpow hone halpha.le
    dsimp [y] at hpower ⊢
    linarith

private lemma central_constant_le_ratio_power
    {x n : ℕ} {alpha U : ℝ}
    (hx : 0 < x) (hn : 0 < n)
    (hUpper : (n : ℝ) < 2 * x)
    (halpha : 0 < alpha) (halphaUpper : alpha ≤ 2)
    (hU : 0 < U) :
    20 / (Real.pi * U) ≤
      32 * (((x : ℝ) / n) ^ alpha) / U := by
  have hquarter := quarter_le_div_rpow hx hn hUpper
    halpha halphaUpper
  have hpi : 20 / Real.pi ≤ (8 : ℝ) := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hpow :
      20 / Real.pi ≤ 32 * (((x : ℝ) / n) ^ alpha) := by
    nlinarith
  calc
    20 / (Real.pi * U) = (20 / Real.pi) / U := by ring
    _ ≤ (32 * (((x : ℝ) / n) ^ alpha)) / U :=
      div_le_div_of_nonneg_right hpow hU.le

private lemma endpoint_constant_le
    {alpha U : ℝ} (halphaUpper : alpha ≤ 2) (hU : 0 < U) :
    alpha / (Real.pi * U) ≤ 32 / U := by
  have hpi : alpha / Real.pi ≤ (32 : ℝ) := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  calc
    alpha / (Real.pi * U) = (alpha / Real.pi) / U := by ring
    _ ≤ 32 / U := div_le_div_of_nonneg_right hpi hU.le

/-- At every positive natural index, the scalar kernel error is bounded by
the near-diagonal reciprocal distance plus one uniform ratio-power term. -/
theorem norm_dirichletPerronKernel_sub_naturalWeight_le
    {x n : ℕ} {alpha U : ℝ}
    (hx : 0 < x) (hn : 0 < n)
    (halpha : 0 < alpha) (halphaUpper : alpha ≤ 2)
    (hU : 0 < U) :
    ‖dirichletPerronKernel ((x : ℝ) / n) alpha U -
      (dirichletPerronNaturalWeight x n : ℂ)‖ ≤
      dirichletPerronNearError x U n +
        32 * (((x : ℝ) / n) ^ alpha) / U := by
  by_cases hne : n = x
  · subst n
    have hxR0 : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
    have hendpoint :=
      norm_dirichletPerronKernel_one_sub_half_le halpha hU
    have hbound := endpoint_constant_le halphaUpper hU
    simpa [dirichletPerronNaturalWeight_self hx, hxR0] using
      hendpoint.trans hbound
  · by_cases hLower : (x : ℝ) / 2 < (n : ℝ)
    · by_cases hUpper : (n : ℝ) < 2 * x
      · have hcentral :=
          norm_dirichletPerronKernel_sub_naturalWeight_central_le
            hx hn hLower hUpper hne halpha halphaUpper hU
        rw [dirichletPerronNearError,
          if_pos ⟨hn, hLower, hUpper, hne⟩]
        exact hcentral.trans <| add_le_add (le_refl _)
          (central_constant_le_ratio_power hx hn hUpper
            halpha halphaUpper hU)
      · have hOuter :
          (n : ℝ) ≤ (x : ℝ) / 2 ∨ 2 * x ≤ (n : ℝ) :=
          Or.inr (le_of_not_gt hUpper)
        have houter :=
          norm_dirichletPerronKernel_sub_naturalWeight_outer_le
            hx hn hOuter halpha hU
        rw [dirichletPerronNearError, if_neg (by
          intro h
          exact hUpper h.2.2.1)]
        have hyNonneg : (0 : ℝ) ≤ ((x : ℝ) / n) ^ alpha :=
          Real.rpow_nonneg (div_nonneg (by positivity) (by positivity)) _
        exact houter.trans (by
          simp only [zero_add]
          have hfactor : (1 : ℝ) ≤ 32 := by norm_num
          calc
            ((x : ℝ) / n) ^ alpha / U =
                1 * (((x : ℝ) / n) ^ alpha / U) := by ring
            _ ≤ 32 * (((x : ℝ) / n) ^ alpha / U) :=
              mul_le_mul_of_nonneg_right hfactor
                (div_nonneg hyNonneg hU.le)
            _ = 32 * ((x : ℝ) / n) ^ alpha / U := by ring)
    · have hOuter :
        (n : ℝ) ≤ (x : ℝ) / 2 ∨ 2 * x ≤ (n : ℝ) :=
        Or.inl (le_of_not_gt hLower)
      have houter :=
        norm_dirichletPerronKernel_sub_naturalWeight_outer_le
          hx hn hOuter halpha hU
      rw [dirichletPerronNearError, if_neg (by
        intro h
        exact hLower h.2.1)]
      have hyNonneg : (0 : ℝ) ≤ ((x : ℝ) / n) ^ alpha :=
        Real.rpow_nonneg (div_nonneg (by positivity) (by positivity)) _
      exact houter.trans (by
        simp only [zero_add]
        have hfactor : (1 : ℝ) ≤ 32 := by norm_num
        calc
          ((x : ℝ) / n) ^ alpha / U =
              1 * (((x : ℝ) / n) ^ alpha / U) := by ring
          _ ≤ 32 * (((x : ℝ) / n) ^ alpha / U) :=
            mul_le_mul_of_nonneg_right hfactor
              (div_nonneg hyNonneg hU.le)
          _ = 32 * ((x : ℝ) / n) ^ alpha / U := by ring)

end

end BoundedGaps.Maynard
