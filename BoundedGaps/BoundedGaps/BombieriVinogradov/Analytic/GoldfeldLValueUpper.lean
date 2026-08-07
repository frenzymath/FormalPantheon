import BoundedGaps.BombieriVinogradov.Analytic.QuadraticRealZeroGap

/-!
# The equation-(12.11) L-value upper bound

The near-one mean-value estimate and the all-nonprincipal value estimate are
combined into one source-shaped bound valid for every real zero at or below
one.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 124,
equation (12.11). Semantic review: `SEM-550`.
-/

noncomputable section

namespace BoundedGaps.Maynard

/-- Explicit norm strengthening of equation (12.11), with no primitivity or
quadraticity hypothesis. -/
theorem norm_LFunction_one_of_real_zero_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {beta : ℝ} (hbetaOne : beta ≤ 1)
    (hzero : DirichletCharacter.LFunction chi (beta : ℂ) = 0) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      512 * (1 - beta) * (q : ℝ) ^ ((1 - beta) / 2) *
        (Real.log (q : ℝ)) ^ 2 := by
  let L := Real.log (q : ℝ)
  let Q := (q : ℝ) ^ ((1 - beta) / 2)
  have hLpos : 0 < L := by
    exact Real.log_pos (by exact_mod_cast hq)
  have hdelta : 0 ≤ 1 - beta := sub_nonneg.mpr hbetaOne
  have hqOne : (1 : ℝ) ≤ q := by
    exact_mod_cast hq.le
  have hQone : 1 ≤ Q := by
    exact Real.one_le_rpow hqOne (div_nonneg hdelta (by norm_num))
  by_cases hbetaNear : 1 - 1 / (4 * L) ≤ beta
  · have hmean := norm_LFunction_one_sub_ofReal_le hq chi hchi
      (by simpa [L] using hbetaNear) hbetaOne
    have hbase :
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          512 * L ^ 2 * (1 - beta) := by
      simpa [hzero, L] using hmean
    calc
      ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          512 * L ^ 2 * (1 - beta) := hbase
      _ = 512 * (1 - beta) * 1 * L ^ 2 := by ring
      _ ≤ 512 * (1 - beta) * Q * L ^ 2 := by gcongr
      _ = 512 * (1 - beta) * (q : ℝ) ^ ((1 - beta) / 2) *
          (Real.log (q : ℝ)) ^ 2 := rfl
  · have hfar : 1 / (4 * L) < 1 - beta := by
      linarith
    have hvalue :
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤ 32 * L := by
      simpa [L] using
        norm_LFunction_near_one_le hq chi hchi (s := (1 : ℂ))
          (by
            have hfrac : 0 ≤ 5 / (16 * L) := by positivity
            simpa [L] using sub_le_self (1 : ℝ) hfrac)
          (by norm_num)
    calc
      ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤ 32 * L := hvalue
      _ ≤ 128 * L := by nlinarith
      _ = 512 * (1 / (4 * L)) * 1 * L ^ 2 := by
        field_simp [hLpos.ne']
        ring
      _ ≤ 512 * (1 - beta) * Q * L ^ 2 := by gcongr
      _ = 512 * (1 - beta) * (q : ℝ) ^ ((1 - beta) / 2) *
          (Real.log (q : ℝ)) ^ 2 := rfl

end BoundedGaps.Maynard
