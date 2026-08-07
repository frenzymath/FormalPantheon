import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldHorizontalEdge

/-!
# Goldfeld horizontal-edge integral limits

This file applies the pointwise envelope only after the raw horizontal paths
have been proved genuinely interval-integrable. It then retains the source
orientation while sending the upper and lower sides to zero.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 58, 74,
125--127, especially (5.13), (7.9), and the proof of Theorem 12.9.
Semantic review: `SEM-557`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set Filter
open scoped Interval Topology

noncomputable section

private theorem norm_intervalIntegral_le_const_of_intervalIntegrable
    {f : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hpoint : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) :
    ‖∫ x in a..b, f x‖ ≤ M * (b - a) := by
  calc
    ‖∫ x in a..b, f x‖ ≤ ∫ x in a..b, ‖f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ _x in a..b, M :=
      intervalIntegral.integral_mono_on hab hf.norm
        intervalIntegrable_const hpoint
    _ = M * (b - a) := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
      ring

/-- The two left-to-right horizontal integrals inherit the pointwise decay;
the factor `3` is the length of the closed strip. -/
theorem exists_norm_intervalIntegral_goldfeldContourIntegrand_horizontal_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x T : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x → 1 ≤ T →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            (‖∫ sigma in (-1)..2,
              goldfeldContourIntegrand chi1 chi beta x
                ((sigma : ℂ) + T * I)‖ ≤
                3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) ∧
            (‖∫ sigma in (-1)..2,
              goldfeldContourIntegrand chi1 chi beta x
                ((sigma : ℂ) - T * I)‖ ≤
                3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) := by
  obtain ⟨A, hA, C, hC, hpoint⟩ :=
    exists_norm_goldfeldContourIntegrand_horizontal_le
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x T hbeta0 hbeta1 hx hT hzero
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTabs : 1 ≤ |T| := by simpa [abs_of_pos hTpos] using hT
  have hraw := intervalIntegrable_goldfeldContourIntegrand_horizontal
    (beta := beta) hchi1 hchi hcross (zero_lt_one.trans_le hx) hT hzero
  have hplusBound : ∀ sigma ∈ Icc (-(1 : ℝ)) 2,
      ‖goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)‖ ≤
        C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by
    intro sigma hsigma
    exact hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x sigma T hbeta0 hbeta1 hx hsigma hTabs
  have hminusBound : ∀ sigma ∈ Icc (-(1 : ℝ)) 2,
      ‖goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)‖ ≤
        C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by
    intro sigma hsigma
    have h := hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x sigma (-T) hbeta0 hbeta1 hx hsigma
      (by simpa [abs_of_pos hTpos, abs_neg] using hT)
    simpa [sub_eq_add_neg, abs_neg] using h
  have hplus := norm_intervalIntegral_le_const_of_intervalIntegrable
    (by norm_num : (-1 : ℝ) ≤ 2) hraw.1 hplusBound
  have hminus := norm_intervalIntegral_le_const_of_intervalIntegrable
    (by norm_num : (-1 : ℝ) ≤ 2) hraw.2 hminusBound
  constructor
  · calc
      ‖∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) + T * I)‖ ≤
          (C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) *
            ((2 : ℝ) - (-1)) := hplus
      _ = 3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by ring
  · calc
      ‖∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) - T * I)‖ ≤
          (C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) *
            ((2 : ℝ) - (-1)) := hminus
      _ = 3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by ring

/-- With the source orientation, the upper edge is left-to-right and the lower
edge is the negative of the left-to-right integral. Both vanish at infinity. -/
theorem exists_tendsto_goldfeldContourIntegrand_horizontal_integrals_zero :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            Tendsto
              (fun T : ℝ => ∫ sigma in (-1)..2,
                goldfeldContourIntegrand chi1 chi beta x
                  ((sigma : ℂ) + T * I)) atTop (𝓝 0) ∧
            Tendsto
              (fun T : ℝ => -(∫ sigma in (-1)..2,
                goldfeldContourIntegrand chi1 chi beta x
                  ((sigma : ℂ) - T * I))) atTop (𝓝 0) := by
  obtain ⟨A, hA, C, hC, hbound⟩ :=
    exists_norm_intervalIntegral_goldfeldContourIntegrand_horizontal_le
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x hbeta0 hbeta1 hx hzero
  let K : ℝ := 3 * C * (q : ℝ) ^ A * x ^ 2
  have hlinear : Tendsto (fun T : ℝ => 1 + T) atTop atTop := by
    simpa [add_comm] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop))
  have hsquare : Tendsto (fun T : ℝ => (1 + T) ^ 2) atTop atTop := by
    have h := tendsto_mul_self_atTop.comp hlinear
    simpa [Function.comp_def, pow_two] using h
  have hdecay : Tendsto (fun T : ℝ => K / (1 + T) ^ 2)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsquare
  have hupperNorm : Tendsto
      (fun T : ℝ => ‖∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) + T * I)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun T : ℝ => K / (1 + T) ^ 2)
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have h := (hbound q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
        beta x T hbeta0 hbeta1 hx hT hzero).1
      simpa [K, abs_of_nonneg (zero_le_one.trans hT)] using h
    · exact hdecay
  have hlowerNorm : Tendsto
      (fun T : ℝ => ‖-(∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) - T * I))‖) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun T : ℝ => K / (1 + T) ^ 2)
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have h := (hbound q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
        beta x T hbeta0 hbeta1 hx hT hzero).2
      simpa [K, norm_neg, abs_of_nonneg (zero_le_one.trans hT)] using h
    · exact hdecay
  exact ⟨tendsto_zero_iff_norm_tendsto_zero.mpr hupperNorm,
    tendsto_zero_iff_norm_tendsto_zero.mpr hlowerNorm⟩

end

end BoundedGaps.Maynard
