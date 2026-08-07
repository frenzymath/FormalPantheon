import BoundedGaps.BombieriVinogradov.Analytic.HalfIntegerPerronKernel

/-!
# The reciprocal envelope for the finite Perron kernel

This file makes the removable value at zero in the source's reciprocal
envelope explicit. The resulting continuous function pointwise dominates the
sine quotient and agrees almost everywhere with the printed expression.

Source: `AkbaryHambrook2013v2`, Section 6, p. 17, after equation (6.3).
Semantic review: `SEM-453`.
-/

open MeasureTheory

namespace BoundedGaps.Maynard

noncomputable section

/-- The continuous representative of `min (1 / |t|) B` for nonnegative `B`.
The explicit zero branch also gives the correct boundary function at `B=0`.
-/
noncomputable def perronEnvelope (B t : ℝ) : ℝ :=
  if B = 0 then 0 else (max |t| B⁻¹)⁻¹

/-- The removable value of the reciprocal envelope is its finite height. -/
theorem perronEnvelope_zero {B : ℝ} (hB : 0 ≤ B) :
    perronEnvelope B 0 = B := by
  by_cases hB0 : B = 0
  · simp [perronEnvelope, hB0]
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    rw [perronEnvelope, if_neg hB0, abs_zero,
      max_eq_right (inv_nonneg.mpr hBpos.le), inv_inv]

/-- Away from zero, the continuous envelope is the literal source minimum. -/
theorem perronEnvelope_of_ne {B t : ℝ} (hB : 0 ≤ B) (ht : t ≠ 0) :
    perronEnvelope B t = min |t|⁻¹ B := by
  by_cases hB0 : B = 0
  · simp [perronEnvelope, hB0, inv_nonneg]
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  rw [perronEnvelope, if_neg hB0]
  rcases le_total |t| B⁻¹ with h | h
  · rw [max_eq_right h, inv_inv, min_eq_right]
    exact (le_inv_comm₀ hBpos (abs_pos.mpr ht)).2 h
  · rw [max_eq_left h, min_eq_left]
    exact (inv_le_comm₀ (abs_pos.mpr ht) hBpos).2 h

/-- The totalized reciprocal envelope is continuous for every nonnegative
height. -/
theorem continuous_perronEnvelope {B : ℝ} (hB : 0 ≤ B) :
    Continuous (perronEnvelope B) := by
  by_cases hB0 : B = 0
  · subst B
    unfold perronEnvelope
    simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  change Continuous (fun t => if B = 0 then 0 else (max |t| B⁻¹)⁻¹)
  simp only [if_neg hB0]
  apply Continuous.inv₀ (continuous_abs.max continuous_const)
  intro t
  exact ne_of_gt ((inv_pos.mpr hBpos).trans_le (le_max_right _ _))

/-- The continuous envelope and the paper's literal expression differ only at
the removable point `t=0`. -/
theorem perronEnvelope_ae_eq_min {B : ℝ} (hB : 0 ≤ B) :
    ∀ᵐ t : ℝ ∂volume, perronEnvelope B t = min |t|⁻¹ B := by
  filter_upwards [volume.ae_ne 0] with t ht
  exact perronEnvelope_of_ne hB ht

private theorem abs_mul_sinc_le_self (beta t : ℝ) (hbeta : 0 ≤ beta) :
    |beta * Real.sinc (beta * t)| ≤ beta := by
  rw [abs_mul, abs_of_nonneg hbeta]
  exact mul_le_of_le_one_right hbeta (Real.abs_sinc_le_one _)

private theorem abs_mul_sinc_le_inv (beta t : ℝ) (ht : t ≠ 0) :
    |beta * Real.sinc (beta * t)| ≤ |t|⁻¹ := by
  by_cases hb : beta = 0
  · simp [hb, abs_nonneg]
  rw [Real.sinc_of_ne_zero (mul_ne_zero hb ht)]
  have hrewrite : beta * (Real.sin (beta * t) / (beta * t)) =
      Real.sin (beta * t) / t := by
    field_simp
  rw [hrewrite, abs_div, div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.mpr (abs_nonneg t))
    (Real.abs_sin_le_one _)

/-- The continuous sine quotient is pointwise bounded by every reciprocal
envelope whose height bounds its nonnegative frequency. -/
theorem abs_mul_sinc_le_perronEnvelope
    {beta B : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (t : ℝ) :
    |beta * Real.sinc (beta * t)| ≤ perronEnvelope B t := by
  have hB : 0 ≤ B := hbeta.trans hbetaB
  by_cases ht : t = 0
  · subst t
    rw [perronEnvelope_zero hB]
    simpa [abs_of_nonneg hbeta] using hbetaB
  rw [perronEnvelope_of_ne hB ht]
  exact le_min (abs_mul_sinc_le_inv beta t ht)
    ((abs_mul_sinc_le_self beta t hbeta).trans hbetaB)

/-- The source's sine-numerator envelope at a positive half-integer cutoff. -/
theorem abs_sin_mul_log_natCast_add_half_le_min
    {k : ℕ} {L : ℝ} (hk : 0 < k) (hL : 0 < L)
    (hkL : (k : ℝ) ≤ L) (t : ℝ) :
    |Real.sin (t * Real.log ((k : ℝ) + 1 / 2))| ≤
      min 1 (|t| * Real.log (2 * L)) := by
  have hbeta_nonneg : 0 ≤ Real.log ((k : ℝ) + 1 / 2) := by
    apply Real.log_nonneg
    have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hbeta_le := log_natCast_add_half_le_log_two_mul hk hL hkL
  apply le_min (Real.abs_sin_le_one _)
  calc
    |Real.sin (t * Real.log ((k : ℝ) + 1 / 2))| ≤
        |t * Real.log ((k : ℝ) + 1 / 2)| := Real.abs_sin_le_abs
    _ = |t| * Real.log ((k : ℝ) + 1 / 2) := by
      rw [abs_mul, abs_of_nonneg hbeta_nonneg]
    _ ≤ |t| * Real.log (2 * L) :=
      mul_le_mul_of_nonneg_left hbeta_le (abs_nonneg t)

/-- The oscillatory Perron phase has norm one, so the reciprocal envelope
also bounds the full continuous complex kernel. -/
theorem norm_symmetricPerronIntegrand_le_perronEnvelope
    (alpha t : ℝ) {beta B : ℝ}
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) :
    ‖symmetricPerronIntegrand alpha beta t‖ ≤ perronEnvelope B t := by
  have hphase : -Complex.I * ((t * alpha : ℝ) : ℂ) =
      ((-(t * alpha) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [symmetricPerronIntegrand, norm_mul, hphase,
    Complex.norm_exp_ofReal_mul_I]
  simpa using abs_mul_sinc_le_perronEnvelope hbeta hbetaB t

end

end BoundedGaps.Maynard
