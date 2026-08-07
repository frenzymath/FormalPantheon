import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Smooth Mellin inversion for an absolutely convergent L-series

This file proves the generic form of Koukoulopoulos equation (7.8).  The
vertical integral is a Bochner integral over the real line, so the source
factor `1 / (2 * pi * I)` becomes `1 / (2 * pi)` after upward
parameterization.

Semantic review: `SEM-553`.
-/

noncomputable section

open Complex MeasureTheory

namespace BoundedGaps.Maynard

private lemma cpow_div_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x / y : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (y : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (div_ne_zero hx.ne' hy.ne')),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.exp_sub]
  congr 1
  rw [← sub_mul]
  congr 1
  rw [← Complex.ofReal_log (div_nonneg hx.le hy.le),
    Real.log_div hx.ne' hy.ne', Complex.ofReal_sub,
    Complex.ofReal_log hx.le, Complex.ofReal_log hy.le]

private lemma cpow_neg_div_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x / y : ℝ) : ℂ) ^ (-s) =
      (x : ℂ) ^ (-s) * (y : ℂ) ^ s := by
  rw [cpow_div_of_pos hx hy, Complex.cpow_neg, Complex.cpow_neg,
    div_inv_eq_mul]

/-- Smooth Mellin inversion after interchanging an absolutely convergent
L-series with the full vertical integral. -/
theorem smoothMellinLSeriesInversion
    (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (phi : ℝ → ℂ) {alpha x : ℝ}
    (_halpha : 0 < alpha) (hx : 0 < x)
    (hsum : LSeriesSummable a (alpha : ℂ))
    (hphi : MellinConvergent phi (alpha : ℂ))
    (hphiVertical : VerticalIntegrable (mellin phi) alpha)
    (hphiContinuous : Continuous phi) :
    (∑' n : ℕ, a n * phi ((n : ℝ) / x)) =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t : ℝ,
          LSeries a ((alpha : ℂ) + t * I) *
            mellin phi ((alpha : ℂ) + t * I) *
            (x : ℂ) ^ ((alpha : ℂ) + t * I) := by
  let s : ℝ → ℂ := fun t => (alpha : ℂ) + t * I
  let phiLine : ℝ → ℂ := fun t => mellin phi (s t)
  let F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term a (s t) n * phiLine t * (x : ℂ) ^ (s t)
  let G : ℝ → ℂ := fun t =>
    LSeries a (s t) * phiLine t * (x : ℂ) ^ (s t)
  have hsContinuous : Continuous s := by
    fun_prop
  have hxPowContinuous : Continuous fun t : ℝ => (x : ℂ) ^ (s t) := by
    exact continuous_const.cpow hsContinuous fun _ =>
      Complex.ofReal_mem_slitPlane.mpr hx
  have htermContinuous (n : ℕ) :
      Continuous fun t : ℝ => LSeries.term a (s t) n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))
    · have hnReal : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hpow : Continuous fun t : ℝ => (n : ℂ) ^ (s t) := by
        exact continuous_const.cpow hsContinuous fun _ => by
          simpa only [← Complex.ofReal_natCast] using
            Complex.ofReal_mem_slitPlane.mpr hnReal
      have hpowNe (t : ℝ) : (n : ℂ) ^ (s t) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr <| Or.inl <| Nat.cast_ne_zero.mpr hn
      simp only [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hpow hpowNe
  have hphiLineIntegrable : Integrable phiLine := by
    simpa [VerticalIntegrable, phiLine, s] using hphiVertical
  have hmultiplierContinuous (n : ℕ) : Continuous fun t : ℝ =>
      LSeries.term a (s t) n * (x : ℂ) ^ (s t) :=
    (htermContinuous n).mul hxPowContinuous
  have hmultiplierNorm (n : ℕ) (t : ℝ) :
      ‖LSeries.term a (s t) n * (x : ℂ) ^ (s t)‖ =
        ‖LSeries.term a (alpha : ℂ) n‖ * x ^ alpha := by
    rw [norm_mul, LSeries.norm_term_eq, LSeries.norm_term_eq,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [s]
  have hFIntegrable (n : ℕ) : Integrable (F n) := by
    have h := hphiLineIntegrable.mul_bdd
      (hmultiplierContinuous n).aestronglyMeasurable
      (ae_of_all _ fun t => (hmultiplierNorm n t).le)
    convert h using 1
    funext t
    simp only [F, phiLine]
    ring
  have hFNormIntegral (n : ℕ) :
      (∫ t : ℝ, ‖F n t‖) =
        ‖LSeries.term a (alpha : ℂ) n‖ * x ^ alpha *
          ∫ t : ℝ, ‖phiLine t‖ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [show F n t = phiLine t *
        (LSeries.term a (s t) n * (x : ℂ) ^ (s t)) by
      simp only [F]
      ring]
    rw [norm_mul, hmultiplierNorm]
    ring
  have hFNormSummable : Summable fun n : ℕ => ∫ t : ℝ, ‖F n t‖ := by
    refine (hsum.norm.mul_right
      (x ^ alpha * ∫ t : ℝ, ‖phiLine t‖)).congr ?_
    intro n
    rw [hFNormIntegral]
    ring
  have hFHasSum (t : ℝ) : HasSum (fun n : ℕ => F n t) (G t) := by
    have hline : LSeriesSummable a (s t) :=
      hsum.of_re_le_re (by simp [s])
    have h := (hline.LSeriesHasSum.mul_right (phiLine t)).mul_right
      ((x : ℂ) ^ (s t))
    simpa [F, G] using h
  have hinterchange : HasSum (fun n : ℕ => ∫ t : ℝ, F n t)
      (∫ t : ℝ, G t) := by
    have h := hasSum_integral_of_summable_integral_norm hFIntegrable hFNormSummable
    rw [← integral_congr_ae
      (ae_of_all _ fun t => (hFHasSum t).tsum_eq)]
    exact h
  have hterm (n : ℕ) :
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) * (∫ t : ℝ, F n t) =
        a n * phi ((n : ℝ) / x) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha0, F]
    · have hnReal : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hratio : 0 < (n : ℝ) / x := div_pos hnReal hx
      have hpoint (t : ℝ) : F n t =
          a n * (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t := by
        dsimp only [F]
        rw [LSeries.term_def₀ ha0, cpow_neg_div_of_pos hnReal hx]
        simp only [Complex.ofReal_natCast]
        ring
      have hintegral : (∫ t : ℝ, F n t) =
          a n * ∫ t : ℝ,
            (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t := by
        calc
          (∫ t : ℝ, F n t) = ∫ t : ℝ,
              a n * ((((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t) := by
            apply integral_congr_ae
            exact ae_of_all _ fun t => by rw [hpoint]; ring
          _ = a n * ∫ t : ℝ,
              (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t :=
            MeasureTheory.integral_const_mul _ _
      have hinversion := mellinInv_mellin_eq alpha phi hratio hphi
        hphiVertical (hphiContinuous.continuousAt)
      have hinversion' :
          (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
              (∫ t : ℝ,
                (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t) =
            phi ((n : ℝ) / x) := by
        simpa [mellinInv, s, phiLine, smul_eq_mul, div_eq_mul_inv,
          mul_comm] using hinversion
      rw [hintegral, ← mul_assoc, mul_comm _ (a n), mul_assoc,
        hinversion']
  have hscaled := hinterchange.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  have hsumSmoothed : HasSum (fun n : ℕ =>
      a n * phi ((n : ℝ) / x))
      ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ t : ℝ, G t) :=
    hscaled.congr_fun fun n => (hterm n).symm
  simpa [G, phiLine, s] using hsumSmoothed.tsum_eq

end BoundedGaps.Maynard
