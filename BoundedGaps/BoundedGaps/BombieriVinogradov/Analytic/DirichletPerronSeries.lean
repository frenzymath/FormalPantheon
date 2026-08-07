import BoundedGaps.BombieriVinogradov.Analytic.DirichletPerronOneTerm
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Countable Perron inversion for an absolutely convergent L-series

This file sums the scalar estimate of `DirichletPerronOneTerm`.  The zero
index is suppressed explicitly: Mathlib's `LSeries.term` vanishes there even
when the supplied coefficient sequence does not.

Semantic review: `SEM-533`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory

noncomputable section

/-- The strict coefficient sum with the exact half-weight at the natural
endpoint, as in equation (7.2) of the source. -/
noncomputable def dirichletPerronStarredSum
    (a : ℕ → ℂ) (x : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 x, a n) + (1 / 2 : ℂ) * a x

/-- The coefficient-weighted near-diagonal part of the scalar Perron error. -/
noncomputable def dirichletPerronNearMass
    (a : ℕ → ℂ) (x : ℕ) (U : ℝ) : ℝ :=
  ∑' n : ℕ, ‖a n‖ * dirichletPerronNearError x U n

/-- The absolute L-series mass on the real line `re s = alpha`. -/
noncomputable def dirichletPerronCoefficientMass
    (a : ℕ → ℂ) (alpha : ℝ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term a (alpha : ℂ) n‖

/-- The normalized finite vertical integral of an L-series with Perron base
`y`. -/
noncomputable def dirichletPerronIntegral
    (a : ℕ → ℂ) (y alpha U : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -U..U,
      LSeries a ((alpha : ℂ) + t * I) *
        (y : ℂ) ^ ((alpha : ℂ) + t * I) /
          ((alpha : ℂ) + t * I)

private lemma cpow_div_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x / y : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (y : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_ne_zero hx.ne' hy.ne')),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), ← Complex.exp_sub]
  congr 1
  rw [← sub_mul]
  congr 1
  rw [← Complex.ofReal_log (div_nonneg hx.le hy.le),
    Real.log_div hx.ne' hy.ne', Complex.ofReal_sub,
    Complex.ofReal_log hx.le, Complex.ofReal_log hy.le]

private lemma norm_perron_series_term_le
    {a : ℕ → ℂ} {x : ℕ} {alpha : ℝ}
    (hx : 0 < x) (halpha : 0 < alpha) (n : ℕ) (t : ℝ) :
    ‖LSeries.term a ((alpha : ℂ) + t * I) n *
        (x : ℂ) ^ ((alpha : ℂ) + t * I) /
          ((alpha : ℂ) + t * I)‖ ≤
      ‖LSeries.term a (alpha : ℂ) n‖ * ((x : ℝ) ^ alpha / alpha) := by
  let s : ℂ := (alpha : ℂ) + t * I
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hsRe : s.re = alpha := by simp [s]
  have hsNorm : alpha ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    simpa [hsRe, abs_of_pos halpha] using h
  have hsNormPos : 0 < ‖s‖ := halpha.trans_le hsNorm
  have hterm : ‖LSeries.term a s n‖ = ‖LSeries.term a (alpha : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq, hsRe, Complex.ofReal_re]
  have hxPow : ‖(x : ℂ) ^ s‖ = (x : ℝ) ^ alpha := by
    simpa [hsRe] using Complex.norm_cpow_eq_rpow_re_of_pos hxR s
  have hpowNonneg : 0 ≤ (x : ℝ) ^ alpha := Real.rpow_nonneg hxR.le _
  have hdiv : (x : ℝ) ^ alpha / ‖s‖ ≤ (x : ℝ) ^ alpha / alpha :=
    div_le_div_of_nonneg_left hpowNonneg halpha hsNorm
  change ‖LSeries.term a s n * (x : ℂ) ^ s / s‖ ≤ _
  rw [norm_div, norm_mul, hterm, hxPow]
  calc
    ‖LSeries.term a (alpha : ℂ) n‖ * (x : ℝ) ^ alpha / ‖s‖ =
        ‖LSeries.term a (alpha : ℂ) n‖ *
          ((x : ℝ) ^ alpha / ‖s‖) := by ring
    _ ≤ ‖LSeries.term a (alpha : ℂ) n‖ *
          ((x : ℝ) ^ alpha / alpha) :=
      mul_le_mul_of_nonneg_left hdiv (norm_nonneg _)

private lemma integral_perron_series_term_eq
    {a : ℕ → ℂ} {x n : ℕ} {alpha U : ℝ}
    (hx : 0 < x) (hn : 0 < n) :
    (∫ t in -U..U,
      LSeries.term a ((alpha : ℂ) + t * I) n *
        (x : ℂ) ^ ((alpha : ℂ) + t * I) /
          ((alpha : ℂ) + t * I)) =
      a n * (∫ t in -U..U,
        (((x : ℝ) / n : ℝ) : ℂ) ^ ((alpha : ℂ) + t * I) /
          ((alpha : ℂ) + t * I)) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  change LSeries.term a ((alpha : ℂ) + t * I) n *
      (x : ℂ) ^ ((alpha : ℂ) + t * I) /
        ((alpha : ℂ) + t * I) =
    a n * ((((x : ℝ) / n : ℝ) : ℂ) ^ ((alpha : ℂ) + t * I) /
      ((alpha : ℂ) + t * I))
  rw [LSeries.term_of_ne_zero hn.ne', cpow_div_of_pos hxR hnR]
  simp only [Complex.ofReal_natCast]
  ring

private lemma hasSum_perron_kernel_integrals
    {a : ℕ → ℂ} {x : ℕ} {alpha U : ℝ}
    (hsum : LSeriesSummable a (alpha : ℂ))
    (hx : 0 < x) (halpha : 0 < alpha) :
    HasSum (fun n : ℕ => if n = 0 then 0 else
      a n * dirichletPerronKernel ((x : ℝ) / n) alpha U)
        (dirichletPerronIntegral a x alpha U) := by
  let F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term a ((alpha : ℂ) + t * I) n *
      (x : ℂ) ^ ((alpha : ℂ) + t * I) /
        ((alpha : ℂ) + t * I)
  let G : ℝ → ℂ := fun t =>
    LSeries a ((alpha : ℂ) + t * I) *
      (x : ℂ) ^ ((alpha : ℂ) + t * I) /
        ((alpha : ℂ) + t * I)
  let bound : ℕ → ℝ → ℝ := fun n _ =>
    ‖LSeries.term a (alpha : ℂ) n‖ * ((x : ℝ) ^ alpha / alpha)
  have hnorm : Summable fun n : ℕ => ‖LSeries.term a (alpha : ℂ) n‖ := hsum.norm
  have hboundSummable : Summable fun n : ℕ =>
      ‖LSeries.term a (alpha : ℂ) n‖ * ((x : ℝ) ^ alpha / alpha) :=
    hnorm.mul_right _
  have hinterchange : HasSum (fun n : ℕ => ∫ t in -U..U, F n t)
      (∫ t in -U..U, G t) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_ ?_
    · intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simpa [F] using
          (continuous_const.aestronglyMeasurable :
            AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))).restrict
      · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hxR : (0 : ℝ) < x := by exact_mod_cast hx
        have hs : Continuous fun t : ℝ => (alpha : ℂ) + t * I := by fun_prop
        have hsne : ∀ t : ℝ, (alpha : ℂ) + t * I ≠ 0 := by
          intro t ht
          have hre := congrArg Complex.re ht
          simp at hre
          linarith
        have hnPow : Continuous fun t : ℝ =>
            (n : ℂ) ^ ((alpha : ℂ) + t * I) := by
          exact continuous_const.cpow hs fun _ => by
            simpa only [← Complex.ofReal_natCast] using
              Complex.ofReal_mem_slitPlane.mpr hnR
        have hnPowNe : ∀ t : ℝ,
            (n : ℂ) ^ ((alpha : ℂ) + t * I) ≠ 0 := by
          intro t
          exact Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
            Nat.cast_ne_zero.mpr hn
        have hxPow : Continuous fun t : ℝ =>
            (x : ℂ) ^ ((alpha : ℂ) + t * I) := by
          exact continuous_const.cpow hs fun _ => by
            simpa only [← Complex.ofReal_natCast] using
              Complex.ofReal_mem_slitPlane.mpr hxR
        have hterm : Continuous fun t : ℝ =>
            a n / (n : ℂ) ^ ((alpha : ℂ) + t * I) :=
          continuous_const.div hnPow hnPowNe
        exact (show Continuous (F n) by
          simp only [F, LSeries.term_of_ne_zero hn]
          exact (hterm.mul hxPow).div hs hsne).aestronglyMeasurable
    · intro n
      exact ae_of_all _ fun t _ => norm_perron_series_term_le hx halpha n t
    · exact ae_of_all _ fun _ _ => hboundSummable
    · simpa only [bound, tsum_mul_right] using
        (intervalIntegrable_const : IntervalIntegrable
          (fun _ : ℝ =>
            (∑' n : ℕ, ‖LSeries.term a (alpha : ℂ) n‖) *
              ((x : ℝ) ^ alpha / alpha)) volume (-U) U)
    · exact ae_of_all _ fun t _ => by
        have htSum : LSeriesSummable a ((alpha : ℂ) + t * I) :=
          hsum.of_re_le_re (by simp)
        let K : ℂ := (x : ℂ) ^ ((alpha : ℂ) + t * I) /
          ((alpha : ℂ) + t * I)
        have hG : G t = LSeries a ((alpha : ℂ) + t * I) * K := by
          dsimp [G, K]
          ring
        rw [hG]
        exact (htSum.LSeriesHasSum.mul_right K).congr_fun fun n => by
          dsimp [F, K]
          ring
  have hscaled := hinterchange.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  rw [dirichletPerronIntegral]
  refine hscaled.congr_fun ?_
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [F]
  · rw [if_neg hn]
    rw [integral_perron_series_term_eq hx (Nat.pos_of_ne_zero hn)]
    rw [dirichletPerronKernel]
    ring

private lemma tsum_naturalWeight_eq_starredSum
    {a : ℕ → ℂ} {x : ℕ} (hx : 0 < x) :
    (∑' n : ℕ, if n = 0 then 0 else
      a n * (dirichletPerronNaturalWeight x n : ℂ)) =
        dirichletPerronStarredSum a x := by
  rw [tsum_eq_sum (s := Finset.Ico 1 (x + 1)) (by
    intro n hn
    have hnot : ¬(1 ≤ n ∧ n < x + 1) := by
      simpa only [Finset.mem_Ico] using hn
    by_cases hnZero : n = 0
    · simp [hnZero]
    · have hnx : x < n := by omega
      simp [hnZero, dirichletPerronNaturalWeight,
        not_lt_of_ge hnx.le, ne_of_gt hnx])]
  rw [Finset.sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hx.ne')]
  rw [dirichletPerronStarredSum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    have hmem := Finset.mem_Ico.mp hn
    have hnZero : n ≠ 0 := by omega
    simp [dirichletPerronNaturalWeight, hnZero, hmem.2]
  · simp [dirichletPerronNaturalWeight, hx.ne']
    ring

private lemma summable_perron_nearMass
    (a : ℕ → ℂ) (x : ℕ) (U : ℝ) :
    Summable fun n : ℕ => ‖a n‖ * dirichletPerronNearError x U n := by
  refine summable_of_ne_finset_zero (s := Finset.range (2 * x)) ?_
  intro n hn
  have hnLower : 2 * x ≤ n := by simpa using hn
  have hnLowerR : (2 : ℝ) * x ≤ n := by exact_mod_cast hnLower
  rw [dirichletPerronNearError, if_neg]
  · simp
  · intro h
    exact (not_lt_of_ge hnLowerR) h.2.2.1

private lemma ratio_mass_identity
    {a : ℕ → ℂ} {x n : ℕ} {alpha U : ℝ} (hn : 0 < n) :
    ‖a n‖ * (32 * (((x : ℝ) / n) ^ alpha) / U) =
      (32 * (x : ℝ) ^ alpha / U) *
        ‖LSeries.term a (alpha : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, if_neg hn.ne', Complex.ofReal_re,
    Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- Absolute convergence on the Perron line makes the unnormalized finite
vertical L-series integrand interval integrable. -/
theorem intervalIntegrable_dirichletPerronLSeriesIntegrand
    {a : ℕ → ℂ} {y alpha U : ℝ}
    (hsum : LSeriesSummable a (alpha : ℂ))
    (hy : 0 < y) (halpha : 0 < alpha) :
    IntervalIntegrable
      (fun t : ℝ =>
        LSeries a ((alpha : ℂ) + t * I) *
          (y : ℂ) ^ ((alpha : ℂ) + t * I) /
            ((alpha : ℂ) + t * I))
      volume (-U) U := by
  let s : ℝ → ℂ := fun t => (alpha : ℂ) + t * I
  have hs : Continuous s := by fun_prop
  have hsne (t : ℝ) : s t ≠ 0 := by
    intro ht
    have hre := congrArg Complex.re ht
    simp [s] at hre
    exact halpha.ne' hre
  have htermContinuous (n : ℕ) :
      Continuous fun t : ℝ => LSeries.term a (s t) n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using
        (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))
    · have hnReal : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hpow : Continuous fun t : ℝ => (n : ℂ) ^ s t := by
        exact continuous_const.cpow hs fun _ => by
          simpa only [← Complex.ofReal_natCast] using
            Complex.ofReal_mem_slitPlane.mpr hnReal
      have hpowNe (t : ℝ) : (n : ℂ) ^ s t ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
          Nat.cast_ne_zero.mpr hn
      simp only [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hpow hpowNe
  have hLMeasurable : AEStronglyMeasurable
      (fun t : ℝ => LSeries a (s t))
      (volume.restrict (Set.uIoc (-U) U)) := by
    have hmeas : AEMeasurable
        (fun t : ℝ => ∑' n : ℕ, LSeries.term a (s t) n)
        (volume.restrict (Set.uIoc (-U) U)) :=
      AEMeasurable.tsum fun n => (htermContinuous n).aemeasurable
    simpa only [LSeries] using hmeas.aestronglyMeasurable
  have hyPow : Continuous fun t : ℝ => (y : ℂ) ^ s t := by
    exact continuous_const.cpow hs fun _ =>
      Complex.ofReal_mem_slitPlane.mpr hy
  have hscalar : Continuous fun t : ℝ => (y : ℂ) ^ s t / s t :=
    hyPow.div hs hsne
  have hintegrandMeasurable : AEStronglyMeasurable
      (fun t : ℝ => LSeries a (s t) * (y : ℂ) ^ s t / s t)
      (volume.restrict (Set.uIoc (-U) U)) := by
    convert hLMeasurable.mul hscalar.aestronglyMeasurable using 1
    ext t
    simp only [Pi.mul_apply]
    ring
  let M : ℝ :=
    dirichletPerronCoefficientMass a alpha * (y ^ alpha / alpha)
  have hmassNonneg : 0 ≤ dirichletPerronCoefficientMass a alpha :=
    tsum_nonneg fun _ => norm_nonneg _
  have hbound (t : ℝ) :
      ‖LSeries a (s t) * (y : ℂ) ^ s t / s t‖ ≤ M := by
    have hsRe : (s t).re = alpha := by simp [s]
    have hline : LSeriesSummable a (s t) :=
      hsum.of_re_le_re (by simp [s])
    have hL : ‖LSeries a (s t)‖ ≤
        dirichletPerronCoefficientMass a alpha := by
      calc
        ‖LSeries a (s t)‖ ≤ ∑' n : ℕ, ‖LSeries.term a (s t) n‖ :=
          norm_tsum_le_tsum_norm hline.norm
        _ = dirichletPerronCoefficientMass a alpha := by
          rw [dirichletPerronCoefficientMass]
          apply tsum_congr
          intro n
          simp only [LSeries.norm_term_eq, hsRe, Complex.ofReal_re]
    have hsNorm : alpha ≤ ‖s t‖ := by
      have h := Complex.abs_re_le_norm (s t)
      simpa [hsRe, abs_of_pos halpha] using h
    have hyNorm : ‖(y : ℂ) ^ s t / s t‖ ≤ y ^ alpha / alpha := by
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hsRe]
      exact div_le_div_of_nonneg_left
        (Real.rpow_nonneg hy.le alpha) halpha hsNorm
    rw [show LSeries a (s t) * (y : ℂ) ^ s t / s t =
        LSeries a (s t) * ((y : ℂ) ^ s t / s t) by ring,
      norm_mul]
    dsimp [M]
    calc
      ‖LSeries a (s t)‖ * ‖(y : ℂ) ^ s t / s t‖ ≤
          dirichletPerronCoefficientMass a alpha *
            ‖(y : ℂ) ^ s t / s t‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      _ ≤ dirichletPerronCoefficientMass a alpha *
          (y ^ alpha / alpha) :=
        mul_le_mul_of_nonneg_left hyNorm hmassNonneg
  change IntervalIntegrable
    (fun t : ℝ => LSeries a (s t) * (y : ℂ) ^ s t / s t)
    volume (-U) U
  exact intervalIntegrable_const.mono_fun' hintegrandMeasurable
    (ae_restrict_of_forall_mem measurableSet_uIoc fun t _ => hbound t)

/-- Summing the scalar Perron estimate against any absolutely convergent
coefficient sequence gives the countable truncated Perron bound. -/
theorem norm_dirichletPerronStarredSum_sub_integral_le
    {a : ℕ → ℂ} {x : ℕ} {alpha U : ℝ}
    (hsum : LSeriesSummable a (alpha : ℂ))
    (hx : 0 < x) (halpha : 0 < alpha)
    (halphaUpper : alpha ≤ 2) (hU : 0 < U) :
    ‖dirichletPerronStarredSum a x -
      dirichletPerronIntegral a x alpha U‖ ≤
      dirichletPerronNearMass a x U +
        (32 * (x : ℝ) ^ alpha / U) *
          dirichletPerronCoefficientMass a alpha := by
  let weighted : ℕ → ℂ := fun n => if n = 0 then 0 else
    a n * (dirichletPerronNaturalWeight x n : ℂ)
  let kernel : ℕ → ℂ := fun n => if n = 0 then 0 else
    a n * dirichletPerronKernel ((x : ℝ) / n) alpha U
  let majorant : ℕ → ℝ := fun n =>
    ‖a n‖ * dirichletPerronNearError x U n +
      (32 * (x : ℝ) ^ alpha / U) *
        ‖LSeries.term a (alpha : ℂ) n‖
  have hweighted : Summable weighted := by
    refine summable_of_ne_finset_zero (s := Finset.Ico 1 (x + 1)) ?_
    intro n hn
    have hnot : ¬(1 ≤ n ∧ n < x + 1) := by
      simpa only [Finset.mem_Ico] using hn
    by_cases hnZero : n = 0
    · simp [weighted, hnZero]
    · have hnx : x < n := by omega
      simp [weighted, hnZero, dirichletPerronNaturalWeight,
        not_lt_of_ge hnx.le, ne_of_gt hnx]
  have hkernelHasSum : HasSum kernel (dirichletPerronIntegral a x alpha U) := by
    simpa only [kernel] using hasSum_perron_kernel_integrals hsum hx halpha
  have hnear := summable_perron_nearMass a x U
  have hcoefficient : Summable fun n : ℕ =>
      (32 * (x : ℝ) ^ alpha / U) *
        ‖LSeries.term a (alpha : ℂ) n‖ :=
    hsum.norm.mul_left _
  have hmajorant : Summable majorant := hnear.add hcoefficient
  have hterm : ∀ n : ℕ, ‖weighted n - kernel n‖ ≤ majorant n := by
    intro n
    dsimp [weighted, kernel, majorant]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [dirichletPerronNearError]
    · have hnPos := Nat.pos_of_ne_zero hn
      simp only [if_neg hn]
      have hscalar := norm_dirichletPerronKernel_sub_naturalWeight_le
        hx hnPos halpha halphaUpper hU
      have hmul := mul_le_mul_of_nonneg_left hscalar (norm_nonneg (a n))
      rw [← norm_mul, mul_sub, norm_sub_rev] at hmul
      calc
        ‖a n * (dirichletPerronNaturalWeight x n : ℂ) -
            a n * dirichletPerronKernel ((x : ℝ) / n) alpha U‖
            ≤ ‖a n‖ * (dirichletPerronNearError x U n +
                32 * (((x : ℝ) / n) ^ alpha) / U) := hmul
        _ = ‖a n‖ * dirichletPerronNearError x U n +
            (32 * (x : ℝ) ^ alpha / U) *
              ‖LSeries.term a (alpha : ℂ) n‖ := by
          rw [mul_add, ratio_mass_identity hnPos]
  have herrorNorm : Summable fun n : ℕ => ‖weighted n - kernel n‖ :=
    hmajorant.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have hstar : ∑' n : ℕ, weighted n = dirichletPerronStarredSum a x := by
    simpa only [weighted] using tsum_naturalWeight_eq_starredSum (a := a) hx
  calc
    ‖dirichletPerronStarredSum a x -
        dirichletPerronIntegral a x alpha U‖ =
        ‖∑' n : ℕ, (weighted n - kernel n)‖ := by
      rw [← hstar, ← hkernelHasSum.tsum_eq,
        hweighted.tsum_sub hkernelHasSum.summable]
    _ ≤ ∑' n : ℕ, ‖weighted n - kernel n‖ :=
      norm_tsum_le_tsum_norm herrorNorm
    _ ≤ ∑' n : ℕ, majorant n :=
      herrorNorm.tsum_le_tsum hterm hmajorant
    _ = dirichletPerronNearMass a x U +
        (32 * (x : ℝ) ^ alpha / U) *
          dirichletPerronCoefficientMass a alpha := by
      rw [hnear.tsum_add hcoefficient, tsum_mul_left]
      rfl

end

end BoundedGaps.Maynard
