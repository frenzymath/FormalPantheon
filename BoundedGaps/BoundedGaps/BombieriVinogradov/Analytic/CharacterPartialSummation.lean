import BoundedGaps.BombieriVinogradov.Analytic.ImprimitivePolyaVinogradovPrefix
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.NumberTheory.AbelSummation

/-!
# Partial summation for nonprincipal character prefixes

This file derives the finite reciprocal Cauchy estimate and weighted-prefix
estimate used before the conditional `L(1, chi)` bridge on Koukoulopoulos,
printed p. 125. The finite statements and their endpoints are reviewed in
`SEM-543`.
-/

open MeasureTheory Set
open scoped BigOperators

namespace BoundedGaps.Maynard

private noncomputable def characterCumulative
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, chi (n : ZMod q)

private lemma characterCumulative_eq_interval
    {q : ℕ} (hq : 1 < q) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    characterCumulative chi t =
      dirichletCharacterIntervalSum 1 ⌊t⌋₊ q chi := by
  rw [characterCumulative, dirichletCharacterIntervalSum,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊t⌋₊), Finset.sum_cons]
  have hzero : chi ((0 : ℕ) : ZMod q) = 0 := by
    simpa only [Nat.cast_zero] using chi.map_zero' (Nat.ne_of_gt hq)
  rw [hzero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 ⌊t⌋₊]
  norm_num

private lemma norm_characterCumulative_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) :
    ‖characterCumulative chi t‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  rw [characterCumulative_eq_interval hq]
  exact norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    hq chi hchi ⌊t⌋₊

private lemma characterScale_nonneg {q : ℕ} (hq : 1 < q) :
    0 ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  exact mul_nonneg
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    (Real.log_pos (by exact_mod_cast hq)).le

private lemma hasDerivAt_complexOfReal_inv {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ ((u : ℂ)⁻¹))
      (-((t : ℂ) ^ 2)⁻¹) t := by
  have hcomplex : HasDerivAt (fun z : ℂ ↦ z⁻¹)
      (-((t : ℂ) ^ 2)⁻¹) (t : ℂ) :=
    hasDerivAt_inv (by exact_mod_cast ht)
  exact hcomplex.comp_ofReal

private lemma integrableOn_deriv_complexOfReal_inv
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc a b) := by
  let g : ℝ → ℂ := fun t ↦ -((t : ℂ) ^ 2)⁻¹
  have hgContinuous : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact Complex.continuous_ofReal.continuousOn.pow 2
    · intro t ht
      exact pow_ne_zero 2 (by exact_mod_cast (ha.trans_le ht.1).ne')
  apply hgContinuous.integrableOn_Icc.congr_fun _ measurableSet_Icc
  intro t ht
  exact (hasDerivAt_complexOfReal_inv (ha.trans_le ht.1).ne').deriv.symm

private lemma integral_Ioc_inv_sq
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in Ioc a b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hdiff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻¹) t := by
    intro t ht
    apply differentiableAt_inv
    have ht' : t ∈ Icc a b := by
      simpa [Set.uIcc_of_le hab] using ht
    exact (ha.trans_le ht'.1).ne'
  have hint : IntervalIntegrable
      (deriv (fun u : ℝ ↦ u⁻¹)) volume a b := by
    rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
      funext u
      exact deriv_inv]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have ht' : t ∈ Icc a b := by
        simpa [Set.uIcc_of_le hab] using ht
      exact pow_ne_zero 2 (ha.trans_le ht'.1).ne'
  have hfund := intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [intervalIntegral.integral_of_le hab] at hfund
  rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
    funext u
    exact deriv_inv] at hfund
  rw [integral_neg] at hfund
  linarith

private lemma integral_const_Ioc (C a b : ℝ) (hab : a ≤ b) :
    (∫ _t : ℝ in Ioc a b, C) = C * (b - a) := by
  rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  simp only [smul_eq_mul]
  ring

/-- A finite reciprocal Cauchy estimate obtained from the all-nonprincipal
Polya--Vinogradov prefix bound. This is not yet an identification of the
conditional infinite tail with `L(1, chi)`. -/
theorem norm_dirichletCharacterReciprocalIntervalSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (x y : ℕ) (hx : 0 < x) :
    ‖∑ n ∈ Finset.Ioc x y,
      chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
  by_cases hxy : x ≤ y
  · have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
    have hxyReal : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
    have hyReal : 0 < (y : ℝ) := hxReal.trans_le hxyReal
    let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
    have hfDiff : ∀ t ∈ Icc (x : ℝ) y,
        DifferentiableAt ℝ (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t := by
      intro t ht
      exact (hasDerivAt_complexOfReal_inv
        (hxReal.trans_le ht.1).ne').differentiableAt
    have hfInt : IntegrableOn
        (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc (x : ℝ) y) :=
      integrableOn_deriv_complexOfReal_inv hxReal
    have habel := sum_mul_eq_sub_sub_integral_mul'
      (f := fun t : ℝ ↦ ((t : ℂ)⁻¹))
      (c := fun n : ℕ ↦ chi (n : ZMod q)) hxy hfDiff hfInt
    have hrepresentation :
        (∑ n ∈ Finset.Ioc x y,
          chi (n : ZMod q) / (n : ℂ)) =
          ((y : ℂ)⁻¹ * characterCumulative chi (y : ℝ) -
            (x : ℂ)⁻¹ * characterCumulative chi (x : ℝ)) -
            ∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                characterCumulative chi t := by
      simpa [characterCumulative, div_eq_mul_inv, mul_comm] using habel
    have hActual : IntegrableOn
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
          characterCumulative chi t) (Ioc (x : ℝ) y) := by
      apply (integrableOn_mul_sum_Icc
        (fun n : ℕ ↦ chi (n : ZMod q)) hxReal.le hfInt).mono_set
      exact Ioc_subset_Icc_self
    have hReciprocalContinuous : ContinuousOn
        (fun t : ℝ ↦ (t ^ 2)⁻¹) (Icc (x : ℝ) y) := by
      apply ContinuousOn.inv₀
      · exact continuousOn_id.pow 2
      · intro t ht
        exact pow_ne_zero 2 (hxReal.trans_le ht.1).ne'
    have hMajorant : IntegrableOn
        (fun t : ℝ ↦ C * (t ^ 2)⁻¹) (Ioc (x : ℝ) y) :=
      (continuousOn_const.mul hReciprocalContinuous).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hPoint : ∀ t ∈ Ioc (x : ℝ) y,
        ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
            characterCumulative chi t‖ ≤ C * (t ^ 2)⁻¹ := by
      intro t ht
      have htPos : 0 < t := hxReal.trans ht.1
      rw [(hasDerivAt_complexOfReal_inv htPos.ne').deriv, norm_mul]
      have hderivNorm : ‖-((t : ℂ) ^ 2)⁻¹‖ = (t ^ 2)⁻¹ := by
        rw [norm_neg, norm_inv, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos htPos]
      rw [hderivNorm]
      calc
        (t ^ 2)⁻¹ * ‖characterCumulative chi t‖ =
            ‖characterCumulative chi t‖ * (t ^ 2)⁻¹ := mul_comm _ _
        _ ≤ C * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_right
          (by simpa [C] using
            norm_characterCumulative_le hq chi hchi t)
          (inv_nonneg.mpr (sq_nonneg t))
    have hIntegral :
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              characterCumulative chi t‖ ≤
          C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
      calc
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              characterCumulative chi t‖ ≤
            ∫ t in Ioc (x : ℝ) y,
              ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                characterCumulative chi t‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioc (x : ℝ) y, C * (t ^ 2)⁻¹ := by
          apply setIntegral_mono_ae_restrict hActual.norm hMajorant
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hPoint t ht
        _ = C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
          rw [integral_const_mul, integral_Ioc_inv_sq hxReal hxyReal]
    have hUpper :
        ‖(y : ℂ)⁻¹ * characterCumulative chi (y : ℝ)‖ ≤
          C * (y : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (y : ℝ)⁻¹ * ‖characterCumulative chi (y : ℝ)‖ ≤
            (y : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left
          (by simpa [C] using
            norm_characterCumulative_le hq chi hchi (y : ℝ))
          (inv_nonneg.mpr hyReal.le)
        _ = C * (y : ℝ)⁻¹ := mul_comm _ _
    have hLower :
        ‖(x : ℂ)⁻¹ * characterCumulative chi (x : ℝ)‖ ≤
          C * (x : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (x : ℝ)⁻¹ * ‖characterCumulative chi (x : ℝ)‖ ≤
            (x : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left
          (by simpa [C] using
            norm_characterCumulative_le hq chi hchi (x : ℝ))
          (inv_nonneg.mpr hxReal.le)
        _ = C * (x : ℝ)⁻¹ := mul_comm _ _
    rw [hrepresentation]
    calc
      ‖((y : ℂ)⁻¹ * characterCumulative chi (y : ℝ) -
          (x : ℂ)⁻¹ * characterCumulative chi (x : ℝ)) -
          ∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              characterCumulative chi t‖ ≤
          (‖(y : ℂ)⁻¹ * characterCumulative chi (y : ℝ)‖ +
            ‖(x : ℂ)⁻¹ * characterCumulative chi (x : ℝ)‖) +
            ‖∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                characterCumulative chi t‖ := by
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (C * (y : ℝ)⁻¹ + C * (x : ℝ)⁻¹) +
          C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) :=
        add_le_add (add_le_add hUpper hLower) hIntegral
      _ = 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
        dsimp [C]
        ring
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    rw [Finset.Ioc_eq_empty_of_le hyx, Finset.sum_empty, norm_zero]
    have hNumerator :
        0 ≤ 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      nlinarith [characterScale_nonneg hq]
    exact div_nonneg hNumerator (by positivity)

/-- A weighted-prefix estimate obtained from the all-nonprincipal
Polya--Vinogradov prefix bound. -/
theorem norm_dirichletCharacterWeightedPrefixSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (y : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 y,
      (n : ℂ) * chi (n : ZMod q)‖ ≤
      4 * (y : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  by_cases hy : y = 0
  · subst y
    simp
  · have hyPos : 0 < y := Nat.pos_of_ne_zero hy
    have hyOne : 1 ≤ y := hyPos
    have hyReal : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hyOne
    let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
    have hcastDeriv (t : ℝ) :
        HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t := by
      simpa using (hasDerivAt_id (𝕜 := ℂ) (x := (t : ℂ))).comp_ofReal
    have hfDiff : ∀ t ∈ Icc (1 : ℝ) y,
        DifferentiableAt ℝ (fun u : ℝ ↦ (u : ℂ)) t := by
      intro t _
      exact (hcastDeriv t).differentiableAt
    have hfInt : IntegrableOn
        (deriv (fun u : ℝ ↦ (u : ℂ))) (Icc (1 : ℝ) y) := by
      apply (continuousOn_const : ContinuousOn
        (fun _t : ℝ ↦ (1 : ℂ)) (Icc (1 : ℝ) y)).integrableOn_Icc.congr_fun
        _ measurableSet_Icc
      intro t _
      exact (hcastDeriv t).deriv.symm
    have habel := sum_mul_eq_sub_integral_mul₀'
      (f := fun t : ℝ ↦ (t : ℂ))
      (c := fun n : ℕ ↦ chi (n : ZMod q))
      (by simpa only [Nat.cast_zero] using
        chi.map_zero' (Nat.ne_of_gt hq)) y hfDiff hfInt
    have hleft :
        (∑ n ∈ Finset.Icc 0 y,
          (n : ℂ) * chi (n : ZMod q)) =
          ∑ n ∈ Finset.Icc 1 y,
            (n : ℂ) * chi (n : ZMod q) := by
      rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le y), Finset.sum_cons]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      rw [← Finset.Icc_add_one_left_eq_Ioc 0 y]
      norm_num
    have hrepresentation :
        (∑ n ∈ Finset.Icc 1 y,
          (n : ℂ) * chi (n : ZMod q)) =
          (y : ℂ) * characterCumulative chi (y : ℝ) -
            ∫ t in Ioc (1 : ℝ) y,
              deriv (fun u : ℝ ↦ (u : ℂ)) t *
                characterCumulative chi t := by
      rw [← hleft]
      simpa [characterCumulative] using habel
    have hActual : IntegrableOn
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ (u : ℂ)) t *
          characterCumulative chi t) (Ioc (1 : ℝ) y) := by
      apply (integrableOn_mul_sum_Icc
        (fun n : ℕ ↦ chi (n : ZMod q)) zero_le_one hfInt).mono_set
      exact Ioc_subset_Icc_self
    have hMajorant : IntegrableOn
        (fun _t : ℝ ↦ C) (Ioc (1 : ℝ) y) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hPoint : ∀ t ∈ Ioc (1 : ℝ) y,
        ‖deriv (fun u : ℝ ↦ (u : ℂ)) t *
            characterCumulative chi t‖ ≤ C := by
      intro t _
      rw [(hcastDeriv t).deriv, one_mul]
      simpa [C] using norm_characterCumulative_le hq chi hchi t
    have hIntegral :
        ‖∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              characterCumulative chi t‖ ≤
          C * ((y : ℝ) - 1) := by
      calc
        ‖∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              characterCumulative chi t‖ ≤
            ∫ t in Ioc (1 : ℝ) y,
              ‖deriv (fun u : ℝ ↦ (u : ℂ)) t *
                characterCumulative chi t‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ _t in Ioc (1 : ℝ) y, C := by
          apply setIntegral_mono_ae_restrict hActual.norm hMajorant
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hPoint t ht
        _ = C * ((y : ℝ) - 1) := integral_const_Ioc C 1 y hyReal
    have hEndpoint :
        ‖(y : ℂ) * characterCumulative chi (y : ℝ)‖ ≤
          (y : ℝ) * C := by
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (by simpa [C] using
          norm_characterCumulative_le hq chi hchi (y : ℝ))
        (by positivity)
    rw [hrepresentation]
    calc
      ‖(y : ℂ) * characterCumulative chi (y : ℝ) -
          ∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              characterCumulative chi t‖ ≤
          ‖(y : ℂ) * characterCumulative chi (y : ℝ)‖ +
            ‖∫ t in Ioc (1 : ℝ) y,
              deriv (fun u : ℝ ↦ (u : ℂ)) t *
                characterCumulative chi t‖ := norm_sub_le _ _
      _ ≤ (y : ℝ) * C + C * ((y : ℝ) - 1) :=
        add_le_add hEndpoint hIntegral
      _ ≤ 4 * (y : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
        dsimp [C]
        have hscale := characterScale_nonneg hq
        nlinarith

end BoundedGaps.Maynard
