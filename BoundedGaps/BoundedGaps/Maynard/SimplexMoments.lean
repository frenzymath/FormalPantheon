import BoundedGaps.Maynard.Variational
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Base case for Maynard simplex moments

This file records the checked one-dimensional base case for the simplex
monomial calculation.  The proof uses Mathlib's complex Beta integral, then
transports the `Fin 1` product volume to `ℝ`.  Higher-dimensional moments are
still an explicit analytic obligation; this theorem fixes the normalization
needed by any eventual dimension induction.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators Pointwise

noncomputable section

def maynardSimplexOneMonomial (a b : ℕ) (t : Fin 1 → ℝ) : ℝ :=
  (1 - ∑ i, t i) ^ b * (t 0) ^ a

private lemma prod_nat_add_one_factorial_mul (a b : ℕ) :
    (Finset.prod (Finset.range (b + 1))
      (fun j => ((a + 1 : ℕ) : ℂ) + (j : ℂ))) *
        (a.factorial : ℂ) = ((a + b + 1).factorial : ℂ) := by
  have hn :
      Finset.prod (Finset.range (b + 1)) (fun j => (a + 1) + j) =
        (a + 1).ascFactorial (b + 1) := by
    exact (Nat.ascFactorial_eq_prod_range (a + 1) (b + 1)).symm
  have hfac : a.factorial * (a + 1).ascFactorial (b + 1) =
      (a + b + 1).factorial := by
    simpa [Nat.add_assoc] using Nat.factorial_mul_ascFactorial a (b + 1)
  have hnat :
      Finset.prod (Finset.range (b + 1)) (fun j => (a + 1) + j) * a.factorial =
        (a + b + 1).factorial := by
    rw [hn, mul_comm]
    exact hfac
  exact_mod_cast hnat

private lemma prod_nat_add_one_factorial (a b : ℕ) :
    Finset.prod (Finset.range (b + 1))
        (fun j => ((a + 1 : ℕ) : ℂ) + (j : ℂ)) =
      ((a + b + 1).factorial : ℂ) / (a.factorial : ℂ) := by
  rw [eq_div_iff]
  · exact prod_nat_add_one_factorial_mul a b
  · exact_mod_cast (Nat.factorial_ne_zero a)

theorem betaNatIntegral (a b : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, x ^ a * (1 - x) ^ b) =
      (a.factorial : ℝ) * b.factorial / (a + b + 1).factorial := by
  have hu : 0 < (((a + 1 : ℕ) : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast Nat.zero_lt_succ a
  have h := Complex.betaIntegral_eval_nat_add_one_right
    (u := ((a + 1 : ℕ) : ℂ)) hu b
  rw [Complex.betaIntegral] at h
  norm_num [Complex.cpow_natCast] at h
  have hleft :
      (∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) ^ a * (1 - (x : ℂ)) ^ b) =
        ∫ x : ℝ in (0 : ℝ)..1,
          ((x ^ a * (1 - x) ^ b : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    norm_cast
  rw [hleft, intervalIntegral.integral_ofReal] at h
  simp_rw [show (a : ℂ) + 1 = ((a + 1 : ℕ) : ℂ) by push_cast; ring] at h
  rw [prod_nat_add_one_factorial] at h
  apply Complex.ofReal_inj.mp
  refine h.trans ?_
  push_cast
  field_simp

theorem maynardSimplex_one_monomial_integral (a b : ℕ) :
    (∫ t in maynardSimplex 1, maynardSimplexOneMonomial a b t) =
      (a.factorial : ℝ) * b.factorial / (a + b + 1).factorial := by
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have he := volume_preserving_piUnique (fun _ : Fin 1 => ℝ)
  have hmem (t : Fin 1 → ℝ) :
      t ∈ maynardSimplex 1 ↔ e t ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [maynardSimplex, maynardCube, maynardCubeOf, Set.mem_setOf_eq,
      Fin.sum_univ_succ]
    constructor
    · intro ht
      have hcoord : t 0 ∈ Set.Icc (0 : ℝ) 1 := ht.1 0 (by simp)
      have heq : e t = t 0 := by simp [e]
      rw [heq]
      exact ⟨hcoord.1, by simpa using ht.2⟩
    · intro ht
      have hcoord : t 0 ∈ Set.Icc (0 : ℝ) 1 := by simpa [e] using ht
      have hcube : t ∈ Set.univ.pi (fun _ : Fin 1 => Set.Icc (0 : ℝ) 1) := by
        intro i hi
        fin_cases i
        exact hcoord
      exact ⟨hcube, by simpa using hcoord.2⟩
  have hfun :
      (maynardSimplex 1).indicator (maynardSimplexOneMonomial a b) =
        (fun t : Fin 1 → ℝ => (Set.Icc (0 : ℝ) 1).indicator
          (fun y : ℝ => y ^ a * (1 - y) ^ b) (e t)) := by
    funext t
    by_cases ht : t ∈ maynardSimplex 1
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ((hmem t).mp ht)]
      simp [maynardSimplexOneMonomial, e]
      ring
    · simp [Set.indicator, ht, (hmem t).not.mp ht]
  calc
    (∫ t in maynardSimplex 1, maynardSimplexOneMonomial a b t) =
        ∫ t, (maynardSimplex 1).indicator
          (maynardSimplexOneMonomial a b) t :=
      (MeasureTheory.integral_indicator (maynardSimplex_measurable (k := 1))).symm
    _ = ∫ t, (Set.Icc (0 : ℝ) 1).indicator
          (fun y : ℝ => y ^ a * (1 - y) ^ b) (e t) := by rw [hfun]
    _ = ∫ y, (Set.Icc (0 : ℝ) 1).indicator
          (fun y : ℝ => y ^ a * (1 - y) ^ b) y := he.integral_comp' _
    _ = ∫ y in Set.Icc (0 : ℝ) 1, y ^ a * (1 - y) ^ b := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ y : ℝ in (0 : ℝ)..1, y ^ a * (1 - y) ^ b := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      exact setIntegral_congr_set Ioc_ae_eq_Icc.symm
    _ = (a.factorial : ℝ) * b.factorial / (a + b + 1).factorial :=
      betaNatIntegral a b

/-! The scaled-simplex API used by the higher-dimensional induction step. -/

def maynardSimplexRadius (k : ℕ) (r : ℝ) : Set (Fin k → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ r}

theorem maynardSimplexRadius_measurable (k : ℕ) (r : ℝ) :
    MeasurableSet (maynardSimplexRadius k r) := by
  unfold maynardSimplexRadius
  measurability

theorem maynardSimplex_eq_radius (k : ℕ) :
    maynardSimplex k = maynardSimplexRadius k 1 := by
  ext t
  constructor
  · intro ht
    refine ⟨fun i => (ht.1 i (by simp)).1, ht.2⟩
  · intro ht
    refine ⟨?_, ht.2⟩
    intro i hi
    refine ⟨ht.1 i, ?_⟩
    calc
      t i ≤ ∑ j, t j := Finset.single_le_sum (fun j hj => ht.1 j) (by simp)
      _ ≤ 1 := ht.2

theorem smul_simplexRadius_one (k : ℕ) {r : ℝ} (hr : 0 < r) :
    r • maynardSimplexRadius k 1 = maynardSimplexRadius k r := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => mul_nonneg hr.le (hu.1 i), ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hu.2 hr.le).trans_eq (mul_one r)
  · intro ht
    refine ⟨r⁻¹ • t, ?_, ?_⟩
    · refine ⟨fun i => mul_nonneg (inv_nonneg.mpr hr.le) (ht.1 i), ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      calc
        r⁻¹ * ∑ i, t i ≤ r⁻¹ * r :=
          mul_le_mul_of_nonneg_left ht.2 (inv_nonneg.mpr hr.le)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · ext i
      simp [hr.ne']

def maynardSimplexRadiusMonomial (k : ℕ) (r : ℝ) (a : Fin k → ℕ) (b : ℕ)
    (t : Fin k → ℝ) : ℝ :=
  (r - ∑ i, t i) ^ b * ∏ i, (t i) ^ a i

theorem radiusMonomial_measurable (k : ℕ) (r : ℝ) (a : Fin k → ℕ) (b : ℕ) :
    Measurable (maynardSimplexRadiusMonomial k r a b) := by
  unfold maynardSimplexRadiusMonomial
  fun_prop

theorem radiusMonomial_norm_le_one (k : ℕ) (a : Fin k → ℕ) (b : ℕ)
    (t : Fin k → ℝ) (ht : t ∈ maynardSimplexRadius k 1) :
    ‖maynardSimplexRadiusMonomial k 1 a b t‖ ≤ 1 := by
  have hsimplex : t ∈ maynardSimplex k := by
    rw [maynardSimplex_eq_radius]
    exact ht
  have hsum_nonneg : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i hi => ht.1 i
  have hslack : ‖1 - ∑ i, t i‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
    linarith
  have hcoord (i : Fin k) : ‖t i‖ ≤ 1 := by
    have hi := hsimplex.1 i (by simp)
    rw [Real.norm_eq_abs, abs_of_nonneg hi.1]
    exact hi.2
  unfold maynardSimplexRadiusMonomial
  rw [norm_mul, norm_pow, norm_prod]
  simp_rw [norm_pow]
  have hpow : ‖1 - ∑ i, t i‖ ^ b ≤ 1 := by
    simpa using pow_le_one₀ (norm_nonneg _) hslack
  have hprod : ∏ i, ‖t i‖ ^ a i ≤ 1 := by
    calc
      ∏ i, ‖t i‖ ^ a i ≤ ∏ _i : Fin k, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          simpa using pow_le_one₀ (norm_nonneg _) (hcoord i)
      _ = 1 := by simp
  calc
    ‖1 - ∑ i, t i‖ ^ b * ∏ i, ‖t i‖ ^ a i ≤ 1 * 1 :=
      mul_le_mul hpow hprod (by positivity) (by positivity)
    _ = 1 := one_mul 1

theorem radiusMonomial_integrableOn_one (k : ℕ) (a : Fin k → ℕ) (b : ℕ) :
    IntegrableOn (maynardSimplexRadiusMonomial k 1 a b)
      (maynardSimplexRadius k 1) := by
  refine maynard_integrableOn_of_measurable_bounded
    (s := maynardSimplexRadius k 1)
    (hs := maynardSimplexRadius_measurable k 1)
    (hsfinite := ?_) (f := maynardSimplexRadiusMonomial k 1 a b)
    (radiusMonomial_measurable k 1 a b) 1 ?_
  · rw [← maynardSimplex_eq_radius]
    exact (measure_mono (show maynardSimplex k ⊆ maynardCube k from
      fun _ ht => ht.1)).trans_lt (maynardCube_measure_lt_top k)
  · intro t ht
    exact radiusMonomial_norm_le_one k a b t ht

theorem radius_one_dim_monomial_integral (a : Fin 1 → ℕ) (b : ℕ) :
    (∫ t in maynardSimplexRadius 1 1,
      maynardSimplexRadiusMonomial 1 1 a b t) =
      ((a 0).factorial : ℝ) * b.factorial /
        (1 + b + ∑ i, a i).factorial := by
  rw [← maynardSimplex_eq_radius 1]
  have h := maynardSimplex_one_monomial_integral (a 0) b
  simpa [maynardSimplexRadiusMonomial, maynardSimplexOneMonomial,
    Fin.sum_univ_succ, Fin.prod_univ_succ, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

theorem radiusMonomial_smul (k : ℕ) (r : ℝ) (a : Fin k → ℕ) (b : ℕ)
    (t : Fin k → ℝ) :
    maynardSimplexRadiusMonomial k r a b (r • t) =
      r ^ (b + ∑ i, a i) * maynardSimplexRadiusMonomial k 1 a b t := by
  unfold maynardSimplexRadiusMonomial
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [show r - r * ∑ i, t i = r * (1 - ∑ i, t i) by ring, mul_pow]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add]
  ring

theorem radiusMonomial_integral_scale (k : ℕ) {r : ℝ} (hr : 0 < r)
    (a : Fin k → ℕ) (b : ℕ) :
    (∫ t in maynardSimplexRadius k r,
      maynardSimplexRadiusMonomial k r a b t) =
      r ^ (k + b + ∑ i, a i) *
        ∫ t in maynardSimplexRadius k 1,
          maynardSimplexRadiusMonomial k 1 a b t := by
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Fin k → ℝ))
    (maynardSimplexRadiusMonomial k r a b) (maynardSimplexRadius k 1) hr
  rw [smul_simplexRadius_one k hr, Module.finrank_fin_fun] at h
  simp_rw [radiusMonomial_smul] at h
  rw [MeasureTheory.integral_const_mul] at h
  simp only [smul_eq_mul] at h
  have hsolve :
      (∫ t in maynardSimplexRadius k r,
        maynardSimplexRadiusMonomial k r a b t) =
        r ^ k * (r ^ (b + ∑ i, a i) *
          ∫ t in maynardSimplexRadius k 1,
            maynardSimplexRadiusMonomial k 1 a b t) := by
    field_simp [hr.ne'] at h ⊢
    exact h.symm
  rw [hsolve]
  calc
    r ^ k * (r ^ (b + ∑ i, a i) *
        ∫ t in maynardSimplexRadius k 1,
          maynardSimplexRadiusMonomial k 1 a b t) =
      (r ^ k * r ^ (b + ∑ i, a i)) *
        ∫ t in maynardSimplexRadius k 1,
          maynardSimplexRadiusMonomial k 1 a b t := by ring
    _ = r ^ (k + (b + ∑ i, a i)) *
        ∫ t in maynardSimplexRadius k 1,
          maynardSimplexRadiusMonomial k 1 a b t := by rw [← pow_add]
    _ = r ^ (k + b + ∑ i, a i) *
        ∫ t in maynardSimplexRadius k 1,
          maynardSimplexRadiusMonomial k 1 a b t := by
      congr 2
      omega

theorem simplexRadius_piFinSuccAbove_symm_mem {n : ℕ} (r x : ℝ)
    (t : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (x, t) ∈
        maynardSimplexRadius (n + 1) r ↔
      0 ≤ x ∧ t ∈ maynardSimplexRadius n (r - x) := by
  unfold maynardSimplexRadius
  simp only [Set.mem_setOf_eq]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.forall_fin_succ, Fin.sum_univ_succ]
  constructor
  · rintro ⟨⟨hx, ht⟩, hs⟩
    exact ⟨hx, ht, by linarith⟩
  · rintro ⟨hx, ht, hs⟩
    exact ⟨⟨hx, ht⟩, by linarith⟩

theorem radiusMonomial_piFinSuccAbove_symm {n : ℕ} (a : Fin (n + 1) → ℕ)
    (b : ℕ) (x : ℝ) (t : Fin n → ℝ) :
    maynardSimplexRadiusMonomial (n + 1) 1 a b
        ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0).symm (x, t)) =
      x ^ a 0 * maynardSimplexRadiusMonomial n (1 - x)
        (fun i => a i.succ) b t := by
  unfold maynardSimplexRadiusMonomial
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

theorem simplexRadius_eq_empty_of_neg (k : ℕ) {r : ℝ} (hr : r < 0) :
    maynardSimplexRadius k r = ∅ := by
  ext t
  simp only [maynardSimplexRadius, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  intro ht
  have hsum : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i hi => ht.1 i
  linarith [ht.2]

theorem radiusMonomial_integral_succ_fiber {n : ℕ} (a : Fin (n + 1) → ℕ)
    (b : ℕ) :
    (∫ u in maynardSimplexRadius (n + 1) 1,
      maynardSimplexRadiusMonomial (n + 1) 1 a b u) =
      ∫ x in Set.Icc (0 : ℝ) 1,
        x ^ a 0 * (∫ t in maynardSimplexRadius n (1 - x),
          maynardSimplexRadiusMonomial n (1 - x) (fun i => a i.succ) b t) := by
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he := volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) 0
  let S := maynardSimplexRadius (n + 1) 1
  let f := maynardSimplexRadiusMonomial (n + 1) 1 a b
  have hfint : Integrable (S.indicator f) :=
    (radiusMonomial_integrableOn_one (n + 1) a b).integrable_indicator
      (maynardSimplexRadius_measurable (n + 1) 1)
  have hpairint :
      Integrable (fun z : ℝ × (Fin n → ℝ) => S.indicator f (e.symm z)) := by
    change Integrable ((S.indicator f) ∘ e.symm)
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
    exact ((he.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hfint
  have hpoint (x : ℝ) (t : Fin n → ℝ) :
      S.indicator f (e.symm (x, t)) =
        (Set.Ici (0 : ℝ)).indicator (fun x =>
          (maynardSimplexRadius n (1 - x)).indicator (fun t =>
            x ^ a 0 * maynardSimplexRadiusMonomial n (1 - x)
              (fun i => a i.succ) b t) t) x := by
    by_cases hx : 0 ≤ x
    · by_cases ht : t ∈ maynardSimplexRadius n (1 - x)
      · have hs : e.symm (x, t) ∈ S := by
          exact (simplexRadius_piFinSuccAbove_symm_mem 1 x t).2 ⟨hx, ht⟩
        rw [Set.indicator_of_mem hs,
          Set.indicator_of_mem (show x ∈ Set.Ici 0 by exact hx),
          Set.indicator_of_mem ht]
        exact radiusMonomial_piFinSuccAbove_symm a b x t
      · have hs : e.symm (x, t) ∉ S := by
          intro hs
          exact ht ((simplexRadius_piFinSuccAbove_symm_mem 1 x t).1 hs).2
        simp [Set.indicator, hs, hx, ht]
    · have hs : e.symm (x, t) ∉ S := by
        intro hs
        exact hx ((simplexRadius_piFinSuccAbove_symm_mem 1 x t).1 hs).1
      simp [Set.indicator, hs, hx]
  calc
    (∫ u in maynardSimplexRadius (n + 1) 1,
      maynardSimplexRadiusMonomial (n + 1) 1 a b u) =
        ∫ u, S.indicator f u := by
      exact (MeasureTheory.integral_indicator
        (maynardSimplexRadius_measurable (n + 1) 1)).symm
    _ = ∫ z : ℝ × (Fin n → ℝ), S.indicator f (e.symm z) := by
      exact ((he.symm e).integral_comp' (S.indicator f)).symm
    _ = ∫ x : ℝ, ∫ t : Fin n → ℝ, S.indicator f (e.symm (x, t)) := by
      exact integral_prod _ hpairint
    _ = ∫ x : ℝ, (Set.Ici (0 : ℝ)).indicator (fun x =>
          x ^ a 0 * (∫ t in maynardSimplexRadius n (1 - x),
            maynardSimplexRadiusMonomial n (1 - x)
              (fun i => a i.succ) b t)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp_rw [hpoint]
      by_cases hx : x ∈ Set.Ici (0 : ℝ)
      · simp only [Set.indicator_of_mem hx]
        rw [MeasureTheory.integral_indicator
          (maynardSimplexRadius_measurable n (1 - x))]
        rw [MeasureTheory.integral_const_mul]
      · simp [Set.indicator, hx]
    _ = ∫ x in Set.Ici (0 : ℝ),
          x ^ a 0 * (∫ t in maynardSimplexRadius n (1 - x),
            maynardSimplexRadiusMonomial n (1 - x)
              (fun i => a i.succ) b t) := by
      rw [MeasureTheory.integral_indicator measurableSet_Ici]
    _ = ∫ x in Set.Icc (0 : ℝ) 1,
          x ^ a 0 * (∫ t in maynardSimplexRadius n (1 - x),
            maynardSimplexRadiusMonomial n (1 - x)
              (fun i => a i.succ) b t) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
        Set.Icc_subset_Ici_self
      intro x hx
      have hxgt : 1 < x := by
        have hxnot := hx.2
        simp only [Set.mem_Icc, not_and_or, not_le] at hxnot
        rcases hxnot with hneg | hgt
        · exact False.elim ((not_lt_of_ge hx.1) hneg)
        · exact hgt
      rw [simplexRadius_eq_empty_of_neg n (by linarith : 1 - x < 0)]
      simp

theorem radius_zero_dim_monomial_integral (a : Fin 0 → ℕ) (b : ℕ) :
    (∫ t in maynardSimplexRadius 0 1,
      maynardSimplexRadiusMonomial 0 1 a b t) =
      ((∏ i, (a i).factorial : ℕ) : ℝ) * b.factorial /
        (0 + b + ∑ i, a i).factorial := by
  simp [maynardSimplexRadius, maynardSimplexRadiusMonomial]
  have hcube : maynardCubeOf (Fin 0) = Set.univ := by
    ext t
    simp [maynardCubeOf]
  have hvol : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
    rw [measureReal_def]
    have h : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      rw [← hcube]
      unfold maynardCubeOf
      rw [volume_pi_pi]
      simp
    rw [h]
    simp
  rw [hvol]
  field_simp

theorem radius_monomial_integral_formula (k : ℕ) (a : Fin k → ℕ) (b : ℕ) :
    (∫ t in maynardSimplexRadius k 1,
      maynardSimplexRadiusMonomial k 1 a b t) =
      ((∏ i, (a i).factorial : ℕ) : ℝ) * b.factorial /
        (k + b + ∑ i, a i).factorial := by
  induction k with
  | zero => exact radius_zero_dim_monomial_integral a b
  | succ n ih =>
    rw [radiusMonomial_integral_succ_fiber]
    rw [← setIntegral_congr_set (Ioo_ae_eq_Icc (α := ℝ) (μ := volume))]
    have hpoint : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        x ^ a 0 * (∫ t in maynardSimplexRadius n (1 - x),
          maynardSimplexRadiusMonomial n (1 - x) (fun i => a i.succ) b t) =
        (x ^ a 0 * (1 - x) ^ (n + b + ∑ i : Fin n, a i.succ)) *
          (((∏ i : Fin n, ((a i.succ).factorial) : ℕ) : ℝ) * b.factorial /
            (n + b + ∑ i : Fin n, a i.succ).factorial) := by
      intro x hx
      rw [radiusMonomial_integral_scale n (sub_pos.mpr hx.2)]
      rw [ih (fun i => a i.succ)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo hpoint]
    rw [MeasureTheory.integral_mul_const]
    rw [setIntegral_congr_set (Ioo_ae_eq_Icc (α := ℝ) (μ := volume))]
    rw [← setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [betaNatIntegral]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ]
    field_simp
    push_cast
    ring

theorem maynardSimplex_monomial_integral (k : ℕ) (a : Fin k → ℕ) (b : ℕ) :
    (∫ t in maynardSimplex k,
      (1 - ∑ i, t i) ^ b * ∏ i, (t i) ^ a i) =
      ((∏ i, (a i).factorial : ℕ) : ℝ) * b.factorial /
        (k + b + ∑ i, a i).factorial := by
  rw [maynardSimplex_eq_radius]
  exact radius_monomial_integral_formula k a b

end
end BoundedGaps.Maynard
