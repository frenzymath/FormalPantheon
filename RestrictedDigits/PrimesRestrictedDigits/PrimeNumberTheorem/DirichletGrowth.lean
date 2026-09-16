import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.SumCoeff
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPartialSums

/-!
# Growth of nonprincipal Dirichlet L-functions

This independently derives explicit bounds from the partial-summation
argument underlying `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 10, Lemma 10.15,
p. 350, and supplies the growth input used in Chapter 11, Lemma 11.1, p. 359.
-/

open Asymptotics Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimesRestrictedDigits

private noncomputable def dirichletPartialSum {q : Nat}
    (chi : DirichletCharacter Complex q) (u : Real) : Complex :=
  ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi k

private noncomputable def dirichletPartialSumTail {q : Nat}
    (chi : DirichletCharacter Complex q) (u : Real) : Complex :=
  (Ioi (1 : Real)).indicator (dirichletPartialSum chi) u

private noncomputable def dirichletPartialSumMellin {q : Nat}
    (chi : DirichletCharacter Complex q) (s : Complex) : Complex :=
  mellin (dirichletPartialSumTail chi) (-s)

private lemma measurable_dirichletPartialSum {q : Nat}
    (chi : DirichletCharacter Complex q) :
    Measurable (dirichletPartialSum chi) := by
  exact (measurable_of_countable fun n : Nat => ∑ k ∈ Finset.Icc 1 n, chi k).comp
    measurable_id.nat_floor

private lemma measurable_dirichletPartialSumTail {q : Nat}
    (chi : DirichletCharacter Complex q) :
    Measurable (dirichletPartialSumTail chi) := by
  exact (measurable_dirichletPartialSum chi).indicator measurableSet_Ioi

private lemma norm_dirichletPartialSumTail_le_level {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ≠ 1) (u : Real) :
    norm (dirichletPartialSumTail chi u) <= (q : Real) := by
  by_cases hu : 1 < u
  · simp only [dirichletPartialSumTail, indicator, mem_Ioi, if_pos hu,
      dirichletPartialSum]
    exact norm_sum_dirichletCharacter_Icc_le_level chi hchi ⌊u⌋₊
  · simp [dirichletPartialSumTail, hu]

private lemma locallyIntegrable_dirichletPartialSumTail {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ≠ 1) :
    LocallyIntegrable (dirichletPartialSumTail chi) := by
  refine (locallyIntegrable_const ((q : Real) : Complex)).mono
    (measurable_dirichletPartialSumTail chi).aestronglyMeasurable ?_
  filter_upwards with u
  simpa using norm_dirichletPartialSumTail_le_level chi hchi u

private lemma dirichletPartialSumTail_isBigO_atTop {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ≠ 1) :
    dirichletPartialSumTail chi =O[atTop] (fun _ : Real => (1 : Real)) := by
  refine isBigO_iff.mpr ⟨(q : Real), ?_⟩
  filter_upwards with u
  simpa using norm_dirichletPartialSumTail_le_level chi hchi u

private lemma dirichletPartialSumTail_isBigO_nhdsGT_zero {q : Nat}
    (chi : DirichletCharacter Complex q) (b : Real) :
    dirichletPartialSumTail chi =O[𝓝[>] 0] (fun u : Real => u ^ (-b)) := by
  have hlt : ∀ᶠ u : Real in 𝓝[>] 0, u < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hlt] with u hu
  simp [dirichletPartialSumTail, not_lt.mpr hu.le]

private lemma differentiableAt_dirichletPartialSumMellin {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ≠ 1)
    {s : Complex} (hRe : 0 < s.re) :
    DifferentiableAt Complex (dirichletPartialSumMellin chi) s := by
  have hMellin : DifferentiableAt Complex
      (mellin (dirichletPartialSumTail chi)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := 0) (b := (-s).re - 1)
      ((locallyIntegrable_dirichletPartialSumTail chi hchi).locallyIntegrableOn
        (Ioi 0)) ?_ ?_ ?_ ?_
    · simpa using dirichletPartialSumTail_isBigO_atTop chi hchi
    · simpa using hRe
    · exact dirichletPartialSumTail_isBigO_nhdsGT_zero chi _
    · linarith
  change DifferentiableAt Complex
    (fun w => mellin (dirichletPartialSumTail chi) (-w)) s
  exact hMellin.comp s differentiableAt_id.neg

private lemma dirichletPartialSumMellin_eq_integral {q : Nat}
    (chi : DirichletCharacter Complex q) (s : Complex) :
    dirichletPartialSumMellin chi s =
      ∫ u : Real in Ioi 1,
        dirichletPartialSum chi u * (u : Complex) ^ (-(s + 1)) := by
  rw [dirichletPartialSumMellin, mellin]
  simp only [smul_eq_mul]
  calc
    (∫ u : Real in Ioi 0,
        (u : Complex) ^ (-s - 1) * dirichletPartialSumTail chi u) =
        ∫ u : Real in Ioi 0, (Ioi (1 : Real)).indicator
          (fun v => (v : Complex) ^ (-s - 1) * dirichletPartialSum chi v) u := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      by_cases hu : 1 < u <;> simp [dirichletPartialSumTail, hu]
    _ = ∫ u : Real in Ioi (0 : Real) ∩ Ioi 1,
        (u : Complex) ^ (-s - 1) * dirichletPartialSum chi u := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ u : Real in Ioi 1,
        (u : Complex) ^ (-s - 1) * dirichletPartialSum chi u := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = ∫ u : Real in Ioi 1,
        dirichletPartialSum chi u * (u : Complex) ^ (-(s + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma norm_dirichletPartialSumMellin_le {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ≠ 1)
    {s : Complex} (hRe : 0 < s.re) :
    norm (dirichletPartialSumMellin chi s) <= (q : Real) / s.re := by
  rw [dirichletPartialSumMellin_eq_integral]
  have hDom : IntegrableOn
      (fun u : Real => (q : Real) * u ^ (-(s.re + 1))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  calc
    norm (∫ u : Real in Ioi 1,
        dirichletPartialSum chi u * (u : Complex) ^ (-(s + 1))) <=
        ∫ u : Real in Ioi 1, (q : Real) * u ^ (-(s.re + 1)) := by
      refine norm_integral_le_of_norm_le hDom ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos
        (zero_lt_one.trans hu)]
      exact mul_le_mul_of_nonneg_right
        (norm_sum_dirichletCharacter_Icc_le_level chi hchi ⌊u⌋₊)
        (Real.rpow_nonneg (zero_lt_one.trans hu).le _)
    _ = (q : Real) / s.re := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      field_simp [hRe.ne']
      ring

private lemma dirichletPartialSums_isBigO {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ≠ 1) :
    (fun n : Nat => ∑ k ∈ Finset.Icc 1 n, chi k) =O[atTop]
      (fun n : Nat => (n : Real) ^ (0 : Real)) := by
  refine isBigO_iff.mpr ⟨(q : Real), ?_⟩
  filter_upwards with n
  simpa using norm_sum_dirichletCharacter_Icc_le_level chi hchi n

private lemma LFunction_eq_mul_dirichletPartialSumMellin_of_one_lt_re
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hchi : chi ≠ 1) {s : Complex} (hRe : 1 < s.re) :
    chi.LFunction s = s * dirichletPartialSumMellin chi s := by
  rw [chi.LFunction_eq_LSeries hRe]
  have hRaw := LSeries_eq_mul_integral (fun n : Nat => chi n)
    (r := 0) le_rfl (zero_lt_one.trans hRe)
    (chi.LSeriesSummable_of_one_lt_re hRe)
    (dirichletPartialSums_isBigO chi hchi)
  rw [hRaw, dirichletPartialSumMellin_eq_integral]
  rfl

private lemma LFunction_eq_mul_dirichletPartialSumMellin
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hchi : chi ≠ 1) {s : Complex} (hRe : 0 < s.re) :
    chi.LFunction s = s * dirichletPartialSumMellin chi s := by
  let U : Set Complex := {w | 0 < w.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUPre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLeft : AnalyticOnNhd Complex chi.LFunction U :=
    (chi.differentiable_LFunction hchi).differentiableOn.analyticOnNhd hUOpen
  have hRight : AnalyticOnNhd Complex
      (fun w => w * dirichletPartialSumMellin chi w) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUOpen
    exact (differentiableAt_id.mul
      (differentiableAt_dirichletPartialSumMellin chi hchi hw)).differentiableWithinAt
  have hEq : EqOn chi.LFunction
      (fun w => w * dirichletPartialSumMellin chi w) U := by
    refine hLeft.eqOn_of_preconnected_of_eventuallyEq hRight hUPre
      (show (2 : Complex) ∈ U by simp [U]) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 1 < (2 : Complex).re by norm_num)) ?_
    intro w hw
    exact LFunction_eq_mul_dirichletPartialSumMellin_of_one_lt_re chi hchi hw
  exact hEq hRe

/-- A project-derived explicit consequence of the partial-summation identity
underlying `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 10, Lemma 10.15, p. 350. -/
theorem norm_LFunction_le_level_mul_norm_div_re
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hchi : chi ≠ 1) {s : Complex} (hRe : 0 < s.re) :
    norm (chi.LFunction s) <= (q : Real) * norm s / s.re := by
  rw [LFunction_eq_mul_dirichletPartialSumMellin chi hchi hRe, norm_mul]
  calc
    norm s * norm (dirichletPartialSumMellin chi s) <=
        norm s * ((q : Real) / s.re) := by
      gcongr
      exact norm_dirichletPartialSumMellin_le chi hchi hRe
    _ = (q : Real) * norm s / s.re := by ring

/-- On the closed unit disk centered at `3 / 2 + I * t`, a nonprincipal
Dirichlet L-function grows at most linearly in the level and height. This
project-derived explicit bound supplies the growth input used in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Lemma 11.1, p. 359. -/
theorem norm_LFunction_le_on_shifted_unitDisk
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hchi : chi ≠ 1) (t : Real) {z : Complex} (hZ : norm z <= 1) :
    norm (chi.LFunction
      (z + (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex)))) <=
      2 * (q : Real) * (abs t + 4) := by
  let s : Complex := z + (((3 / 2 : Real) : Complex) + Complex.I * t)
  let tau : Real := abs t + 4
  have hTau : 0 < tau := by
    dsimp [tau]
    positivity
  have hNormCenter :
      norm (((3 / 2 : Real) : Complex) + Complex.I * t) <= 3 / 2 + abs t := by
    calc
      norm (((3 / 2 : Real) : Complex) + Complex.I * t) <=
          norm ((3 / 2 : Real) : Complex) + norm (Complex.I * (t : Complex)) :=
        norm_add_le _ _
      _ = 3 / 2 + abs t := by norm_num [norm_mul, Real.norm_eq_abs]
  have hNormS : norm s <= tau := by
    calc
      norm s <= norm z +
          norm (((3 / 2 : Real) : Complex) + Complex.I * t) := by
        simpa only [s] using norm_add_le z
          (((3 / 2 : Real) : Complex) + Complex.I * t)
      _ <= 1 + (3 / 2 + abs t) := add_le_add hZ hNormCenter
      _ <= tau := by
        dsimp [tau]
        linarith
  have hzRe : -1 <= z.re := by
    have hLower := (abs_le.mp (Complex.abs_re_le_norm z)).1
    linarith
  have hReLower : 1 / 2 <= s.re := by
    dsimp [s]
    norm_num
    linarith
  have hRe : 0 < s.re := by linarith
  have hCore : (q : Real) * norm s / s.re <= 2 * (q : Real) * tau := by
    apply (div_le_iff₀ hRe).2
    have hq : (0 : Real) <= q := Nat.cast_nonneg q
    have hProduct := mul_nonneg hTau.le (sub_nonneg.mpr hReLower)
    nlinarith [mul_le_mul_of_nonneg_left hNormS hq]
  change norm (chi.LFunction s) <= 2 * (q : Real) * tau
  exact (norm_LFunction_le_level_mul_norm_div_re chi hchi hRe).trans hCore

end PrimesRestrictedDigits
