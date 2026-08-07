import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# An Abel representation for regularized zeta

Euler--Maclaurin summation represents zeta on the positive half-plane by a
pole term and an absolutely convergent fractional-part integral. Multiplying
away the pole gives an analytic identity for Mathlib's entire
`riemannZeta₁`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 14--15,
Theorem 1.10, and printed p. 55, equation (5.7). Semantic review: `SEM-482`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Asymptotics Complex Filter MeasureTheory Set
open scoped Topology

private noncomputable def zetaFractionalTail (u : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) u

private noncomputable def zetaFractionalMellin (s : ℂ) : ℂ :=
  mellin zetaFractionalTail (-s)

private lemma measurable_zetaFractionalTail :
    Measurable zetaFractionalTail := by
  exact (Complex.continuous_ofReal.measurable.comp measurable_fract).indicator
    measurableSet_Ioi

private lemma norm_zetaFractionalTail_le_one (u : ℝ) :
    ‖zetaFractionalTail u‖ ≤ 1 := by
  by_cases hu : 1 < u
  · simpa [zetaFractionalTail, hu, Complex.norm_real, Real.norm_eq_abs,
      Int.abs_fract] using
      (Int.fract_lt_one u).le
  · simp [zetaFractionalTail, hu]

private lemma locallyIntegrable_zetaFractionalTail :
    LocallyIntegrable zetaFractionalTail := by
  refine (locallyIntegrable_const (1 : ℂ)).mono
    measurable_zetaFractionalTail.aestronglyMeasurable ?_
  filter_upwards with u
  simpa using norm_zetaFractionalTail_le_one u

private lemma zetaFractionalTail_isBigO_atTop :
    zetaFractionalTail =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨1, Eventually.of_forall fun u => ?_⟩
  simpa using norm_zetaFractionalTail_le_one u

private lemma zetaFractionalTail_isBigO_nhdsGT_zero (b : ℝ) :
    zetaFractionalTail =O[𝓝[>] 0] (fun u : ℝ => u ^ (-b)) := by
  have hsmall : ∀ᶠ u : ℝ in 𝓝[>] 0, u < 1 :=
    Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hsmall] with u hu
  simp [zetaFractionalTail, not_lt.mpr hu.le]

private lemma mellinConvergent_zetaFractionalTail
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent zetaFractionalTail (-s) := by
  refine mellinConvergent_of_isBigO_rpow
    (a := 0) (b := (-s).re - 1)
    (locallyIntegrable_zetaFractionalTail.locallyIntegrableOn (Ioi 0))
    (by simpa using zetaFractionalTail_isBigO_atTop) ?_
    (zetaFractionalTail_isBigO_nhdsGT_zero ((-s).re - 1)) ?_
  · simpa using hs
  · linarith

private lemma differentiableAt_zetaFractionalMellin
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaFractionalMellin s := by
  have hMellin : DifferentiableAt ℂ (mellin zetaFractionalTail) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := 0) (b := (-s).re - 1)
      (locallyIntegrable_zetaFractionalTail.locallyIntegrableOn (Ioi 0))
      (by simpa using zetaFractionalTail_isBigO_atTop) ?_
      (zetaFractionalTail_isBigO_nhdsGT_zero ((-s).re - 1)) ?_
    · simpa using hs
    · linarith
  exact hMellin.comp s differentiableAt_id.neg

private lemma zetaFractionalMellin_eq_integral (s : ℂ) :
    zetaFractionalMellin s =
      ∫ u in Ioi (1 : ℝ),
        (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))) := by
  rw [zetaFractionalMellin, mellin]
  simp only [smul_eq_mul]
  calc
    (∫ u : ℝ in Ioi 0,
        (u : ℂ) ^ (-s - 1) * zetaFractionalTail u) =
        ∫ u : ℝ in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun x : ℝ =>
            (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ)) u := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      by_cases hu : 1 < u <;> simp [zetaFractionalTail, hu]
    _ = ∫ u : ℝ in Ioi (0 : ℝ) ∩ Ioi 1,
        (u : ℂ) ^ (-s - 1) * ((Int.fract u : ℝ) : ℂ) := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ u : ℝ in Ioi 1,
        (u : ℂ) ^ (-s - 1) * ((Int.fract u : ℝ) : ℂ) := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = ∫ u : ℝ in Ioi 1,
        ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma norm_zetaFractionalMellin_le
    {s : ℂ} (hs : 0 < s.re) :
    ‖zetaFractionalMellin s‖ ≤ 1 / s.re := by
  rw [zetaFractionalMellin_eq_integral]
  have hmajorant : IntegrableOn
      (fun u : ℝ => u ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hconvergent := mellinConvergent_zetaFractionalTail hs
  rw [MellinConvergent] at hconvergent
  have hrestricted :=
    hconvergent.mono_set (Ioi_subset_Ioi zero_le_one)
  have hintegrable : IntegrableOn
      (fun u : ℝ =>
        ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
    refine hrestricted.congr_fun ?_ measurableSet_Ioi
    intro u hu
    simp only [smul_eq_mul]
    rw [zetaFractionalTail, indicator_of_mem hu, mul_comm]
    congr 1
    ring_nf
  have hbound : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioi 1),
      ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))‖ ≤
        u ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hu)]
    simp only [neg_re, add_re, one_re, Complex.norm_real, Real.norm_eq_abs,
      Int.abs_fract]
    exact mul_le_of_le_one_left
      (Real.rpow_nonneg (zero_lt_one.trans hu).le _)
      (Int.fract_lt_one u).le
  calc
    ‖∫ u : ℝ in Ioi 1,
        ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))‖ ≤
        ∫ u : ℝ in Ioi 1,
          ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Ioi 1, u ^ (-(s.re + 1)) :=
      setIntegral_mono_ae_restrict hintegrable.norm hmajorant hbound
    _ = 1 / s.re := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      field_simp [hs.ne']
      ring

private lemma unit_partialSums_isBigO :
    (fun n : ℕ => ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  simpa [Nat.card_Icc] using
    (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)

private lemma riemannZeta_eq_pole_sub_mellin
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * zetaFractionalMellin s := by
  have hseries :
      riemannZeta s =
        s * ∫ u : ℝ in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℂ)) *
            (u : ℂ) ^ (-(s + 1)) := by
    have h := LSeries_eq_mul_integral_of_nonneg
      (fun _ : ℕ => (1 : ℝ)) (r := 1) zero_le_one hs
      unit_partialSums_isBigO (fun _ => zero_le_one)
    calc
      riemannZeta s = LSeries (1 : ℕ → ℂ) s :=
        (LSeries_one_eq_riemannZeta hs).symm
      _ = LSeries (fun _ : ℕ => ((1 : ℝ) : ℂ)) s := by
        apply LSeries_congr
        simp
      _ = s * ∫ u : ℝ in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℂ)) *
            (u : ℂ) ^ (-(s + 1)) := by simpa using h
  have hfloor :
      (∫ u : ℝ in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℂ)) *
            (u : ℂ) ^ (-(s + 1))) =
        ∫ u : ℝ in Ioi 1,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) *
            (u : ℂ) ^ (-(s + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 ≤ u := (zero_lt_one.trans hu).le
    have hfloorReal : (⌊u⌋₊ : ℝ) = u - Int.fract u := by
      rw [natCast_floor_eq_intCast_floor hu0]
      linarith [Int.floor_add_fract u]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
      Nat.add_sub_cancel, mul_one]
    rw [← Complex.ofReal_natCast, hfloorReal, Complex.ofReal_sub]
  rw [hfloor] at hseries
  have hpure : IntegrableOn
      (fun u : ℝ => (u : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one
  have hfrac : IntegrableOn
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) *
        (u : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    have hconv := mellinConvergent_zetaFractionalTail (zero_lt_one.trans hs)
    rw [MellinConvergent] at hconv
    have hrestrict := hconv.mono_set (Ioi_subset_Ioi zero_le_one)
    refine hrestrict.congr_fun ?_ measurableSet_Ioi
    intro u hu
    simp only [smul_eq_mul]
    rw [zetaFractionalTail, indicator_of_mem hu, mul_comm]
    congr 1
    ring_nf
  have hpoint : ∀ u ∈ Ioi (1 : ℝ),
      ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) *
          (u : ℂ) ^ (-(s + 1)) =
        (u : ℂ) ^ (-s) -
          ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1)) := by
    intro u hu
    rw [sub_mul]
    congr 2
    have hu0 : (u : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hu).ne'
    calc
      (u : ℂ) * (u : ℂ) ^ (-(s + 1)) =
          (u : ℂ) ^ 1 * (u : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
      _ = (u : ℂ) ^ (1 + -(s + 1)) := (cpow_add _ _ hu0).symm
      _ = (u : ℂ) ^ (-s) := by congr 1; ring
  have hintegral :
      (∫ u : ℝ in Ioi 1,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) *
            (u : ℂ) ^ (-(s + 1))) =
        (∫ u : ℝ in Ioi 1, (u : ℂ) ^ (-s)) -
          ∫ u : ℝ in Ioi 1,
            ((Int.fract u : ℝ) : ℂ) *
              (u : ℂ) ^ (-(s + 1)) := by
    rw [← integral_sub hpure hfrac]
    exact setIntegral_congr_fun measurableSet_Ioi hpoint
  rw [hintegral,
    integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one,
    Complex.ofReal_one, one_cpow, ← zetaFractionalMellin_eq_integral] at hseries
  have hpole : -1 / (-s + 1) = 1 / (s - 1) := by
    rw [show -s + 1 = -(s - 1) by ring, div_neg]
    ring
  calc
    riemannZeta s = s * (-1 / (-s + 1) - zetaFractionalMellin s) := hseries
    _ = s / (s - 1) - s * zetaFractionalMellin s := by
      rw [hpole]
      ring

/-- The regularized zeta function represented by the fractional-part Abel
integral throughout the positive half-plane. -/
theorem riemannZeta₁_eq_abelIntegral
    (s : ℂ) (hs : 0 < s.re) :
    riemannZeta₁ s =
      s - s * (s - 1) *
        ∫ u in Set.Ioi (1 : ℝ),
          (((Int.fract u : ℝ) : ℂ) *
            (u : ℂ) ^ (-(s + 1))) := by
  let U : Set ℂ := {z | 0 < z.re}
  let rhs : ℂ → ℂ := fun z =>
    z - z * (z - 1) * zetaFractionalMellin z
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hleft : AnalyticOnNhd ℂ riemannZeta₁ U :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hUopen
  have hright : AnalyticOnNhd ℂ rhs U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact (differentiableAt_id.sub
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
        (differentiableAt_zetaFractionalMellin hz))).differentiableWithinAt
  have heq : Set.EqOn riemannZeta₁ rhs U := by
    refine hleft.eqOn_of_preconnected_of_eventuallyEq hright
      (convex_halfSpace_re_gt 0).isPreconnected
      (show (2 : ℂ) ∈ U by simp [U]) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)) ?_
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hz
    have hfactor : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1]
      field_simp
    rw [hfactor, riemannZeta_eq_pole_sub_mellin hz]
    dsimp [rhs]
    field_simp
  rw [heq hs]
  dsimp [rhs]
  rw [zetaFractionalMellin_eq_integral]

/-- The direct norm consequence of the regularized Abel representation. -/
theorem norm_riemannZeta₁_le_abel
    (s : ℂ) (hs : 0 < s.re) :
    ‖riemannZeta₁ s‖ ≤
      ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [riemannZeta₁_eq_abelIntegral s hs,
    ← zetaFractionalMellin_eq_integral]
  calc
    ‖s - s * (s - 1) * zetaFractionalMellin s‖ ≤
        ‖s‖ + ‖s * (s - 1) * zetaFractionalMellin s‖ := norm_sub_le _ _
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ * ‖zetaFractionalMellin s‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * (1 / s.re) := by
      gcongr
      exact norm_zetaFractionalMellin_le hs
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by ring

end BoundedGaps.Maynard
