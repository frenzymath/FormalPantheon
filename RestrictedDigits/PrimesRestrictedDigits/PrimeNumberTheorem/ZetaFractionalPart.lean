import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaRegularized

/-!
# A fractional-part bound for the Riemann zeta function

This proves the `x = 1` consequence of `MONTGOMERY-VAUGHAN-MNT-I`,
Chapter 1, Eq. (1.24), in the norm form used in Chapter 6, Eq. (6.5).
-/

open Asymptotics Complex Filter MeasureTheory Set
open scoped ArithmeticFunction Topology

namespace PrimesRestrictedDigits

private noncomputable def complexFract (u : Real) : Complex :=
  ((Int.fract u : Real) : Complex)

private noncomputable def fractionalPartTail (u : Real) : Complex :=
  (Ioi (1 : Real)).indicator complexFract u

private noncomputable def fractionalPartMellin (s : Complex) : Complex :=
  mellin fractionalPartTail (-s)

private lemma measurable_fractionalPartTail : Measurable fractionalPartTail := by
  exact (Complex.continuous_ofReal.measurable.comp measurable_fract).indicator measurableSet_Ioi

private lemma norm_fractionalPartTail_le_one (u : Real) :
    ‖fractionalPartTail u‖ ≤ 1 := by
  by_cases hu : 1 < u
  · simp only [fractionalPartTail, Set.indicator, Set.mem_Ioi, if_pos hu]
    simpa [complexFract, Real.norm_eq_abs, Int.abs_fract] using (Int.fract_lt_one u).le
  · simp [fractionalPartTail, Set.indicator, Set.mem_Ioi, hu]

private lemma locallyIntegrable_fractionalPartTail :
    LocallyIntegrable fractionalPartTail := by
  refine (locallyIntegrable_const (1 : Complex)).mono
    measurable_fractionalPartTail.aestronglyMeasurable ?_
  filter_upwards with u
  simpa using norm_fractionalPartTail_le_one u

private lemma fractionalPartTail_isBigO_atTop :
    fractionalPartTail =O[atTop] (fun _ : Real => (1 : Real)) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards with u
  simpa using norm_fractionalPartTail_le_one u

private lemma fractionalPartTail_isBigO_nhdsGT_zero (b : Real) :
    fractionalPartTail =O[𝓝[>] 0] (fun u : Real => u ^ (-b)) := by
  have hlt : ∀ᶠ u : Real in 𝓝[>] 0, u < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hlt] with u hu
  simp [fractionalPartTail, not_lt.mpr hu.le]

private lemma mellinConvergent_fractionalPartTail {s : Complex} (hRe : 0 < s.re) :
    MellinConvergent fractionalPartTail (-s) := by
  refine mellinConvergent_of_isBigO_rpow
    (a := 0) (b := (-s).re - 1)
    (locallyIntegrable_fractionalPartTail.locallyIntegrableOn (Ioi 0)) ?_ ?_ ?_ ?_
  · simpa using fractionalPartTail_isBigO_atTop
  · simpa using hRe
  · exact fractionalPartTail_isBigO_nhdsGT_zero _
  · linarith

private lemma differentiableAt_fractionalPartMellin {s : Complex} (hRe : 0 < s.re) :
    DifferentiableAt Complex fractionalPartMellin s := by
  have hMellin : DifferentiableAt Complex (mellin fractionalPartTail) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := 0) (b := (-s).re - 1)
      (locallyIntegrable_fractionalPartTail.locallyIntegrableOn (Ioi 0)) ?_ ?_ ?_ ?_
    · simpa using fractionalPartTail_isBigO_atTop
    · simpa using hRe
    · exact fractionalPartTail_isBigO_nhdsGT_zero _
    · linarith
  change DifferentiableAt Complex (fun w => mellin fractionalPartTail (-w)) s
  exact hMellin.comp s differentiableAt_id.neg

private lemma fractionalPartMellin_eq_integral (s : Complex) :
    fractionalPartMellin s =
      ∫ u : Real in Ioi 1,
        complexFract u * (u : Complex) ^ (-(s + 1)) := by
  rw [fractionalPartMellin, mellin]
  simp only [smul_eq_mul]
  calc
    (∫ u : Real in Ioi 0,
        (u : Complex) ^ (-s - 1) * fractionalPartTail u) =
        ∫ u : Real in Ioi 0, (Ioi (1 : Real)).indicator
          (fun v => (v : Complex) ^ (-s - 1) * complexFract v) u := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      by_cases hu : 1 < u <;> simp [fractionalPartTail, hu]
    _ = ∫ u : Real in Ioi (0 : Real) ∩ Ioi 1,
        (u : Complex) ^ (-s - 1) * complexFract u := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ u : Real in Ioi 1,
        (u : Complex) ^ (-s - 1) * complexFract u := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = ∫ u : Real in Ioi 1,
        complexFract u * (u : Complex) ^ (-(s + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma norm_fractionalPartMellin_le {s : Complex} (hRe : 0 < s.re) :
    ‖fractionalPartMellin s‖ ≤ 1 / s.re := by
  rw [fractionalPartMellin_eq_integral]
  have hDom : IntegrableOn (fun u : Real => u ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  calc
    ‖∫ u : Real in Ioi 1,
        complexFract u * (u : Complex) ^ (-(s + 1))‖ ≤
        ∫ u : Real in Ioi 1, u ^ (-(s.re + 1)) := by
      refine norm_integral_le_of_norm_le hDom ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hu)]
      rw [complexFract, norm_real, Real.norm_eq_abs, Int.abs_fract]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (zero_lt_one.trans hu).le _)
        (Int.fract_lt_one u).le
    _ = 1 / s.re := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      field_simp [hRe.ne']
      ring

private lemma partialSums_one (n : Nat) :
    ∑ _k ∈ Finset.Icc 1 n, (1 : Real) = n := by
  simp [Nat.card_Icc]

private lemma partialSums_one_isBigO :
    (fun n : Nat => ∑ _k ∈ Finset.Icc 1 n, (1 : Real)) =O[atTop]
      (fun n : Nat => (n : Real) ^ (1 : Real)) := by
  simpa [partialSums_one] using
    (isBigO_refl (fun n : Nat => (n : Real)) atTop)

private lemma riemannZeta_eq_fractionalPartMellin_of_one_lt_re
    {s : Complex} (hRe : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * fractionalPartMellin s := by
  have hL : riemannZeta s =
      s * ∫ u : Real in Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : Complex)) *
          (u : Complex) ^ (-(s + 1)) := by
    have hRaw := LSeries_eq_mul_integral_of_nonneg
      (fun _ : Nat => (1 : Real)) (r := 1) zero_le_one hRe
      partialSums_one_isBigO (fun _ => zero_le_one)
    have hSeries : LSeries (fun _ : Nat => ((1 : Real) : Complex)) s =
        LSeries (1 : Nat → Complex) s :=
      LSeries_congr (fun _ => by norm_num) s
    calc
      riemannZeta s = LSeries (1 : Nat → Complex) s :=
        (LSeries_one_eq_riemannZeta hRe).symm
      _ = LSeries (fun _ : Nat => ((1 : Real) : Complex)) s := hSeries.symm
      _ = s * ∫ u : Real in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : Complex)) *
            (u : Complex) ^ (-(s + 1)) := by simpa using hRaw
  have hFloor :
      (∫ u : Real in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : Complex)) *
            (u : Complex) ^ (-(s + 1))) =
        ∫ u : Real in Ioi 1,
          ((u : Complex) - complexFract u) *
            (u : Complex) ^ (-(s + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hFloorReal : (⌊u⌋₊ : Real) = u - Int.fract u := by
      rw [natCast_floor_eq_intCast_floor (zero_le_one.trans hu.le)]
      linarith [Int.floor_add_fract u]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel,
      mul_one]
    rw [← Complex.ofReal_natCast, hFloorReal, Complex.ofReal_sub]
    rfl
  rw [hFloor] at hL
  have hPure : IntegrableOn (fun u : Real => (u : Complex) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simpa using hRe) zero_lt_one
  have hFrac : IntegrableOn
      (fun u : Real => complexFract u * (u : Complex) ^ (-(s + 1)))
      (Ioi 1) := by
    have h := mellinConvergent_fractionalPartTail (zero_lt_one.trans hRe)
    rw [MellinConvergent] at h
    have hSub := h.mono_set (Ioi_subset_Ioi zero_le_one)
    refine hSub.congr_fun ?_ measurableSet_Ioi
    intro u hu
    simp only [smul_eq_mul]
    rw [fractionalPartTail, indicator_of_mem hu, mul_comm]
    congr 1
    ring_nf
  have hPoint (u : Real) (hu : u ∈ Ioi (1 : Real)) :
      ((u : Complex) - complexFract u) * (u : Complex) ^ (-(s + 1)) =
        (u : Complex) ^ (-s) -
          complexFract u * (u : Complex) ^ (-(s + 1)) := by
    rw [sub_mul]
    congr 2
    have huZero : (u : Complex) ≠ 0 :=
      ofReal_ne_zero.mpr (zero_lt_one.trans hu).ne'
    calc
      (u : Complex) * (u : Complex) ^ (-(s + 1)) =
          (u : Complex) ^ 1 * (u : Complex) ^ (-(s + 1)) := by rw [cpow_one]
      _ = (u : Complex) ^ (1 + -(s + 1)) := (cpow_add _ _ huZero).symm
      _ = (u : Complex) ^ (-s) := by congr 1; ring
  rw [show (∫ u : Real in Ioi 1,
      ((u : Complex) - complexFract u) *
        (u : Complex) ^ (-(s + 1))) =
      (∫ u : Real in Ioi 1, (u : Complex) ^ (-s)) -
        ∫ u : Real in Ioi 1,
          complexFract u * (u : Complex) ^ (-(s + 1)) by
      rw [← integral_sub hPure hFrac]
      exact setIntegral_congr_fun measurableSet_Ioi hPoint] at hL
  rw [integral_Ioi_cpow_of_lt (by simpa using hRe) zero_lt_one,
    Complex.ofReal_one, one_cpow, ← fractionalPartMellin_eq_integral] at hL
  have hFracRewrite : -1 / (-s + 1) = 1 / (s - 1) := by
    rw [show -s + 1 = -(s - 1) by ring, div_neg]
    ring
  calc
    riemannZeta s = s * (-1 / (-s + 1) - fractionalPartMellin s) := hL
    _ = s / (s - 1) - s * fractionalPartMellin s := by
      rw [hFracRewrite]
      ring

private lemma regularized_zeta_identity {s : Complex} (hRe : 0 < s.re) :
    regularizedRiemannZeta s =
      s - s * (s - 1) * fractionalPartMellin s := by
  let U : Set Complex := {w | 0 < w.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUPre : IsPreconnected U := by
    exact (convex_halfSpace_re_gt 0).isPreconnected
  have hLeft : AnalyticOnNhd Complex regularizedRiemannZeta U :=
    differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd hUOpen
  have hRight : AnalyticOnNhd Complex
      (fun w => w - w * (w - 1) * fractionalPartMellin w) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUOpen
    exact (differentiableAt_id.sub
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
        (differentiableAt_fractionalPartMellin hw))).differentiableWithinAt
  have hEq : EqOn regularizedRiemannZeta
      (fun w => w - w * (w - 1) * fractionalPartMellin w) U := by
    refine hLeft.eqOn_of_preconnected_of_eventuallyEq hRight hUPre
      (show (2 : Complex) ∈ U by simp [U]) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 1 < (2 : Complex).re by norm_num)) ?_
    intro w hw
    have hwOne : w ≠ 1 := by
      intro h
      subst w
      norm_num at hw
    rw [regularizedRiemannZeta_apply_of_ne hwOne,
      riemannZeta_eq_fractionalPartMellin_of_one_lt_re hw]
    field_simp
  exact hEq hRe

private lemma riemannZeta_eq_fractionalPartMellin
    {s : Complex} (hRe : 0 < s.re) (hOne : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * fractionalPartMellin s := by
  have h := regularized_zeta_identity hRe
  rw [regularizedRiemannZeta_apply_of_ne hOne] at h
  have hsOne : s - 1 ≠ 0 := sub_ne_zero.mpr hOne
  apply (mul_left_cancel₀ hsOne)
  calc
    (s - 1) * riemannZeta s = s - s * (s - 1) * fractionalPartMellin s := h
    _ = (s - 1) * (s / (s - 1) - s * fractionalPartMellin s) := by
      field_simp

/-- Montgomery--Vaughan, Chapter 6, Eq. (6.5): the regular part of zeta is
bounded throughout the positive half-plane. -/
theorem norm_riemannZeta_sub_self_div_sub_one_le
    {s : Complex} (hRe : 0 < s.re) (hOne : s ≠ 1) :
    ‖riemannZeta s - s / (s - 1)‖ ≤ ‖s‖ / s.re := by
  rw [riemannZeta_eq_fractionalPartMellin hRe hOne]
  rw [sub_sub_cancel_left, norm_neg, norm_mul]
  calc
    ‖s‖ * ‖fractionalPartMellin s‖ ≤ ‖s‖ * (1 / s.re) := by
      gcongr
      exact norm_fractionalPartMellin_le hRe
    _ = ‖s‖ / s.re := by simp [div_eq_mul_inv]

end PrimesRestrictedDigits
