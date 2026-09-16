import PrimesRestrictedDigits.BasicEstimates.BuchstabPrimeWeight
import PrimesRestrictedDigits.BasicEstimates.LogarithmicIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Remainder estimates for the Buchstab prime weight

This file makes the exponent-two remainder estimates following Eq. (7.45) of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 7, p. 218, explicit. The PNT estimate
itself remains a separate input.
-/

open MeasureTheory Set
open scoped Interval Topology

namespace PrimesRestrictedDigits

private noncomputable def remainderKernel (t : Real) : Real :=
  (Real.log t + 3) / (t * Real.log t ^ 4)

private noncomputable def remainderAntiderivative (t : Real) : Real :=
  (1 / 2 : Real) * (Real.log t ^ 2)⁻¹ + (Real.log t ^ 3)⁻¹

private lemma continuousOn_remainderKernel {a b : Real} (ha : 2 ≤ a) :
    ContinuousOn remainderKernel (Set.Icc a b) := by
  have hlog : ContinuousOn Real.log (Set.Icc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (by linarith [ha, ht.1])
  have hlogpos : ∀ t ∈ Set.Icc a b, 0 < Real.log t := by
    intro t ht
    exact Real.log_pos (by linarith [ha, ht.1])
  have hden : ∀ t ∈ Set.Icc a b, t * Real.log t ^ 4 ≠ 0 := by
    intro t ht
    have htpos : 0 < t := by linarith [ha, ht.1]
    exact mul_ne_zero (ne_of_gt htpos)
      (pow_ne_zero _ (ne_of_gt (hlogpos t ht)))
  unfold remainderKernel
  exact (hlog.add continuousOn_const).div
    (continuousOn_id.mul (hlog.pow 4)) hden

private lemma continuousOn_remainderAntiderivative {a b : Real}
    (ha : 2 ≤ a) :
    ContinuousOn remainderAntiderivative (Set.Icc a b) := by
  have hlog : ContinuousOn Real.log (Set.Icc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (by linarith [ha, ht.1])
  have hlogpos : ∀ t ∈ Set.Icc a b, 0 < Real.log t := by
    intro t ht
    exact Real.log_pos (by linarith [ha, ht.1])
  have h2 : ∀ t ∈ Set.Icc a b, Real.log t ^ 2 ≠ 0 := by
    intro t ht
    exact pow_ne_zero _ (ne_of_gt (hlogpos t ht))
  have h3 : ∀ t ∈ Set.Icc a b, Real.log t ^ 3 ≠ 0 := by
    intro t ht
    exact pow_ne_zero _ (ne_of_gt (hlogpos t ht))
  unfold remainderAntiderivative
  exact (continuousOn_const.mul ((hlog.pow 2).inv₀ h2)).add
    ((hlog.pow 3).inv₀ h3)

private lemma hasDerivAt_remainderAntiderivative {t : Real} (ht : 1 < t) :
    HasDerivAt remainderAntiderivative
      (-(Real.log t + 3) / (t * Real.log t ^ 4)) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hlog0 : Real.log t ≠ 0 := ne_of_gt hlogpos
  have h2 : Real.log t ^ 2 ≠ 0 := pow_ne_zero _ hlog0
  have h3 : Real.log t ^ 3 ≠ 0 := pow_ne_zero _ hlog0
  have hi2 := ((Real.hasDerivAt_log ht0).pow 2).inv h2
  have hi3 := ((Real.hasDerivAt_log ht0).pow 3).inv h3
  have hs := (hi2.const_mul (1 / 2 : Real)).add hi3
  have hfun : remainderAntiderivative =ᶠ[𝓝 t]
      (fun y => (1 / 2 : Real) * (Real.log ^ 2)⁻¹ y) +
        (Real.log ^ 3)⁻¹ := by
    filter_upwards [] with s
    rfl
  apply (hs.congr_of_eventuallyEq hfun).congr_deriv
  norm_num [Function.comp_apply]
  field_simp [hlog0, ht0]
  ring_nf

private lemma integral_remainderKernel {a b : Real} (ha : 2 ≤ a)
    (hab : a ≤ b) :
    (∫ t in a..b, remainderKernel t) =
      ((1 / 2 : Real) * (Real.log a ^ 2)⁻¹ + (Real.log a ^ 3)⁻¹) -
        ((1 / 2 : Real) * (Real.log b ^ 2)⁻¹ +
          (Real.log b ^ 3)⁻¹) := by
  have hkernel : IntervalIntegrable remainderKernel volume a b :=
    (continuousOn_remainderKernel ha).intervalIntegrable_of_Icc hab
  have hanti : IntervalIntegrable
      (fun t => -(remainderKernel t)) volume a b := hkernel.neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := remainderAntiderivative) (f' := fun t => -(remainderKernel t))
    hab (continuousOn_remainderAntiderivative ha)
    (fun t ht => by
      have h := hasDerivAt_remainderAntiderivative (t := t)
        (by linarith [ha, ht.1])
      apply h.congr_deriv
      dsimp [remainderKernel]
      ring) hanti
  calc
    (∫ t in a..b, remainderKernel t) =
        -∫ t in a..b, -(remainderKernel t) := by
          rw [intervalIntegral.integral_neg]
          ring
    _ = -(remainderAntiderivative b - remainderAntiderivative a) := by
      rw [hftc]
    _ = _ := by
      dsimp [remainderAntiderivative]
      ring_nf

/-- Exact integral control for an exponent-two PNT remainder and the
transformed-weight derivative majorant. -/
theorem abs_integral_mul_deriv_of_log_bounds
    {x C a b : Real} {R f : Real → Real}
    (ha : 2 ≤ a) (hab : a ≤ b)
    (hR : ∀ t ∈ Set.Ioo a b,
      |R t| ≤ C * t / Real.log t ^ 2)
    (hD : ∀ t ∈ Set.Ioo a b,
      |deriv f t| ≤
        x * (Real.log t + 3) / (t ^ 2 * Real.log t ^ 2))
    (hRm : AEMeasurable R (volume.restrict (Set.Ioo a b))) :
    |∫ t in a..b, R t * deriv f t| ≤
      C * x *
        (((1 / 2 : Real) * (Real.log a ^ 2)⁻¹ +
            (Real.log a ^ 3)⁻¹) -
          ((1 / 2 : Real) * (Real.log b ^ 2)⁻¹ +
            (Real.log b ^ 3)⁻¹)) := by
  by_cases hEq : a = b
  · subst b
    simp
  let g : Real → Real := fun t => C * x * remainderKernel t
  have hg_cont : ContinuousOn g (Set.Icc a b) :=
    (continuousOn_const.mul continuousOn_const).mul
      (continuousOn_remainderKernel ha)
  have hg_int : IntervalIntegrable g volume a b :=
    hg_cont.intervalIntegrable_of_Icc hab
  have hprod_meas :
      AEStronglyMeasurable (fun t => R t * deriv f t)
        (volume.restrict (Set.Ioo a b)) :=
    hRm.aestronglyMeasurable.mul
      (aemeasurable_deriv f
        (volume.restrict (Set.Ioo a b))).aestronglyMeasurable
  have hprod_point : ∀ t ∈ Set.Ioo a b,
      |R t * deriv f t| ≤ g t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ha, ht.1]
    have htpos : 0 < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos ht1
    rw [abs_mul]
    calc
      |R t| * |deriv f t| ≤
          (C * t / Real.log t ^ 2) *
            (x * (Real.log t + 3) / (t ^ 2 * Real.log t ^ 2)) := by
              exact mul_le_mul (hR t ht) (hD t ht) (abs_nonneg _)
                ((abs_nonneg _).trans (hR t ht))
      _ = g t := by
        dsimp [g, remainderKernel]
        field_simp [ne_of_gt htpos, ne_of_gt hlogpos]
  have hprod_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
      |R t * deriv f t| ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hprod_point t ht
  have hprod_int : IntervalIntegrable
      (fun t => R t * deriv f t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2
    have hg_on : IntegrableOn g (Set.Ioo a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hg_int
    exact hg_on.mono' hprod_meas hprod_bound
  have habs_int : IntervalIntegrable
      (fun t => |R t * deriv f t|) volume a b := hprod_int.abs
  have hmono :
      (∫ t in a..b, |R t * deriv f t|) ≤ ∫ t in a..b, g t := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab habs_int hg_int
    intro t ht
    exact hprod_point t ht
  have hbound :
      |∫ t in a..b, R t * deriv f t| ≤ ∫ t in a..b, g t :=
    (intervalIntegral.abs_integral_le_integral_abs hab).trans hmono
  rw [show (∫ t in a..b, g t) =
      C * x * (∫ t in a..b, remainderKernel t) by
        simp [g, intervalIntegral.integral_const_mul] ] at hbound
  rw [integral_remainderKernel ha hab] at hbound
  exact hbound

/-- A weak exponent-two PNT remainder bound controls a strict boundary term,
including the possible jump at a prime integer endpoint. -/
theorem abs_buchstabPrimeWeight_mul_strictPrimeRemainder_le
    {x C t : Real} (hx : 0 ≤ x) (ht : 2 ≤ t)
    (hv : 1 ≤ buchstabArgument x t)
    (hR : |primeRemainder t| ≤ C * t / Real.log t ^ 2) :
    |buchstabPrimeWeight x t * strictPrimeRemainder t| ≤
      C * x / Real.log t ^ 3 + x / (t * Real.log t) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hstrict : |strictPrimeRemainder t| ≤ |primeRemainder t| + 1 := by
    calc
      |strictPrimeRemainder t| =
          |(strictPrimeRemainder t - primeRemainder t) +
            primeRemainder t| := by
        congr 1
        ring
      _ ≤ |strictPrimeRemainder t - primeRemainder t| +
          |primeRemainder t| := abs_add_le _ _
      _ ≤ 1 + |primeRemainder t| := by
        linarith [abs_strictPrimeRemainder_sub_primeRemainder_le_one t]
      _ = |primeRemainder t| + 1 := by ring
  rw [abs_mul]
  calc
    |buchstabPrimeWeight x t| * |strictPrimeRemainder t| ≤
        (x / (t * Real.log t)) *
          (C * t / Real.log t ^ 2 + 1) := by
      apply mul_le_mul (abs_buchstabPrimeWeight_le hx ht hv)
        (hstrict.trans (by linarith [hR])) (abs_nonneg _)
      positivity
    _ = C * x / Real.log t ^ 3 + x / (t * Real.log t) := by
      field_simp

end PrimesRestrictedDigits
