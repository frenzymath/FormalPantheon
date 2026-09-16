import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayShiftLower
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Improper tails of the dimension-one delay functions

This proves the specialization of Iwaniec's Eq. (7.4) at `kappa=1` and `beta=2`, including its
weak endpoints. See `IWANIEC-ROSSER-SIEVE-1980`, printed p. 194.
-/

open Filter MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem dimensionOneDelayScaled_tendsto_zero
    (scaled Q : Real -> Real)
    (hscale : forall {s : Real}, s ≠ 0 -> s ^ 2 * Q s = scaled s)
    (hpos : forall {s : Real}, 0 < s -> 0 < Q s)
    (hbound : forall {s : Real}, 128 * Real.exp 2 <= s ->
      s ^ 2 * Q s < Real.exp (-s)) :
    Tendsto scaled atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ Real.tendsto_exp_neg_atTop_nhds_zero
  · filter_upwards [eventually_gt_atTop (0 : Real)] with s hs
    rw [<- hscale hs.ne']
    exact mul_nonneg (sq_nonneg s) (hpos hs).le
  · filter_upwards [eventually_ge_atTop (128 * Real.exp 2)] with s hs
    have hs0 : 0 < s := by nlinarith [Real.exp_pos (2 : Real)]
    rw [<- hscale hs0.ne']
    exact (hbound hs).le

/-- The scaled upper delay function tends to zero at positive infinity. -/
theorem dimensionOneDelayScaledPlus_tendsto_zero :
    Tendsto dimensionOneDelayScaledPlus atTop (nhds 0) :=
  dimensionOneDelayScaled_tendsto_zero
    dimensionOneDelayScaledPlus dimensionOneDelayQPlus
    sq_mul_dimensionOneDelayQPlus dimensionOneDelayQPlus_pos
    dimensionOneDelayQPlus_scaled_lt_exp_neg

/-- The scaled lower delay function tends to zero at positive infinity. -/
theorem dimensionOneDelayScaledMinus_tendsto_zero :
    Tendsto dimensionOneDelayScaledMinus atTop (nhds 0) :=
  dimensionOneDelayScaled_tendsto_zero
    dimensionOneDelayScaledMinus dimensionOneDelayQMinus
    sq_mul_dimensionOneDelayQMinus dimensionOneDelayQMinus_pos
    dimensionOneDelayQMinus_scaled_lt_exp_neg

private theorem dimensionOneDelayTail_data
    (scaled Q : Real -> Real) {threshold s : Real}
    (hthreshold : 2 <= threshold) (hs : threshold <= s)
    (hcontinuous : Continuous scaled)
    (hderiv : forall {t : Real}, threshold < t ->
      HasDerivAt scaled (-t * Q (t - 1)) t)
    (hpos : forall {t : Real}, 0 < t -> 0 < Q t)
    (htendsto : Tendsto scaled atTop (nhds 0)) :
    IntegrableOn (fun t => t * Q (t - 1)) (Ioi s) /\
      scaled s = ∫ t in Ioi s, t * Q (t - 1) := by
  have hderivTail : forall t, t ∈ Ioi s ->
      HasDerivAt scaled (-t * Q (t - 1)) t := by
    intro t ht
    change s < t at ht
    exact hderiv (by linarith)
  have hnonpos : forall t, t ∈ Ioi s -> -t * Q (t - 1) <= 0 := by
    intro t ht
    change s < t at ht
    have hm : 0 <= t * Q (t - 1) :=
      mul_nonneg (by linarith) (hpos (by linarith)).le
    nlinarith
  have hneg : IntegrableOn (fun t => -t * Q (t - 1)) (Ioi s) :=
    integrableOn_Ioi_deriv_of_nonpos
      (g := scaled) (g' := fun t => -t * Q (t - 1))
      (a := s) (l := 0)
      hcontinuous.continuousAt.continuousWithinAt hderivTail hnonpos htendsto
  have hpositive : IntegrableOn (fun t => t * Q (t - 1)) (Ioi s) := by
    refine hneg.neg.congr_fun ?_ measurableSet_Ioi
    intro t ht
    change (-fun u : Real => -u * Q (u - 1)) t = t * Q (t - 1)
    simp only [Pi.neg_apply]
    ring
  refine ⟨hpositive, ?_⟩
  have heval : (∫ t in Ioi s, -t * Q (t - 1)) = 0 - scaled s :=
    integral_Ioi_of_hasDerivAt_of_tendsto
      (f := scaled) (f' := fun t => -t * Q (t - 1))
      (a := s) (m := 0)
      hcontinuous.continuousAt.continuousWithinAt hderivTail hneg htendsto
  rw [show (fun t : Real => -t * Q (t - 1)) =
      fun t => -(t * Q (t - 1)) by
        funext t
        ring,
    integral_neg] at heval
  linarith

private theorem dimensionOneDelayPlusTail_data {s : Real} (hs : 3 <= s) :
    IntegrableOn
        (fun t => t * dimensionOneDelayQMinus (t - 1)) (Ioi s) /\
      dimensionOneDelayScaledPlus s =
        ∫ t in Ioi s, t * dimensionOneDelayQMinus (t - 1) :=
  dimensionOneDelayTail_data
    dimensionOneDelayScaledPlus dimensionOneDelayQMinus
    (by norm_num) hs dimensionOneDelayScaledPlus_continuous
    dimensionOneDelayScaledPlus_hasDerivAt dimensionOneDelayQMinus_pos
    dimensionOneDelayScaledPlus_tendsto_zero

private theorem dimensionOneDelayMinusTail_data {s : Real} (hs : 2 <= s) :
    IntegrableOn
        (fun t => t * dimensionOneDelayQPlus (t - 1)) (Ioi s) /\
      dimensionOneDelayScaledMinus s =
        ∫ t in Ioi s, t * dimensionOneDelayQPlus (t - 1) :=
  dimensionOneDelayTail_data
    dimensionOneDelayScaledMinus dimensionOneDelayQPlus
    (by norm_num) hs dimensionOneDelayScaledMinus_continuous
    dimensionOneDelayScaledMinus_hasDerivAt dimensionOneDelayQPlus_pos
    dimensionOneDelayScaledMinus_tendsto_zero

/-- Integrability of the cross-sign kernel in the upper delay tail. -/
theorem dimensionOneDelayPlusTail_integrableOn
    {s : Real} (hs : 3 <= s) :
    IntegrableOn
      (fun t => t * dimensionOneDelayQMinus (t - 1)) (Ioi s) :=
  (dimensionOneDelayPlusTail_data hs).1

/-- Integrability of the cross-sign kernel in the lower delay tail. -/
theorem dimensionOneDelayMinusTail_integrableOn
    {s : Real} (hs : 2 <= s) :
    IntegrableOn
      (fun t => t * dimensionOneDelayQPlus (t - 1)) (Ioi s) :=
  (dimensionOneDelayMinusTail_data hs).1

/-- The upper identity in Iwaniec's Eq. (7.4), including its weak endpoint. -/
theorem dimensionOneDelayScaledPlus_eq_integral_Ioi
    {s : Real} (hs : 3 <= s) :
    dimensionOneDelayScaledPlus s =
      ∫ t in Ioi s, t * dimensionOneDelayQMinus (t - 1) :=
  (dimensionOneDelayPlusTail_data hs).2

/-- The lower identity in Iwaniec's Eq. (7.4), including its weak endpoint. -/
theorem dimensionOneDelayScaledMinus_eq_integral_Ioi
    {s : Real} (hs : 2 <= s) :
    dimensionOneDelayScaledMinus s =
      ∫ t in Ioi s, t * dimensionOneDelayQPlus (t - 1) :=
  (dimensionOneDelayMinusTail_data hs).2

end PrimesRestrictedDigits
