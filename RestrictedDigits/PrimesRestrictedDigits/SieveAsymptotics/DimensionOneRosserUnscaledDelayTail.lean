import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayFiniteTails

/-!
# Finite tails for unscaled Rosser delay transport

The unscaled recurrence kernel is strictly smaller than the derivative kernel of the
sign-paired scaled delay function.
-/

open MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private theorem integral_unscaledDelayKernel_le_endpointFactor_mul_sub
    (scaledOpp QOpp scaledTarget : Real -> Real)
    (hscaledOppCont : Continuous scaledOpp)
    (hQOppCont : ContinuousOn QOpp (Ioi 0))
    (hQOppPos : ∀ {t : Real}, 0 < t -> 0 < QOpp t)
    (hscaledOpp : ∀ {t : Real}, t ≠ 0 -> t ^ 2 * QOpp t = scaledOpp t)
    {lower s u : Real} (hlower : 1 < lower) (hs : lower <= s)
    (hsu : s <= u)
    (htail : (∫ t in s..u, t * QOpp (t - 1)) =
      scaledTarget s - scaledTarget u) :
    (∫ t in s..u, scaledOpp (t - 1) / (t - 1)) <=
      (1 - 1 / u) * (scaledTarget s - scaledTarget u) := by
  have hsuIcc : uIcc s u = Icc s u := uIcc_of_le hsu
  have hshiftPos : ∀ t ∈ Icc s u, 0 < t - 1 := by
    intro t ht
    linarith [hlower, hs, ht.1]
  have hscaledCont : ContinuousOn
      (fun t => scaledOpp (t - 1) / (t - 1)) (Icc s u) := by
    apply (hscaledOppCont.comp
      (continuous_id.sub continuous_const)).continuousOn.div
      (continuous_id.sub continuous_const).continuousOn
    intro t ht
    exact (hshiftPos t ht).ne'
  have hQShiftCont : ContinuousOn (fun t => QOpp (t - 1)) (Icc s u) := by
    apply hQOppCont.comp
      (continuousOn_id.sub continuousOn_const)
    intro t ht
    exact hshiftPos t ht
  have htargetCont : ContinuousOn
      (fun t => (1 - 1 / u) * (t * QOpp (t - 1))) (Icc s u) :=
    continuousOn_const.mul (continuousOn_id.mul hQShiftCont)
  have hsourceInt : IntervalIntegrable
      (fun t => scaledOpp (t - 1) / (t - 1)) volume s u :=
    hscaledCont.intervalIntegrable_of_Icc hsu
  have htargetInt : IntervalIntegrable
      (fun t => (1 - 1 / u) * (t * QOpp (t - 1))) volume s u :=
    htargetCont.intervalIntegrable_of_Icc hsu
  have hpoint : ∀ t ∈ Icc s u,
      scaledOpp (t - 1) / (t - 1) <=
        (1 - 1 / u) * (t * QOpp (t - 1)) := by
    intro t ht
    have htShift := hshiftPos t ht
    have htPos : 0 < t := by linarith [hlower, hs, ht.1]
    have hq := hQOppPos htShift
    calc
      scaledOpp (t - 1) / (t - 1) =
          ((t - 1) ^ 2 * QOpp (t - 1)) / (t - 1) := by
        rw [hscaledOpp htShift.ne']
      _ = (1 - 1 / t) * (t * QOpp (t - 1)) := by
        field_simp [htPos.ne']

      _ <= (1 - 1 / u) * (t * QOpp (t - 1)) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg htPos.le hq.le)
        have hinv : 1 / u <= 1 / t :=
          one_div_le_one_div_of_le htPos ht.2
        linarith
  calc
    (∫ t in s..u, scaledOpp (t - 1) / (t - 1)) <=
        ∫ t in s..u, (1 - 1 / u) * (t * QOpp (t - 1)) :=
      intervalIntegral.integral_mono_on hsu hsourceInt htargetInt hpoint
    _ = (1 - 1 / u) * (∫ t in s..u, t * QOpp (t - 1)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (1 - 1 / u) * (scaledTarget s - scaledTarget u) := by rw [htail]

/-- The upper-target unscaled kernel retains the endpoint contraction factor
from the finite delay tail. -/
theorem integral_dimensionOneRosserPlusUnscaledDelay_le_endpointFactor_mul_sub
    {s u : Real} (hs : 3 <= s) (hsu : s <= u) :
    (∫ t in s..u,
      dimensionOneDelayScaledMinus (t - 1) / (t - 1)) <=
      (1 - 1 / u) *
        (dimensionOneDelayScaledPlus s - dimensionOneDelayScaledPlus u) := by
  exact integral_unscaledDelayKernel_le_endpointFactor_mul_sub
    dimensionOneDelayScaledMinus dimensionOneDelayQMinus
    dimensionOneDelayScaledPlus dimensionOneDelayScaledMinus_continuous
    dimensionOneDelayQMinus_continuousOn dimensionOneDelayQMinus_pos
    (fun ht => sq_mul_dimensionOneDelayQMinus ht) (lower := (3 : Real))
    (by norm_num) hs hsu (integral_dimensionOneDelayPlusKernel_eq_sub hs hsu)

/-- The lower-target unscaled kernel retains the endpoint contraction factor
from the finite delay tail. -/
theorem integral_dimensionOneRosserMinusUnscaledDelay_le_endpointFactor_mul_sub
    {s u : Real} (hs : 2 <= s) (hsu : s <= u) :
    (∫ t in s..u,
      dimensionOneDelayScaledPlus (t - 1) / (t - 1)) <=
      (1 - 1 / u) *
        (dimensionOneDelayScaledMinus s - dimensionOneDelayScaledMinus u) := by
  exact integral_unscaledDelayKernel_le_endpointFactor_mul_sub
    dimensionOneDelayScaledPlus dimensionOneDelayQPlus
    dimensionOneDelayScaledMinus dimensionOneDelayScaledPlus_continuous
    dimensionOneDelayQPlus_continuousOn dimensionOneDelayQPlus_pos
    (fun ht => sq_mul_dimensionOneDelayQPlus ht) (lower := (2 : Real))
    (by norm_num) hs hsu (integral_dimensionOneDelayMinusKernel_eq_sub hs hsu)

/-- The upper-target unscaled kernel is bounded by the finite difference of
the scaled upper delay function. -/
theorem integral_dimensionOneRosserPlusUnscaledDelay_le_sub
    {s u : Real} (hs : 3 <= s) (hsu : s <= u) :
    (∫ t in s..u,
      dimensionOneDelayScaledMinus (t - 1) / (t - 1)) <=
      dimensionOneDelayScaledPlus s - dimensionOneDelayScaledPlus u := by
  have hstrong :=
    integral_dimensionOneRosserPlusUnscaledDelay_le_endpointFactor_mul_sub
      hs hsu
  have hdiff : 0 <= dimensionOneDelayScaledPlus s -
      dimensionOneDelayScaledPlus u := sub_nonneg.mpr
    (dimensionOneDelayScaledPlus_antitoneOn
      (show (1 : Real) <= s by linarith)
      (show (1 : Real) <= u by linarith) hsu)
  have huPos : 0 < u := by linarith
  exact hstrong.trans (mul_le_of_le_one_left hdiff (by
    exact sub_le_self _ (one_div_nonneg.mpr huPos.le)))

/-- The lower-target unscaled kernel is bounded by the finite difference of
the scaled lower delay function. -/
theorem integral_dimensionOneRosserMinusUnscaledDelay_le_sub
    {s u : Real} (hs : 2 <= s) (hsu : s <= u) :
    (∫ t in s..u,
      dimensionOneDelayScaledPlus (t - 1) / (t - 1)) <=
      dimensionOneDelayScaledMinus s - dimensionOneDelayScaledMinus u := by
  have hstrong :=
    integral_dimensionOneRosserMinusUnscaledDelay_le_endpointFactor_mul_sub
      hs hsu
  have hdiff : 0 <= dimensionOneDelayScaledMinus s -
      dimensionOneDelayScaledMinus u := sub_nonneg.mpr
    (dimensionOneDelayScaledMinus_antitoneOn
      (show (2 : Real) <= s by exact hs)
      (show (2 : Real) <= u by exact hs.trans hsu) hsu)
  have huPos : 0 < u := by linarith
  exact hstrong.trans (mul_le_of_le_one_left hdiff (by
    exact sub_le_self _ (one_div_nonneg.mpr huPos.le)))

end PrimesRestrictedDigits
