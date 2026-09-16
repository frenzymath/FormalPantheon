import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayImproperTails

/-!
# Strict delay-kernel comparison for the dimension-one Rosser model

This isolates the positive kernel gap used in Iwaniec's Lemma 17. See
`IWANIEC-ROSSER-SIEVE-1980`, printed pp. 194--195.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem dimensionOneDelayRosserKernel_data
    (scaled Q : Real -> Real) {threshold s : Real}
    (hthreshold : 2 <= threshold) (hs : threshold <= s)
    (hQcont : ContinuousOn Q (Ioi 0))
    (hQpos : forall {u : Real}, 0 < u -> 0 < Q u)
    (htailInt : IntegrableOn (fun t => t * Q (t - 1)) (Ioi s))
    (htailEq : scaled s = ∫ t in Ioi s, t * Q (t - 1)) :
    IntegrableOn (fun t => (t - 1) * Q (t - 1)) (Ioi s) /\
      (∫ t in Ioi s, (t - 1) * Q (t - 1)) < scaled s := by
  have hs2 : 2 <= s := hthreshold.trans hs
  have hshift : ContinuousOn (fun t : Real => Q (t - 1)) (Ioi s) :=
    hQcont.comp (continuous_id.sub continuous_const).continuousOn (by
      intro t ht
      change 0 < t - 1
      change s < t at ht
      linarith)
  have hmodel : IntegrableOn (fun t => (t - 1) * Q (t - 1)) (Ioi s) := by
    apply htailInt.mono'
    · exact ((continuousOn_id.sub continuousOn_const).mul hshift)
        |>.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change s < t at ht
      have ht1 : 0 <= t - 1 := by linarith
      have hq : 0 <= Q (t - 1) := (hQpos (by linarith)).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht1 hq)]
      nlinarith
  have hgap : IntegrableOn (fun t => Q (t - 1)) (Ioi s) := by
    apply htailInt.mono'
    · exact hshift.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change s < t at ht
      have hq : 0 <= Q (t - 1) := (hQpos (by linarith)).le
      rw [Real.norm_eq_abs, abs_of_nonneg hq]
      nlinarith
  have hgapPos : 0 < ∫ t in Ioi s, Q (t - 1) := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun (t : Real) ht =>
        (hQpos (by
          change s < t at ht
          linarith)).le)) hgap).2
    have hsub : Ioo (s + 1) (s + 2) ⊆
        Function.support (fun t : Real => Q (t - 1)) ∩ Ioi s := by
      intro t ht
      have htlo : s + 1 < t := ht.1
      have hu : 0 < t - 1 := by linarith
      constructor
      · exact (hQpos hu).ne'
      · change s < t
        linarith
    have hm : volume (Ioo (s + 1) (s + 2)) <=
        volume (Function.support (fun t : Real => Q (t - 1)) ∩ Ioi s) :=
      measure_mono hsub
    have hvol : 0 < volume (Ioo (s + 1) (s + 2)) := by
      rw [Real.volume_Ioo]
      simp
    exact hvol.trans_le hm
  have hsplit : (∫ t in Ioi s, t * Q (t - 1)) =
      (∫ t in Ioi s, (t - 1) * Q (t - 1)) +
        ∫ t in Ioi s, Q (t - 1) := by
    rw [<- integral_add hmodel hgap]
    apply integral_congr_ae
    filter_upwards with t
    ring
  constructor
  · exact hmodel
  · rw [htailEq, hsplit]
    linarith

/-- Integrability of the finite-model kernel used to compare with the scaled
upper delay function. -/
theorem dimensionOneDelayPlusRosserKernel_integrableOn
    {s : Real} (hs : 3 <= s) :
    IntegrableOn
      (fun t => (t - 1) * dimensionOneDelayQMinus (t - 1)) (Ioi s) :=
  (dimensionOneDelayRosserKernel_data
    dimensionOneDelayScaledPlus dimensionOneDelayQMinus
    (by norm_num) hs dimensionOneDelayQMinus_continuousOn
    dimensionOneDelayQMinus_pos (dimensionOneDelayPlusTail_integrableOn hs)
    (dimensionOneDelayScaledPlus_eq_integral_Ioi hs)).1

/-- Integrability of the finite-model kernel used to compare with the scaled
lower delay function. -/
theorem dimensionOneDelayMinusRosserKernel_integrableOn
    {s : Real} (hs : 2 <= s) :
    IntegrableOn
      (fun t => (t - 1) * dimensionOneDelayQPlus (t - 1)) (Ioi s) :=
  (dimensionOneDelayRosserKernel_data
    dimensionOneDelayScaledMinus dimensionOneDelayQPlus
    (by norm_num) hs dimensionOneDelayQPlus_continuousOn
    dimensionOneDelayQPlus_pos (dimensionOneDelayMinusTail_integrableOn hs)
    (dimensionOneDelayScaledMinus_eq_integral_Ioi hs)).1

/-- The finite-model kernel is strictly smaller than the scaled upper delay
tail because their difference has a positive integral. -/
theorem dimensionOneDelayPlusRosserKernel_integral_lt
    {s : Real} (hs : 3 <= s) :
    (∫ t in Ioi s, (t - 1) * dimensionOneDelayQMinus (t - 1)) <
      dimensionOneDelayScaledPlus s :=
  (dimensionOneDelayRosserKernel_data
    dimensionOneDelayScaledPlus dimensionOneDelayQMinus
    (by norm_num) hs dimensionOneDelayQMinus_continuousOn
    dimensionOneDelayQMinus_pos (dimensionOneDelayPlusTail_integrableOn hs)
    (dimensionOneDelayScaledPlus_eq_integral_Ioi hs)).2

/-- The finite-model kernel is strictly smaller than the scaled lower delay
tail because their difference has a positive integral. -/
theorem dimensionOneDelayMinusRosserKernel_integral_lt
    {s : Real} (hs : 2 <= s) :
    (∫ t in Ioi s, (t - 1) * dimensionOneDelayQPlus (t - 1)) <
      dimensionOneDelayScaledMinus s :=
  (dimensionOneDelayRosserKernel_data
    dimensionOneDelayScaledMinus dimensionOneDelayQPlus
    (by norm_num) hs dimensionOneDelayQPlus_continuousOn
    dimensionOneDelayQPlus_pos (dimensionOneDelayMinusTail_integrableOn hs)
    (dimensionOneDelayScaledMinus_eq_integral_Ioi hs)).2

end PrimesRestrictedDigits
