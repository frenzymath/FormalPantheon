import PrimesRestrictedDigits.Fourier.PeriodicCircleIntegral

/-!
# Local smoothing for periodic functions

This is the analytic local-average step in the repaired proof of `MAYNARD-PRD-PUBLISHED`,
Lemma 10.5.
-/

namespace PrimesRestrictedDigits

/-- A variation bound controlled by a nonnegative envelope gives a local
average bound on the unit circle. -/
theorem le_periodicLift_closedBall_average_add_envelope
    {f envelope : Real -> Real}
    (hf : Continuous f) (henvelope : Continuous envelope)
    (hfPeriod : Function.Periodic f 1)
    (henvelopePeriod : Function.Periodic envelope 1)
    (henvelope0 : ∀ x, 0 <= envelope x)
    (hvariation : ∀ {s t : Real}, s <= t ->
      |f t - f s| <= ∫ x in s..t, envelope x)
    {L : Real} (hL : 1 <= L) (y : Real) :
    f y <=
      2 * L *
          (∫ z in Metric.closedBall (y : UnitAddCircle) (1 / (4 * L)),
            hfPeriod.lift z) +
        (∫ z in Metric.closedBall (y : UnitAddCircle) (1 / (4 * L)),
          henvelopePeriod.lift z) := by
  let r : Real := 1 / (4 * L)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hr0 : 0 <= r := by
    dsimp [r]
    positivity
  have hr : r < 1 / 2 := by
    dsimp [r]
    apply (div_lt_div_iff₀ (by positivity : (0 : Real) < 4 * L)
      (by norm_num : (0 : Real) < 2)).mpr
    nlinarith
  have henvelopeIntegrable :
      IntervalIntegrable envelope MeasureTheory.volume (y - r) (y + r) :=
    henvelope.intervalIntegrable (μ := MeasureTheory.volume) (y - r) (y + r)
  let envelopeIntegral := ∫ x in y - r..y + r, envelope x
  have hpoint (s : Real) (hs : s ∈ Set.Icc (y - r) (y + r)) :
      f y <= f s + envelopeIntegral := by
    rw [Set.mem_Icc] at hs
    rcases le_total s y with hsy | hys
    · have hsub :
          (∫ x in s..y, envelope x) <= envelopeIntegral := by
        apply intervalIntegral.integral_mono_interval hs.1 hsy (by linarith)
        · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
            fun x _ => henvelope0 x
        · exact henvelopeIntegrable
      have hvar := hvariation hsy
      have hdifference : f y - f s <= |f y - f s| := le_abs_self _
      dsimp [envelopeIntegral]
      linarith
    · have hsub :
          (∫ x in y..s, envelope x) <= envelopeIntegral := by
        apply intervalIntegral.integral_mono_interval (by linarith) hys hs.2
        · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
            fun x _ => henvelope0 x
        · exact henvelopeIntegrable
      have hvar := hvariation hys
      have hdifference : f y - f s <= |f s - f y| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      dsimp [envelopeIntegral]
      linarith
  have hfIntegrable :
      IntervalIntegrable f MeasureTheory.volume (y - r) (y + r) :=
    hf.intervalIntegrable (μ := MeasureTheory.volume) (y - r) (y + r)
  have hrightIntegrable :
      IntervalIntegrable (fun s => f s + envelopeIntegral)
        MeasureTheory.volume (y - r) (y + r) :=
    hfIntegrable.add intervalIntegrable_const
  have havg :
      2 * r * f y <=
        (∫ s in y - r..y + r, f s) + 2 * r * envelopeIntegral := by
    calc
      2 * r * f y = ∫ _s in y - r..y + r, f y := by
        rw [intervalIntegral.integral_const]
        ring
      _ <= ∫ s in y - r..y + r, f s + envelopeIntegral := by
        apply intervalIntegral.integral_mono_on (by linarith)
          intervalIntegrable_const hrightIntegrable
        exact hpoint
      _ = (∫ s in y - r..y + r, f s) +
          ∫ _s in y - r..y + r, envelopeIntegral := by
        rw [intervalIntegral.integral_add hfIntegrable intervalIntegrable_const]
      _ = (∫ s in y - r..y + r, f s) + 2 * r * envelopeIntegral := by
        rw [intervalIntegral.integral_const]
        ring
  calc
    f y = 2 * L * (2 * r * f y) := by
      dsimp [r]
      field_simp; ring
    _ <= 2 * L * ((∫ s in y - r..y + r, f s) +
        2 * r * envelopeIntegral) :=
      mul_le_mul_of_nonneg_left havg (by positivity)
    _ = 2 * L * (∫ s in y - r..y + r, f s) + envelopeIntegral := by
      dsimp [r]
      field_simp; ring
    _ = 2 * L *
          (∫ z in Metric.closedBall (y : UnitAddCircle) r,
            hfPeriod.lift z) +
        (∫ z in Metric.closedBall (y : UnitAddCircle) r,
          henvelopePeriod.lift z) := by
      rw [intervalIntegral_centered_eq_integral_closedBall_periodicLift
        hf hfPeriod y r hr0 hr]
      dsimp [envelopeIntegral]
      rw [intervalIntegral_centered_eq_integral_closedBall_periodicLift
        henvelope henvelopePeriod y r hr0 hr]
    _ = _ := by ring

end PrimesRestrictedDigits
