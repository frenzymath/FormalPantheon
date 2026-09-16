import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelLimits

/-!
# Improper-tail recurrences for the raw dimension-one Rosser model

This proves Iwaniec's Eq. (7.7) at `kappa=1`, `beta=2` by dominated convergence, including
both weak endpoints. See `IWANIEC-ROSSER-SIEVE-1980`, printed p. 195.
-/

open Filter MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem dimensionOneRosserModelMinusRaw_dctData
    {s : Real} (hs : 2 <= s) :
    IntegrableOn
        (fun t => dimensionOneRosserModelPlusRaw (t - 1) / (t - 1))
        (Ioi s) /\
      Tendsto
        (fun R => ∫ t in Ioi s,
          dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1))
        atTop
        (nhds (∫ t in Ioi s,
          dimensionOneRosserModelPlusRaw (t - 1) / (t - 1))) := by
  rcases exists_dimensionOneRosserModelPartialSums_lt_delay with
    ⟨c, hc, hplus, hminus⟩
  let bound := fun t : Real =>
    c * ((t - 1) * dimensionOneDelayQPlus (t - 1))
  have hfiniteMeas : forall R, AEStronglyMeasurable
      (fun t => dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1))
      (volume.restrict (Ioi s)) := by
    intro R
    have hi : IntegrableOn
        (fun t => dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1))
        (Ioi s) :=
      (integrable_shiftedRosserKernel_plusPartialSum R).integrableOn.congr_fun
        (fun t ht => rfl) measurableSet_Ioi
    exact hi.aestronglyMeasurable
  have hboundInt : Integrable bound (volume.restrict (Ioi s)) := by
    dsimp [bound]
    exact (dimensionOneDelayMinusRosserKernel_integrableOn hs).const_mul c
  have hbound : forall R, ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1)‖ <=
        bound t := by
    intro R
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change s < t at ht
    have ht1 : 0 < t - 1 := by linarith
    have hpartial :
        0 <= dimensionOneRosserModelPlusPartialSum R (t - 1) :=
      dimensionOneRosserModelPlusPartialSum_nonneg R (t - 1)
    have hm := (hplus R (show 1 < t - 1 by linarith)).le
    rw [<- sq_mul_dimensionOneDelayQPlus ht1.ne'] at hm
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hpartial ht1.le)]
    dsimp [bound]
    calc
      dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1) <=
          (c * ((t - 1) ^ 2 * dimensionOneDelayQPlus (t - 1))) /
            (t - 1) :=
        (div_le_div_iff_of_pos_right ht1).2 hm
      _ = c * ((t - 1) * dimensionOneDelayQPlus (t - 1)) := by
        field_simp
  have hlim : ∀ᵐ t ∂volume.restrict (Ioi s),
      Tendsto
        (fun R => dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1))
        atTop
        (nhds (dimensionOneRosserModelPlusRaw (t - 1) / (t - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change s < t at ht
    exact (dimensionOneRosserModelPlusPartialSum_tendsto_raw
      (show 1 < t - 1 by linarith)).div_const (t - 1)
  have hrawMeas : AEStronglyMeasurable
      (fun t => dimensionOneRosserModelPlusRaw (t - 1) / (t - 1))
      (volume.restrict (Ioi s)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hfiniteMeas hlim
  have hrawFinite : HasFiniteIntegral
      (fun t => dimensionOneRosserModelPlusRaw (t - 1) / (t - 1))
      (volume.restrict (Ioi s)) :=
    hasFiniteIntegral_of_dominated_convergence
      hboundInt.hasFiniteIntegral hbound hlim
  exact ⟨⟨hrawMeas, hrawFinite⟩,
    tendsto_integral_of_dominated_convergence
      bound hfiniteMeas hboundInt hbound hlim⟩

private theorem dimensionOneRosserModelPlusRaw_dctData
    {s : Real} (hs : 3 <= s) :
    IntegrableOn
        (fun t => dimensionOneRosserModelMinusRaw (t - 1) / (t - 1))
        (Ioi s) /\
      Tendsto
        (fun R => ∫ t in Ioi s,
          dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1))
        atTop
        (nhds (∫ t in Ioi s,
          dimensionOneRosserModelMinusRaw (t - 1) / (t - 1))) := by
  rcases exists_dimensionOneRosserModelPartialSums_lt_delay with
    ⟨c, hc, hplus, hminus⟩
  let bound := fun t : Real =>
    c * ((t - 1) * dimensionOneDelayQMinus (t - 1))
  have hfiniteMeas : forall R, AEStronglyMeasurable
      (fun t => dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1))
      (volume.restrict (Ioi s)) := by
    intro R
    have hi : IntegrableOn
        (fun t => dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1))
        (Ioi s) :=
      (integrable_shiftedRosserKernel_minusPartialSum R).integrableOn.congr_fun
        (fun t ht => rfl) measurableSet_Ioi
    exact hi.aestronglyMeasurable
  have hboundInt : Integrable bound (volume.restrict (Ioi s)) := by
    dsimp [bound]
    exact (dimensionOneDelayPlusRosserKernel_integrableOn hs).const_mul c
  have hbound : forall R, ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1)‖ <=
        bound t := by
    intro R
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change s < t at ht
    have ht1 : 0 < t - 1 := by linarith
    have hpartial :
        0 <= dimensionOneRosserModelMinusPartialSum R (t - 1) :=
      dimensionOneRosserModelMinusPartialSum_nonneg R (t - 1)
    have hm := (hminus R (show 2 <= t - 1 by linarith)).le
    rw [<- sq_mul_dimensionOneDelayQMinus ht1.ne'] at hm
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hpartial ht1.le)]
    dsimp [bound]
    calc
      dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1) <=
          (c * ((t - 1) ^ 2 * dimensionOneDelayQMinus (t - 1))) /
            (t - 1) :=
        (div_le_div_iff_of_pos_right ht1).2 hm
      _ = c * ((t - 1) * dimensionOneDelayQMinus (t - 1)) := by
        field_simp
  have hlim : ∀ᵐ t ∂volume.restrict (Ioi s),
      Tendsto
        (fun R => dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1))
        atTop
        (nhds (dimensionOneRosserModelMinusRaw (t - 1) / (t - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change s < t at ht
    exact (dimensionOneRosserModelMinusPartialSum_tendsto_raw
      (show 2 <= t - 1 by linarith)).div_const (t - 1)
  have hrawMeas : AEStronglyMeasurable
      (fun t => dimensionOneRosserModelMinusRaw (t - 1) / (t - 1))
      (volume.restrict (Ioi s)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hfiniteMeas hlim
  have hrawFinite : HasFiniteIntegral
      (fun t => dimensionOneRosserModelMinusRaw (t - 1) / (t - 1))
      (volume.restrict (Ioi s)) :=
    hasFiniteIntegral_of_dominated_convergence
      hboundInt.hasFiniteIntegral hbound hlim
  exact ⟨⟨hrawMeas, hrawFinite⟩,
    tendsto_integral_of_dominated_convergence
      bound hfiniteMeas hboundInt hbound hlim⟩

/-- Integrability of the shifted raw upper kernel in the lower recurrence. -/
theorem integrableOn_shifted_dimensionOneRosserModelPlusRaw
    {s : Real} (hs : 2 <= s) :
    IntegrableOn
      (fun t => dimensionOneRosserModelPlusRaw (t - 1) / (t - 1))
      (Ioi s) :=
  (dimensionOneRosserModelMinusRaw_dctData hs).1

/-- Integrability of the shifted raw lower kernel in the upper recurrence. -/
theorem integrableOn_shifted_dimensionOneRosserModelMinusRaw
    {s : Real} (hs : 3 <= s) :
    IntegrableOn
      (fun t => dimensionOneRosserModelMinusRaw (t - 1) / (t - 1))
      (Ioi s) :=
  (dimensionOneRosserModelPlusRaw_dctData hs).1

/-- The lower identity in Iwaniec's Eq. (7.7), including the endpoint two. -/
theorem dimensionOneRosserModelMinusRaw_eq_integral_Ioi
    {s : Real} (hs : 2 <= s) :
    dimensionOneRosserModelMinusRaw s =
      ∫ t in Ioi s, dimensionOneRosserModelPlusRaw (t - 1) / (t - 1) := by
  have hdct := (dimensionOneRosserModelMinusRaw_dctData hs).2
  have hrec :
      (fun R => ∫ t in Ioi s,
        dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1)) =
      fun R => dimensionOneRosserModelMinusPartialSum (R + 1) s := by
    funext R
    exact (dimensionOneRosserModelMinusPartialSum_succ_integral R hs).symm
  rw [hrec] at hdct
  have hraw :=
    (dimensionOneRosserModelMinusPartialSum_tendsto_raw hs).comp
      (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hraw hdct

/-- The upper identity in Iwaniec's Eq. (7.7), including the endpoint three. -/
theorem dimensionOneRosserModelPlusRaw_eq_integral_Ioi
    {s : Real} (hs : 3 <= s) :
    dimensionOneRosserModelPlusRaw s =
      ∫ t in Ioi s, dimensionOneRosserModelMinusRaw (t - 1) / (t - 1) := by
  have hdct := (dimensionOneRosserModelPlusRaw_dctData hs).2
  have hrec :
      (fun R => ∫ t in Ioi s,
        dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1)) =
      fun R => dimensionOneRosserModelPlusPartialSum R s := by
    funext R
    exact (dimensionOneRosserModelPlusPartialSum_integral R hs).symm
  rw [hrec] at hdct
  exact tendsto_nhds_unique
    (dimensionOneRosserModelPlusPartialSum_tendsto_raw (by linarith)) hdct

end PrimesRestrictedDigits
