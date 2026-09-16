import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelAffineExtension

/-!
# Regularity of the raw dimension-one Rosser model

This derives continuity and the strict-tail differential form of Iwaniec's Eq. (7.7). The
endpoint identities remain integral identities; no derivative is asserted at two or three. See
`IWANIEC-ROSSER-SIEVE-1980`, printed p. 195.
-/

open Filter MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem hasDerivAt_integral_Ioi
    {f : Real -> Real} {a s : Real}
    (hint : IntegrableOn f (Ioi a)) (has : a < s)
    (hcont : ContinuousOn f (Ioi a)) :
    HasDerivAt (fun u => ∫ x in Ioi u, f x) (-f s) s := by
  have hIci : IntegrableOn f (Ici a) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hint
  have huIcc : uIcc a s ⊆ Ici a := by
    rw [uIcc_of_le has.le]
    exact Icc_subset_Ici_self
  have hinter := (hIci.mono_set huIcc).intervalIntegrable
  have hcontAt := hcont.continuousAt (Ioi_mem_nhds has)
  have hmeas : StronglyMeasurableAtFilter f (nhds s) volume :=
    hcont.stronglyMeasurableAtFilter isOpen_Ioi s has
  have hprimitive :=
    intervalIntegral.integral_hasDerivAt_right hinter hmeas hcontAt
  have hsub := (hasDerivAt_const s (∫ x in Ioi a, f x)).sub hprimitive
  have hfun :
      ((fun _ : Real => ∫ x in Ioi a, f x) -
        fun u => ∫ x in a..u, f x) =
      (fun u => (∫ x in Ioi a, f x) - ∫ x in a..u, f x) := by
    funext u
    rfl
  rw [hfun] at hsub
  have hrhs : HasDerivAt
      (fun u => (∫ x in Ioi a, f x) - ∫ x in a..u, f x)
      (-f s) s := by
    simpa only [zero_sub] using hsub
  apply hrhs.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds has] with u hu
  have hdiff := intervalIntegral.integral_Ioi_sub_Ioi hint hu.le
  linarith

/-- Continuity of the raw lower model on its closed source domain. -/
theorem continuousOn_dimensionOneRosserModelMinusRaw :
    ContinuousOn dimensionOneRosserModelMinusRaw (Ici 2) := by
  have htail :=
    (integrableOn_shifted_dimensionOneRosserModelPlusRaw
      (s := (2 : Real)) le_rfl).continuousOn_Ici_primitive_Ioi
  apply htail.congr
  intro s hs
  exact dimensionOneRosserModelMinusRaw_eq_integral_Ioi hs

private theorem continuousOn_dimensionOneRosserModelPlusRaw_Ici_two :
    ContinuousOn dimensionOneRosserModelPlusRaw (Ici 2) := by
  have hleft :
      ContinuousOn dimensionOneRosserModelPlusRaw (Icc 2 3) := by
    have hbase : ContinuousOn
        (fun s : Real => dimensionOneRosserModelPlusAffineConstant - s)
        (Icc 2 3) :=
      (continuous_const.sub continuous_id).continuousOn
    apply hbase.congr
    intro s hs
    have hplus := dimensionOneRosserModelPlusRaw_add_eq_affineConstant
      (show 1 < s by linarith [hs.1]) hs.2
    linarith
  have hright :
      ContinuousOn dimensionOneRosserModelPlusRaw (Ici 3) := by
    have htail :=
      (integrableOn_shifted_dimensionOneRosserModelMinusRaw
        (s := (3 : Real)) le_rfl).continuousOn_Ici_primitive_Ioi
    apply htail.congr
    intro s hs
    exact dimensionOneRosserModelPlusRaw_eq_integral_Ioi hs
  rw [<- Icc_union_Ici_eq_Ici (show (2 : Real) <= 3 by norm_num)]
  exact hleft.union_of_isClosed hright isClosed_Icc isClosed_Ici

/-- Continuity of the raw upper model on its strict source domain. -/
theorem continuousOn_dimensionOneRosserModelPlusRaw :
    ContinuousOn dimensionOneRosserModelPlusRaw (Ioi 1) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  by_cases hs2 : 2 < s
  · exact continuousOn_dimensionOneRosserModelPlusRaw_Ici_two.continuousAt
      (Ici_mem_nhds hs2)
  · have hs3 : s < 3 := by linarith
    have hlocal : ∀ᶠ u in nhds s, 1 < u ∧ u <= 3 := by
      filter_upwards [Ioi_mem_nhds hs, Iic_mem_nhds hs3] with u hu1 hu3
      exact ⟨hu1, hu3⟩
    have hbase : ContinuousAt
        (fun u : Real => dimensionOneRosserModelPlusAffineConstant - u) s :=
      (continuous_const.sub continuous_id).continuousAt
    apply hbase.congr_of_eventuallyEq
    filter_upwards [hlocal] with u hu
    have hplus := dimensionOneRosserModelPlusRaw_add_eq_affineConstant
      hu.1 hu.2
    linarith

private theorem continuousOn_shifted_dimensionOneRosserModelPlusRaw :
    ContinuousOn
      (fun t => dimensionOneRosserModelPlusRaw (t - 1) / (t - 1))
      (Ioi 2) := by
  have hshift : Continuous (fun t : Real => t - 1) :=
    continuous_id.sub continuous_const
  have hnum : ContinuousOn
      (fun t => dimensionOneRosserModelPlusRaw (t - 1)) (Ioi 2) := by
    change ContinuousOn
      (Function.comp dimensionOneRosserModelPlusRaw
        (fun t : Real => t - 1)) (Ioi 2)
    apply continuousOn_dimensionOneRosserModelPlusRaw.comp hshift.continuousOn
    intro t ht
    change 1 < t - 1
    linarith [mem_Ioi.mp ht]
  apply hnum.div hshift.continuousOn
  intro t ht
  linarith [mem_Ioi.mp ht]

private theorem continuousOn_shifted_dimensionOneRosserModelMinusRaw :
    ContinuousOn
      (fun t => dimensionOneRosserModelMinusRaw (t - 1) / (t - 1))
      (Ioi 3) := by
  have hshift : Continuous (fun t : Real => t - 1) :=
    continuous_id.sub continuous_const
  have hnum : ContinuousOn
      (fun t => dimensionOneRosserModelMinusRaw (t - 1)) (Ioi 3) := by
    change ContinuousOn
      (Function.comp dimensionOneRosserModelMinusRaw
        (fun t : Real => t - 1)) (Ioi 3)
    apply continuousOn_dimensionOneRosserModelMinusRaw.comp hshift.continuousOn
    intro t ht
    change 2 <= t - 1
    linarith [mem_Ioi.mp ht]
  apply hnum.div hshift.continuousOn
  intro t ht
  linarith [mem_Ioi.mp ht]

/-- The strict-tail differential form of the raw lower recurrence. -/
theorem hasDerivAt_dimensionOneRosserModelMinusRaw
    {s : Real} (hs : 2 < s) :
    HasDerivAt dimensionOneRosserModelMinusRaw
      (-dimensionOneRosserModelPlusRaw (s - 1) / (s - 1)) s := by
  have htail := hasDerivAt_integral_Ioi
    (integrableOn_shifted_dimensionOneRosserModelPlusRaw
      (s := (2 : Real)) le_rfl) hs
    continuousOn_shifted_dimensionOneRosserModelPlusRaw
  have hraw : HasDerivAt dimensionOneRosserModelMinusRaw
      (-(dimensionOneRosserModelPlusRaw (s - 1) / (s - 1))) s :=
    htail.congr_of_eventuallyEq (by
      filter_upwards [eventually_gt_nhds hs] with u hu
      exact dimensionOneRosserModelMinusRaw_eq_integral_Ioi hu.le)
  simpa only [neg_div] using hraw

/-- The strict-tail differential form of the raw upper recurrence. -/
theorem hasDerivAt_dimensionOneRosserModelPlusRaw
    {s : Real} (hs : 3 < s) :
    HasDerivAt dimensionOneRosserModelPlusRaw
      (-dimensionOneRosserModelMinusRaw (s - 1) / (s - 1)) s := by
  have htail := hasDerivAt_integral_Ioi
    (integrableOn_shifted_dimensionOneRosserModelMinusRaw
      (s := (3 : Real)) le_rfl) hs
    continuousOn_shifted_dimensionOneRosserModelMinusRaw
  have hraw : HasDerivAt dimensionOneRosserModelPlusRaw
      (-(dimensionOneRosserModelMinusRaw (s - 1) / (s - 1))) s :=
    htail.congr_of_eventuallyEq (by
      filter_upwards [eventually_gt_nhds hs] with u hu
      exact dimensionOneRosserModelPlusRaw_eq_integral_Ioi hu.le)
  simpa only [neg_div] using hraw

/-- Continuity of the raw sum on the common closed domain. -/
theorem continuousOn_dimensionOneRosserModelRawSum :
    ContinuousOn dimensionOneRosserModelRawSum (Ici 2) := by
  change ContinuousOn
    (fun s => dimensionOneRosserModelPlusRaw s +
      dimensionOneRosserModelMinusRaw s) (Ici 2)
  exact continuousOn_dimensionOneRosserModelPlusRaw_Ici_two.add
    continuousOn_dimensionOneRosserModelMinusRaw

/-- The dimension-one first conjugate delay equation for the raw sum. -/
theorem hasDerivAt_dimensionOneRosserModelRawSum
    {s : Real} (hs : 3 < s) :
    HasDerivAt dimensionOneRosserModelRawSum
      (-dimensionOneRosserModelRawSum (s - 1) / (s - 1)) s := by
  have h := (hasDerivAt_dimensionOneRosserModelPlusRaw hs).add
    (hasDerivAt_dimensionOneRosserModelMinusRaw (by linarith))
  change HasDerivAt
    (fun u => dimensionOneRosserModelPlusRaw u +
      dimensionOneRosserModelMinusRaw u)
    (-(dimensionOneRosserModelPlusRaw (s - 1) +
      dimensionOneRosserModelMinusRaw (s - 1)) / (s - 1)) s
  apply h.congr_deriv
  ring

end PrimesRestrictedDigits
