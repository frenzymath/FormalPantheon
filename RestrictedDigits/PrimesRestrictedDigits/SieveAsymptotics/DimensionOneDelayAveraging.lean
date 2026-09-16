import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayAveragingSeams
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Averaging identities for the dimension-one delay system

This proves Iwaniec's corrected Eqs. (6.12)--(6.13) at `kappa=1`, `beta=2`. The additive
constants at `s=3` come from the exact seam calculations in the preceding module; see
`IWANIEC-ROSSER-SIEVE-1980`, printed pp. 189--190.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem hasDerivAt_integral_sub_one
    {f : Real -> Real} (hf : ContinuousOn f (Ioi 0))
    {s : Real} (hs : 1 < s) :
    HasDerivAt (fun u => ∫ t in u - 1..u, f t) (f s - f (s - 1)) s := by
  have hleft : ContinuousAt f (s - 1) :=
    hf.continuousAt (Ioi_mem_nhds (by linarith))
  have hright : ContinuousAt f s :=
    hf.continuousAt (Ioi_mem_nhds (by linarith))
  have hcont : ContinuousOn f (Icc (s - 1) s) := by
    exact hf.mono (by
      intro x hx
      exact (by linarith [hx.1] : 0 < x))
  have hint : IntervalIntegrable f volume (s - 1) s :=
    hcont.intervalIntegrable_of_Icc (by linarith)
  have hmeasLeft : StronglyMeasurableAtFilter f (nhds (s - 1)) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hf (s - 1) (by
      show 0 < s - 1
      linarith)
  have hmeasRight : StronglyMeasurableAtFilter f (nhds s) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hf s (by
      show 0 < s
      linarith)
  have hintegral := intervalIntegral.integral_hasFDerivAt hint
    hmeasLeft hmeasRight hleft hright
  have hpair : HasFDerivAt (fun u : Real => (u - 1, u))
      ((ContinuousLinearMap.toSpanSingleton Real 1).prod
        (ContinuousLinearMap.toSpanSingleton Real 1)) s := by
    simpa only [id_eq] using
      ((hasDerivAt_id s).sub_const 1).hasFDerivAt.prodMk
        (hasDerivAt_id s).hasFDerivAt
  have h := (hintegral.comp (f := fun u : Real => (u - 1, u)) s hpair).hasDerivAt
  apply h.congr_deriv
  simp

noncomputable def dimensionOneDelaySumAveragingDefect (s : Real) : Real :=
  s * dimensionOneDelaySum s * dimensionOneDelayConjugateWeight s -
    ∫ x in s - 1..s,
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1)

noncomputable def dimensionOneDelayDifferenceAveragingDefect (s : Real) : Real :=
  s * dimensionOneDelayDifference s +
    ∫ x in s - 1..s, dimensionOneDelayDifference x

theorem dimensionOneDelaySumAveragingDefect_hasDerivAt
    {s : Real} (hs : 3 < s) :
    HasDerivAt dimensionOneDelaySumAveragingDefect 0 s := by
  have hGshift : Continuous (fun x : Real =>
      dimensionOneDelayConjugateWeight (x + 1)) :=
    dimensionOneDelayConjugateWeight_continuous.comp
      (continuous_id.add continuous_const)
  have hwindow := hasDerivAt_integral_sub_one
    (dimensionOneDelaySum_continuousOn.mul hGshift.continuousOn)
    (by linarith : 1 < s)
  have hleft := ((hasDerivAt_id s).mul
    (dimensionOneDelaySum_hasDerivAt hs)).mul
      (dimensionOneDelayConjugateWeight_hasDerivAt s)
  unfold dimensionOneDelaySumAveragingDefect
  have h := hleft.sub hwindow
  apply h.congr_deriv
  unfold dimensionOneDelayConjugateWeight
  simp only [id_eq, Pi.mul_apply]
  field_simp [show s ≠ 0 by linarith]
  ring

theorem dimensionOneDelayDifferenceAveragingDefect_hasDerivAt
    {s : Real} (hs : 3 < s) :
    HasDerivAt dimensionOneDelayDifferenceAveragingDefect 0 s := by
  have hwindow := hasDerivAt_integral_sub_one
    dimensionOneDelayDifference_continuousOn (by linarith : 1 < s)
  have hleft := (hasDerivAt_id s).mul
    (dimensionOneDelayDifference_hasDerivAt hs)
  unfold dimensionOneDelayDifferenceAveragingDefect
  have h := hleft.add hwindow
  apply h.congr_deriv
  simp only [id_eq]
  field_simp [show s ≠ 0 by linarith]
  ring

private theorem dimensionOneDelaySumAveragingDefect_three :
    dimensionOneDelaySumAveragingDefect 3 = 0 := by
  unfold dimensionOneDelaySumAveragingDefect
  convert dimensionOneDelaySum_averaging_seam using 1
  all_goals norm_num

private theorem dimensionOneDelayDifferenceAveragingDefect_three :
    dimensionOneDelayDifferenceAveragingDefect 3 = 0 := by
  unfold dimensionOneDelayDifferenceAveragingDefect
  convert dimensionOneDelayDifference_averaging_seam using 1
  all_goals norm_num

private theorem dimensionOneDelaySumAveragingDefect_continuousOn :
    ContinuousOn dimensionOneDelaySumAveragingDefect (Ioi 1) := by
  have hGShift : Continuous (fun x : Real =>
      dimensionOneDelayConjugateWeight (x + 1)) :=
    dimensionOneDelayConjugateWeight_continuous.comp
      (continuous_id.add continuous_const)
  have hWindow : ContinuousOn (fun u => ∫ x in u - 1..u,
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1))
      (Ioi 1) := by
    intro s hs
    exact (hasDerivAt_integral_sub_one
      (dimensionOneDelaySum_continuousOn.mul hGShift.continuousOn) hs).continuousAt
        |>.continuousWithinAt
  have hPositive : Ioi (1 : Real) ⊆ Ioi 0 := by
    intro s hs
    change 1 < s at hs
    change 0 < s
    linarith
  have hLeft : ContinuousOn (fun s =>
      s * dimensionOneDelaySum s * dimensionOneDelayConjugateWeight s)
      (Ioi 1) :=
    (continuousOn_id.mul (dimensionOneDelaySum_continuousOn.mono hPositive)).mul
      dimensionOneDelayConjugateWeight_continuous.continuousOn
  unfold dimensionOneDelaySumAveragingDefect
  exact hLeft.sub hWindow

private theorem dimensionOneDelayDifferenceAveragingDefect_continuousOn :
    ContinuousOn dimensionOneDelayDifferenceAveragingDefect (Ioi 1) := by
  have hWindow : ContinuousOn
      (fun u => ∫ x in u - 1..u, dimensionOneDelayDifference x) (Ioi 1) := by
    intro s hs
    exact (hasDerivAt_integral_sub_one
      dimensionOneDelayDifference_continuousOn hs).continuousAt.continuousWithinAt
  have hPositive : Ioi (1 : Real) ⊆ Ioi 0 := by
    intro s hs
    change 1 < s at hs
    change 0 < s
    linarith
  have hLeft : ContinuousOn
      (fun s => s * dimensionOneDelayDifference s) (Ioi 1) :=
    continuousOn_id.mul (dimensionOneDelayDifference_continuousOn.mono hPositive)
  unfold dimensionOneDelayDifferenceAveragingDefect
  exact hLeft.add hWindow

theorem dimensionOneDelaySumAveragingDefect_eq_zero
    {s : Real} (hs : 3 <= s) :
    dimensionOneDelaySumAveragingDefect s = 0 := by
  rcases hs.eq_or_lt with rfl | hs
  · exact dimensionOneDelaySumAveragingDefect_three
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.le
    (dimensionOneDelaySumAveragingDefect_continuousOn.mono (by
      intro x hx
      exact (by linarith [hx.1] : 1 < x)))
    (fun x hx => dimensionOneDelaySumAveragingDefect_hasDerivAt hx.1)
    (continuousOn_const.intervalIntegrable_of_Icc hs.le)
  rw [dimensionOneDelaySumAveragingDefect_three] at hFTC
  simpa using hFTC.symm

theorem dimensionOneDelayDifferenceAveragingDefect_eq_zero
    {s : Real} (hs : 3 <= s) :
    dimensionOneDelayDifferenceAveragingDefect s = 0 := by
  rcases hs.eq_or_lt with rfl | hs
  · exact dimensionOneDelayDifferenceAveragingDefect_three
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.le
    (dimensionOneDelayDifferenceAveragingDefect_continuousOn.mono (by
      intro x hx
      exact (by linarith [hx.1] : 1 < x)))
    (fun x hx => dimensionOneDelayDifferenceAveragingDefect_hasDerivAt hx.1)
    (continuousOn_const.intervalIntegrable_of_Icc hs.le)
  rw [dimensionOneDelayDifferenceAveragingDefect_three] at hFTC
  simpa using hFTC.symm

theorem dimensionOneDelaySum_averaging {s : Real} (hs : 3 <= s) :
    s * dimensionOneDelaySum s * dimensionOneDelayConjugateWeight s =
      ∫ x in s - 1..s,
        dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1) := by
  have h := dimensionOneDelaySumAveragingDefect_eq_zero hs
  unfold dimensionOneDelaySumAveragingDefect at h
  linarith

theorem dimensionOneDelayDifference_averaging {s : Real} (hs : 3 <= s) :
    s * dimensionOneDelayDifference s =
      -(∫ x in s - 1..s, dimensionOneDelayDifference x) := by
  have h := dimensionOneDelayDifferenceAveragingDefect_eq_zero hs
  unfold dimensionOneDelayDifferenceAveragingDefect at h
  linarith

end PrimesRestrictedDigits
