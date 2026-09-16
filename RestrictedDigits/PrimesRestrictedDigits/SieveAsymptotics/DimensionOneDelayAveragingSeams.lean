import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayAveragingFoundations

/-!
# Seam values for the dimension-one averaging identities

This computes the two additive constants in Iwaniec's Section 6 averaging identities at the
nondifferentiable seam `s = 3`. The proof uses only the middle-strip delay equations and exact
rational integrals on `[2, 3]`; it does not use the downstream positivity or decay theory. See
`IWANIEC-ROSSER-SIEVE-1980`, printed pp. 189--190, Eqs. (6.12)--(6.13).
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem dimensionOneDelayQPlus_shift_integral :
    (∫ s in (2 : Real)..3, dimensionOneDelayQPlus (s - 1)) = 1 / 4 := by
  have hPrimitive : ContinuousOn
      (fun s : Real => (-1 / 2) * (s - 1)⁻¹) (Icc 2 3) := by
    exact continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀ (by
        intro s hs
        change s - 1 ≠ 0
        linarith [hs.1]))
  have hKernel : ContinuousOn
      (fun s : Real => 1 / (2 * (s - 1) ^ 2)) (Icc 2 3) := by
    apply continuousOn_const.div
      (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2))
    intro s hs
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by
      change s - 1 ≠ 0
      linarith [hs.1]))
  have hDeriv : ∀ s ∈ Ioo (2 : Real) 3,
      HasDerivAt (fun t : Real => (-1 / 2) * (t - 1)⁻¹)
        (1 / (2 * (s - 1) ^ 2)) s := by
    intro s hs
    have h := (((hasDerivAt_id s).sub_const 1).inv (by
      simpa only [id_eq] using (show s - 1 ≠ 0 by linarith [hs.1]))).const_mul
        (-1 / 2 : Real)
    simp only [id_eq, Pi.inv_apply] at h
    exact h.congr_deriv (by
      field_simp [show s - 1 ≠ 0 by linarith [hs.1]])
  have hIntegral := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (2 : Real) <= 3) hPrimitive hDeriv
      (hKernel.intervalIntegrable_of_Icc (by norm_num))
  have hCongr :
      (∫ s in (2 : Real)..3, dimensionOneDelayQPlus (s - 1)) =
        ∫ s in (2 : Real)..3, 1 / (2 * (s - 1) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (2 : Real) <= 3)] at hs
    exact dimensionOneDelayQPlus_shift_middle hs.1 hs.2
  rw [hCongr, hIntegral]
  norm_num

private theorem dimensionOneDelayConjugateQPlus_shift_integral :
    (∫ s in (2 : Real)..3,
      dimensionOneDelayConjugateWeight s *
        dimensionOneDelayQPlus (s - 1)) = 3 / 8 := by
  have hQContinuous : ContinuousOn
      (fun s : Real => dimensionOneDelayQPlus (s - 1)) (Icc 2 3) := by
    exact dimensionOneDelayQPlus_continuousOn.comp
      (continuousOn_id.sub continuousOn_const) (by
        intro s hs
        change 0 < s - 1
        linarith [hs.1])
  have hQIntegrable : IntervalIntegrable
      (fun s : Real => dimensionOneDelayQPlus (s - 1)) volume 2 3 :=
    hQContinuous.intervalIntegrable_of_Icc (by norm_num)
  have hConstIntegrable : IntervalIntegrable (fun _ : Real => (1 / 2 : Real))
      volume 2 3 := continuousOn_const.intervalIntegrable_of_Icc
        (by norm_num : (2 : Real) <= 3)
  calc
    (∫ s in (2 : Real)..3,
        dimensionOneDelayConjugateWeight s *
          dimensionOneDelayQPlus (s - 1)) =
        ∫ s in (2 : Real)..3,
          1 / 2 - (1 / 2) * dimensionOneDelayQPlus (s - 1) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (2 : Real) <= 3)] at hs
      change dimensionOneDelayConjugateWeight s *
        dimensionOneDelayQPlus (s - 1) =
          1 / 2 - (1 / 2) * dimensionOneDelayQPlus (s - 1)
      rw [dimensionOneDelayQPlus_shift_middle hs.1 hs.2]
      unfold dimensionOneDelayConjugateWeight
      field_simp [show s - 1 ≠ 0 by linarith [hs.1]]
    _ = (∫ _s in (2 : Real)..3, 1 / 2) -
        ∫ s in (2 : Real)..3,
          (1 / 2) * dimensionOneDelayQPlus (s - 1) := by
      rw [intervalIntegral.integral_sub hConstIntegrable
        (hQIntegrable.const_mul (1 / 2))]
    _ = 3 / 8 := by
      rw [intervalIntegral.integral_const_mul,
        dimensionOneDelayQPlus_shift_integral]
      norm_num

private theorem dimensionOneDelaySum_two :
    dimensionOneDelaySum 2 = 3 / 8 := by
  unfold dimensionOneDelaySum dimensionOneDelayQPlus dimensionOneDelayQMinus
  rw [dimensionOneDelayScaledPlus_eq_half_of_le (by norm_num),
    dimensionOneDelayScaledMinus_eq_one_of_le (by norm_num)]
  norm_num

private theorem dimensionOneDelayDifference_two :
    dimensionOneDelayDifference 2 = -1 / 8 := by
  unfold dimensionOneDelayDifference dimensionOneDelayQPlus
    dimensionOneDelayQMinus
  rw [dimensionOneDelayScaledPlus_eq_half_of_le (by norm_num),
    dimensionOneDelayScaledMinus_eq_one_of_le (by norm_num)]
  norm_num

private theorem dimensionOneDelayDifference_mul_hasDerivAt_middle
    {s : Real} (hs2 : 2 < s) (hs3 : s < 3) :
    HasDerivAt (fun t => t * dimensionOneDelayDifference t)
      (-dimensionOneDelayDifference s + dimensionOneDelayQPlus (s - 1)) s := by
  have h := (hasDerivAt_id s).mul
    (dimensionOneDelayDifference_hasDerivAt_middle hs2 hs3)
  apply h.congr_deriv
  simp only [id_eq, one_mul]
  field_simp [show s ≠ 0 by linarith]
  ring

private theorem dimensionOneDelaySum_weighted_hasDerivAt_middle
    {s : Real} (hs2 : 2 < s) (hs3 : s < 3) :
    HasDerivAt
      (fun t => t * dimensionOneDelaySum t *
        dimensionOneDelayConjugateWeight t)
      (dimensionOneDelaySum s * dimensionOneDelayConjugateWeight (s + 1) -
        dimensionOneDelayConjugateWeight s *
          dimensionOneDelayQPlus (s - 1)) s := by
  have h := ((hasDerivAt_id s).mul
    (dimensionOneDelaySum_hasDerivAt_middle hs2 hs3)).mul
      (dimensionOneDelayConjugateWeight_hasDerivAt s)
  apply h.congr_deriv
  simp only [id_eq, one_mul, Pi.mul_apply]
  unfold dimensionOneDelayConjugateWeight
  field_simp [show s ≠ 0 by linarith]
  ring

/-- Exact cancellation for the unweighted averaging defect at the seam. -/
theorem dimensionOneDelayDifference_averaging_seam :
    3 * dimensionOneDelayDifference 3 +
      ∫ x in (2 : Real)..3, dimensionOneDelayDifference x = 0 := by
  have hDifferenceContinuous : ContinuousOn dimensionOneDelayDifference
      (Icc 2 3) := dimensionOneDelayDifference_continuousOn.mono (by
    intro s hs
    exact (by linarith [hs.1] : 0 < s))
  have hQShiftContinuous : ContinuousOn
      (fun s : Real => dimensionOneDelayQPlus (s - 1)) (Icc 2 3) := by
    exact dimensionOneDelayQPlus_continuousOn.comp
      (continuousOn_id.sub continuousOn_const) (by
        intro s hs
        change 0 < s - 1
        linarith [hs.1])
  have hDifferenceIntegrable : IntervalIntegrable dimensionOneDelayDifference
      volume 2 3 := hDifferenceContinuous.intervalIntegrable_of_Icc (by norm_num)
  have hQShiftIntegrable : IntervalIntegrable
      (fun s : Real => dimensionOneDelayQPlus (s - 1)) volume 2 3 :=
    hQShiftContinuous.intervalIntegrable_of_Icc (by norm_num)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (2 : Real) <= 3)
    (continuousOn_id.mul hDifferenceContinuous)
    (fun s hs => dimensionOneDelayDifference_mul_hasDerivAt_middle hs.1 hs.2)
    ((hDifferenceIntegrable.neg).add hQShiftIntegrable)
  have hSplit := intervalIntegral.integral_add hDifferenceIntegrable.neg
    hQShiftIntegrable
  simp only [Pi.neg_apply] at hSplit
  rw [hSplit, intervalIntegral.integral_neg,
    dimensionOneDelayQPlus_shift_integral] at hFTC
  norm_num only [Pi.mul_apply, id_eq] at hFTC
  rw [dimensionOneDelayDifference_two] at hFTC
  linarith

/-- Exact cancellation for the conjugate-weighted averaging defect at the seam. -/
theorem dimensionOneDelaySum_averaging_seam :
    3 * dimensionOneDelaySum 3 * dimensionOneDelayConjugateWeight 3 -
      ∫ x in (2 : Real)..3,
        dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1) = 0 := by
  have hSumContinuous : ContinuousOn dimensionOneDelaySum (Icc 2 3) :=
    dimensionOneDelaySum_continuousOn.mono (by
      intro s hs
      exact (by linarith [hs.1] : 0 < s))
  have hGShiftContinuous : ContinuousOn
      (fun s : Real => dimensionOneDelayConjugateWeight (s + 1))
      (Icc 2 3) := dimensionOneDelayConjugateWeight_continuous.continuousOn.comp
        (continuousOn_id.add continuousOn_const) (fun _ _ => mem_univ _)
  have hQShiftContinuous : ContinuousOn
      (fun s : Real => dimensionOneDelayQPlus (s - 1)) (Icc 2 3) := by
    exact dimensionOneDelayQPlus_continuousOn.comp
      (continuousOn_id.sub continuousOn_const) (by
        intro s hs
        change 0 < s - 1
        linarith [hs.1])
  have hMainIntegrable : IntervalIntegrable
      (fun s : Real => dimensionOneDelaySum s *
        dimensionOneDelayConjugateWeight (s + 1)) volume 2 3 :=
    (hSumContinuous.mul hGShiftContinuous).intervalIntegrable_of_Icc (by norm_num)
  have hErrorIntegrable : IntervalIntegrable
      (fun s : Real => dimensionOneDelayConjugateWeight s *
        dimensionOneDelayQPlus (s - 1)) volume 2 3 :=
    (dimensionOneDelayConjugateWeight_continuous.continuousOn.mul
      hQShiftContinuous).intervalIntegrable_of_Icc (by norm_num)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (2 : Real) <= 3)
    ((continuousOn_id.mul hSumContinuous).mul
      dimensionOneDelayConjugateWeight_continuous.continuousOn)
    (fun s hs => dimensionOneDelaySum_weighted_hasDerivAt_middle hs.1 hs.2)
    (hMainIntegrable.sub hErrorIntegrable)
  have hSplit := intervalIntegral.integral_sub hMainIntegrable hErrorIntegrable
  rw [hSplit, dimensionOneDelayConjugateQPlus_shift_integral] at hFTC
  norm_num only [Pi.mul_apply, id_eq] at hFTC
  rw [dimensionOneDelaySum_two] at hFTC
  norm_num [dimensionOneDelayConjugateWeight] at hFTC ⊢
  linarith

end PrimesRestrictedDigits
