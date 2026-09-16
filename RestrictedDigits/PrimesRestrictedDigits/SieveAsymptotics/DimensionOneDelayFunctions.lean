import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelaySteps

/-!
# Dimension-one delay functions

This is Iwaniec's Section 6 delay system at `kappa=1`, `beta=2`; see
`IWANIEC-ROSSER-SIEVE-1980`, printed p. 189, Eqs. (6.1)--(6.2).

The scaled functions are constructed in the preceding method-of-steps module. Here we recover
the source functions `Q+`, `Q-` on the positive reals and prove the finite Volterra and strict
differential equations. Positivity and decay are separate downstream theorems.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

theorem dimensionOneDelayScaledMinus_eq_integral {s : Real} (hs : 2 <= s) :
    dimensionOneDelayScaledMinus s =
      1 - ∫ t in 2..s,
        t * dimensionOneDelayScaledPlus (t - 1) / (t - 1) ^ 2 := by
  rw [dimensionOneDelayScaledMinus_eq_stepUpdate,
    dimensionOneDelayStepUpdate_eq_integral_of_le _ hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hs] at ht
  unfold dimensionOneDelayStepKernel
  rw [max_eq_right ht.1]

theorem dimensionOneDelayScaledPlus_eq_integral {s : Real} (hs : 3 <= s) :
    dimensionOneDelayScaledPlus s =
      1 / 2 - ∫ t in 3..s,
        t * dimensionOneDelayScaledMinus (t - 1) / (t - 1) ^ 2 := by
  rw [dimensionOneDelayScaledPlus_eq_stepUpdate,
    dimensionOneDelayStepUpdate_eq_integral_of_le _ hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hs] at ht
  unfold dimensionOneDelayStepKernel
  rw [max_eq_right ht.1]

private theorem dimensionOneDelayStepUpdate_hasDerivAt_of_lt
    {threshold initial s : Real} (hthreshold : 1 < threshold)
    {f : Real -> Real} (hf : Continuous f) (hs : threshold < s) :
    HasDerivAt (dimensionOneDelayStepUpdate threshold initial f)
      (-(s * f (s - 1) / (s - 1) ^ 2)) s := by
  have hkernel := dimensionOneDelayStepKernel_continuous hthreshold hf
  have hbase : HasDerivAt
      (fun u => initial - ∫ t in threshold..u,
        dimensionOneDelayStepKernel threshold f t)
      (-(dimensionOneDelayStepKernel threshold f s)) s := by
    exact (hkernel.integral_hasStrictDerivAt threshold s).hasDerivAt.const_sub initial
  have heq : Filter.Eventually
      (fun u => dimensionOneDelayStepUpdate threshold initial f u =
        initial - ∫ t in threshold..u,
          dimensionOneDelayStepKernel threshold f t)
      (nhds s) := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    rw [dimensionOneDelayStepUpdate, max_eq_right hu.le]
  have h := hbase.congr_of_eventuallyEq heq
  apply h.congr_deriv
  unfold dimensionOneDelayStepKernel
  rw [max_eq_right hs.le]

noncomputable def dimensionOneDelayQPlus (s : Real) : Real :=
  dimensionOneDelayScaledPlus s / s ^ 2

noncomputable def dimensionOneDelayQMinus (s : Real) : Real :=
  dimensionOneDelayScaledMinus s / s ^ 2

theorem dimensionOneDelayQPlus_continuousOn :
    ContinuousOn dimensionOneDelayQPlus (Ioi 0) := by
  apply dimensionOneDelayScaledPlus_continuous.continuousOn.div
    (continuousOn_id.pow 2)
  intro s hs
  exact pow_ne_zero _ hs.ne'

theorem dimensionOneDelayQMinus_continuousOn :
    ContinuousOn dimensionOneDelayQMinus (Ioi 0) := by
  apply dimensionOneDelayScaledMinus_continuous.continuousOn.div
    (continuousOn_id.pow 2)
  intro s hs
  exact pow_ne_zero _ hs.ne'

theorem sq_mul_dimensionOneDelayQPlus {s : Real} (hs : s ≠ 0) :
    s ^ 2 * dimensionOneDelayQPlus s = dimensionOneDelayScaledPlus s := by
  rw [dimensionOneDelayQPlus]
  field_simp [hs]

theorem sq_mul_dimensionOneDelayQMinus {s : Real} (hs : s ≠ 0) :
    s ^ 2 * dimensionOneDelayQMinus s = dimensionOneDelayScaledMinus s := by
  rw [dimensionOneDelayQMinus]
  field_simp [hs]

theorem dimensionOneDelayQPlus_initial {s : Real} (hs0 : 0 < s)
    (hs3 : s <= 3) :
    s ^ 2 * dimensionOneDelayQPlus s = 1 / 2 := by
  rw [sq_mul_dimensionOneDelayQPlus hs0.ne',
    dimensionOneDelayScaledPlus_eq_half_of_le hs3]

theorem dimensionOneDelayQMinus_initial {s : Real} (hs0 : 0 < s)
    (hs2 : s <= 2) :
    s ^ 2 * dimensionOneDelayQMinus s = 1 := by
  rw [sq_mul_dimensionOneDelayQMinus hs0.ne',
    dimensionOneDelayScaledMinus_eq_one_of_le hs2]

theorem dimensionOneDelayScaledPlus_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt dimensionOneDelayScaledPlus
      (-s * dimensionOneDelayQMinus (s - 1)) s := by
  rw [show dimensionOneDelayScaledPlus =
      dimensionOneDelayStepUpdate 3 (1 / 2) dimensionOneDelayScaledMinus by
    funext t
    exact dimensionOneDelayScaledPlus_eq_stepUpdate t]
  convert dimensionOneDelayStepUpdate_hasDerivAt_of_lt (by norm_num)
    dimensionOneDelayScaledMinus_continuous hs using 1
  rw [dimensionOneDelayQMinus]
  ring

theorem dimensionOneDelayScaledMinus_hasDerivAt {s : Real} (hs : 2 < s) :
    HasDerivAt dimensionOneDelayScaledMinus
      (-s * dimensionOneDelayQPlus (s - 1)) s := by
  rw [show dimensionOneDelayScaledMinus =
      dimensionOneDelayStepUpdate 2 1 dimensionOneDelayScaledPlus by
    funext t
    exact dimensionOneDelayScaledMinus_eq_stepUpdate t]
  convert dimensionOneDelayStepUpdate_hasDerivAt_of_lt (by norm_num)
    dimensionOneDelayScaledPlus_continuous hs using 1
  rw [dimensionOneDelayQPlus]
  ring

theorem dimensionOneDelayQPlus_scaled_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt (fun t => t ^ 2 * dimensionOneDelayQPlus t)
      (-s * dimensionOneDelayQMinus (s - 1)) s := by
  apply (dimensionOneDelayScaledPlus_hasDerivAt hs).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by linarith : 0 < s)] with t ht
  have ht0 : 0 < t := ht
  exact sq_mul_dimensionOneDelayQPlus ht0.ne'

theorem dimensionOneDelayQMinus_scaled_hasDerivAt {s : Real} (hs : 2 < s) :
    HasDerivAt (fun t => t ^ 2 * dimensionOneDelayQMinus t)
      (-s * dimensionOneDelayQPlus (s - 1)) s := by
  apply (dimensionOneDelayScaledMinus_hasDerivAt hs).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by linarith : 0 < s)] with t ht
  have ht0 : 0 < t := ht
  exact sq_mul_dimensionOneDelayQMinus ht0.ne'

end PrimesRestrictedDigits
