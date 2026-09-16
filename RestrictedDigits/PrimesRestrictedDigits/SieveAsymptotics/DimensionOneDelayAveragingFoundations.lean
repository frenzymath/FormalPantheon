import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayFunctions
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Foundations for the dimension-one averaging identities

This introduces the corrected Section 6 sum, difference, and conjugate weight, then derives
their strict delay equations from the scaled system. See `IWANIEC-ROSSER-SIEVE-1980`, printed
pp. 189--190, Eqs. (6.6)--(6.13).
-/

open Set

namespace PrimesRestrictedDigits

noncomputable def dimensionOneDelaySum (s : Real) : Real :=
  dimensionOneDelayQPlus s + dimensionOneDelayQMinus s

noncomputable def dimensionOneDelayDifference (s : Real) : Real :=
  dimensionOneDelayQPlus s - dimensionOneDelayQMinus s

noncomputable def dimensionOneDelayConjugateWeight (s : Real) : Real :=
  (s - 1) ^ 2 - 1 / 2

theorem dimensionOneDelayConjugateWeight_pos {s : Real} (hs : 2 <= s) :
    0 < dimensionOneDelayConjugateWeight s := by
  unfold dimensionOneDelayConjugateWeight
  nlinarith [sq_nonneg (s - 2)]

theorem dimensionOneDelayConjugateWeight_monoOn :
    MonotoneOn dimensionOneDelayConjugateWeight (Ici 1) := by
  intro x hx y hy hxy
  change 1 <= x at hx
  change 1 <= y at hy
  unfold dimensionOneDelayConjugateWeight
  have hxy' : 0 <= y - x := sub_nonneg.mpr hxy
  have hsum : 0 <= x + y - 2 := by linarith
  nlinarith [mul_nonneg hxy' hsum]

theorem dimensionOneDelayConjugateWeight_continuous :
    Continuous dimensionOneDelayConjugateWeight := by
  unfold dimensionOneDelayConjugateWeight
  exact ((continuous_id.sub continuous_const).pow 2).sub continuous_const

theorem dimensionOneDelayConjugateWeight_hasDerivAt (s : Real) :
    HasDerivAt dimensionOneDelayConjugateWeight (2 * (s - 1)) s := by
  unfold dimensionOneDelayConjugateWeight
  simp only [pow_two]
  change HasDerivAt (fun t : Real => (t - 1) * (t - 1) - 1 / 2)
    (2 * (s - 1)) s
  have hshift := (hasDerivAt_id s).sub_const 1
  have hraw := (hshift.mul hshift).sub_const (1 / 2)
  simp only [Pi.mul_apply, id_eq, one_mul, mul_one] at hraw
  apply hraw.congr_deriv
  ring

theorem dimensionOneDelayConjugateWeight_equation (s : Real) :
    HasDerivAt (fun t => t * dimensionOneDelayConjugateWeight t)
      (2 * dimensionOneDelayConjugateWeight s +
        dimensionOneDelayConjugateWeight (s + 1)) s := by
  change HasDerivAt (fun t : Real => t * ((t - 1) ^ 2 - 1 / 2))
    (2 * ((s - 1) ^ 2 - 1 / 2) + ((s + 1 - 1) ^ 2 - 1 / 2)) s
  have h := (hasDerivAt_id s).mul
    (dimensionOneDelayConjugateWeight_hasDerivAt s)
  simp only [id_eq, one_mul] at h
  apply h.congr_deriv
  unfold dimensionOneDelayConjugateWeight
  ring

theorem dimensionOneDelayQPlus_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt dimensionOneDelayQPlus
      ((-2 * dimensionOneDelayQPlus s -
        dimensionOneDelayQMinus (s - 1)) / s) s := by
  unfold dimensionOneDelayQPlus
  have h := (dimensionOneDelayScaledPlus_hasDerivAt hs).div
    (hasDerivAt_pow 2 s) (pow_ne_zero _ (by linarith))
  apply h.congr_deriv
  rw [<- sq_mul_dimensionOneDelayQPlus (by linarith : s ≠ 0)]
  field_simp
  ring

theorem dimensionOneDelayQMinus_hasDerivAt {s : Real} (hs : 2 < s) :
    HasDerivAt dimensionOneDelayQMinus
      ((-2 * dimensionOneDelayQMinus s -
        dimensionOneDelayQPlus (s - 1)) / s) s := by
  unfold dimensionOneDelayQMinus
  have h := (dimensionOneDelayScaledMinus_hasDerivAt hs).div
    (hasDerivAt_pow 2 s) (pow_ne_zero _ (by linarith))
  apply h.congr_deriv
  rw [<- sq_mul_dimensionOneDelayQMinus (by linarith : s ≠ 0)]
  field_simp
  ring

private theorem dimensionOneDelayScaledPlus_hasDerivAt_middle
    {s : Real} (hs : s < 3) :
    HasDerivAt dimensionOneDelayScaledPlus 0 s := by
  refine (hasDerivAt_const s (1 / 2 : Real)).congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hs] with t ht
  exact dimensionOneDelayScaledPlus_eq_half_of_le ht.le

theorem dimensionOneDelayQPlus_hasDerivAt_middle
    {s : Real} (hs0 : 0 < s) (hs3 : s < 3) :
    HasDerivAt dimensionOneDelayQPlus
      (-2 * dimensionOneDelayQPlus s / s) s := by
  unfold dimensionOneDelayQPlus
  have h := (dimensionOneDelayScaledPlus_hasDerivAt_middle hs3).div
    (hasDerivAt_pow 2 s) (pow_ne_zero _ hs0.ne')
  apply h.congr_deriv
  rw [<- sq_mul_dimensionOneDelayQPlus hs0.ne']
  field_simp
  ring

theorem dimensionOneDelayQPlus_shift_middle
    {s : Real} (hs2 : 2 <= s) (hs3 : s <= 3) :
    dimensionOneDelayQPlus (s - 1) = 1 / (2 * (s - 1) ^ 2) := by
  unfold dimensionOneDelayQPlus
  rw [dimensionOneDelayScaledPlus_eq_half_of_le (by linarith)]
  field_simp [show s - 1 ≠ 0 by linarith]

theorem dimensionOneDelaySum_continuousOn :
    ContinuousOn dimensionOneDelaySum (Ioi 0) :=
  dimensionOneDelayQPlus_continuousOn.add dimensionOneDelayQMinus_continuousOn

theorem dimensionOneDelayDifference_continuousOn :
    ContinuousOn dimensionOneDelayDifference (Ioi 0) :=
  dimensionOneDelayQPlus_continuousOn.sub dimensionOneDelayQMinus_continuousOn

theorem dimensionOneDelaySum_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt dimensionOneDelaySum
      ((-2 * dimensionOneDelaySum s - dimensionOneDelaySum (s - 1)) / s) s := by
  unfold dimensionOneDelaySum
  have h := (dimensionOneDelayQPlus_hasDerivAt hs).add
    (dimensionOneDelayQMinus_hasDerivAt (by linarith))
  apply h.congr_deriv
  ring

theorem dimensionOneDelayDifference_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt dimensionOneDelayDifference
      ((-2 * dimensionOneDelayDifference s +
        dimensionOneDelayDifference (s - 1)) / s) s := by
  unfold dimensionOneDelayDifference
  have h := (dimensionOneDelayQPlus_hasDerivAt hs).sub
    (dimensionOneDelayQMinus_hasDerivAt (by linarith))
  apply h.congr_deriv
  ring

theorem dimensionOneDelaySum_hasDerivAt_middle
    {s : Real} (hs2 : 2 < s) (hs3 : s < 3) :
    HasDerivAt dimensionOneDelaySum
      ((-2 * dimensionOneDelaySum s - dimensionOneDelayQPlus (s - 1)) / s) s := by
  unfold dimensionOneDelaySum
  have h := (dimensionOneDelayQPlus_hasDerivAt_middle (by linarith) hs3).add
    (dimensionOneDelayQMinus_hasDerivAt hs2)
  apply h.congr_deriv
  ring

theorem dimensionOneDelayDifference_hasDerivAt_middle
    {s : Real} (hs2 : 2 < s) (hs3 : s < 3) :
    HasDerivAt dimensionOneDelayDifference
      ((-2 * dimensionOneDelayDifference s +
        dimensionOneDelayQPlus (s - 1)) / s) s := by
  unfold dimensionOneDelayDifference
  have h := (dimensionOneDelayQPlus_hasDerivAt_middle (by linarith) hs3).sub
    (dimensionOneDelayQMinus_hasDerivAt hs2)
  apply h.congr_deriv
  ring

end PrimesRestrictedDigits
