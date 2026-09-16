import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelLimitRecurrences
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lower affine continuation of the dimension-one Rosser model

This separates Iwaniec's post-Lemma 18 lower continuation from the raw infinite-rank series
and derives the corrected first-strip identity. The signs printed in Eqs. (7.8)--(7.9) are
incompatible with the definitions at the endpoint two. See `IWANIEC-ROSSER-SIEVE-1980`,
printed pp. 195--196.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

/-- The sum of the two raw dimension-one model limits. -/
noncomputable def dimensionOneRosserModelRawSum (s : Real) : Real :=
  dimensionOneRosserModelPlusRaw s + dimensionOneRosserModelMinusRaw s

/-- Iwaniec's constant `A` at `kappa=1`, `beta=2`. -/
noncomputable def dimensionOneRosserModelPlusAffineConstant : Real :=
  dimensionOneRosserModelPlusRaw 2 + 2

/-- Iwaniec's constant `B` at `kappa=1`, `beta=2`. -/
noncomputable def dimensionOneRosserModelMinusAffineConstant : Real :=
  dimensionOneRosserModelMinusRaw 2 - 2

/-- The source's lower affine continuation, kept distinct from the raw lower
series. Nonpositive inputs receive a neutral totalized value. -/
noncomputable def dimensionOneRosserModelMinus (s : Real) : Real :=
  if s <= 0 then 0
  else if s < 2 then s + dimensionOneRosserModelMinusAffineConstant
  else dimensionOneRosserModelMinusRaw s

/-- The raw upper affine branch expressed using the source constant `A`. -/
theorem dimensionOneRosserModelPlusRaw_add_eq_affineConstant
    {s : Real} (hs1 : 1 < s) (hs3 : s <= 3) :
    dimensionOneRosserModelPlusRaw s + s =
      dimensionOneRosserModelPlusAffineConstant := by
  have hs := dimensionOneRosserModelPlusRaw_add_eq_at_three hs1 hs3
  have htwo := dimensionOneRosserModelPlusRaw_add_eq_at_three
    (s := (2 : Real)) (by norm_num) (by norm_num)
  unfold dimensionOneRosserModelPlusAffineConstant
  exact hs.trans htwo.symm

/-- The affine continuation agrees with the raw lower series from two onward. -/
theorem dimensionOneRosserModelMinus_eq_raw
    {s : Real} (hs : 2 <= s) :
    dimensionOneRosserModelMinus s = dimensionOneRosserModelMinusRaw s := by
  simp [dimensionOneRosserModelMinus, show Not (s <= 0) by linarith,
    show Not (s < 2) by linarith]

/-- The chosen totalization is zero outside the source's positive domain. -/
theorem dimensionOneRosserModelMinus_eq_zero_of_nonpos
    {s : Real} (hs : s <= 0) : dimensionOneRosserModelMinus s = 0 := by
  simp [dimensionOneRosserModelMinus, hs]

/-- The source affine equation, including its seam at two. -/
theorem dimensionOneRosserModelMinus_sub_eq_affineConstant
    {s : Real} (hs0 : 0 < s) (hs2 : s <= 2) :
    dimensionOneRosserModelMinus s - s =
      dimensionOneRosserModelMinusAffineConstant := by
  by_cases hs : s < 2
  · simp [dimensionOneRosserModelMinus, not_le_of_gt hs0, hs]
  · have hseam : s = 2 := by linarith
    subst s
    simp [dimensionOneRosserModelMinus,
      dimensionOneRosserModelMinusAffineConstant]

private theorem dimensionOneRosserModelMinusRaw_sub_eq_intervalIntegral
    {s : Real} (hs : 2 <= s) :
    dimensionOneRosserModelMinusRaw 2 -
        dimensionOneRosserModelMinusRaw s =
      ∫ t in (2 : Real)..s,
        dimensionOneRosserModelPlusRaw (t - 1) / (t - 1) := by
  rw [dimensionOneRosserModelMinusRaw_eq_integral_Ioi
      (s := (2 : Real)) (by norm_num),
    dimensionOneRosserModelMinusRaw_eq_integral_Ioi hs]
  exact intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_shifted_dimensionOneRosserModelPlusRaw
      (s := (2 : Real)) (by norm_num)) hs

private theorem shiftedPlus_intervalIntegral_eq
    {s : Real} (hs2 : 2 <= s) (hs3 : s <= 3) :
    (∫ t in (2 : Real)..s,
        dimensionOneRosserModelPlusRaw (t - 1) / (t - 1)) =
      ∫ t in (2 : Real)..s,
        dimensionOneRosserModelPlusAffineConstant / (t - 1) - 1 := by
  apply intervalIntegral.integral_congr_Ioo_of_le hs2
  intro t ht
  dsimp only
  have ht1 : 1 < t - 1 := by linarith [ht.1]
  have ht3 : t - 1 <= 3 := by linarith [ht.2, hs3]
  have hplus :=
    dimensionOneRosserModelPlusRaw_add_eq_affineConstant ht1 ht3
  have hne : Ne (t - 1) 0 := by linarith
  rw [show dimensionOneRosserModelPlusRaw (t - 1) =
      dimensionOneRosserModelPlusAffineConstant - (t - 1) by linarith]
  field_simp

private theorem const_div_intervalIntegrable
    {s : Real} (hs2 : 2 <= s) :
    IntervalIntegrable
      (fun t : Real => dimensionOneRosserModelPlusAffineConstant / (t - 1))
      volume 2 s := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hs2]
  intro t ht
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div continuousAt_const
    (continuousAt_id.sub continuousAt_const)
  change t - 1 ≠ 0
  linarith [ht.1]

private theorem shiftedAffine_intervalIntegral_eval
    {s : Real} (hs2 : 2 <= s) :
    (∫ t in (2 : Real)..s,
        dimensionOneRosserModelPlusAffineConstant / (t - 1) - 1) =
      dimensionOneRosserModelPlusAffineConstant *
          (∫ t in (2 : Real)..s, 1 / (t - 1)) - (s - 2) := by
  rw [intervalIntegral.integral_sub (const_div_intervalIntegrable hs2)
    (continuous_const.intervalIntegrable 2 s)]
  congr 1
  · simp [div_eq_mul_inv, intervalIntegral.integral_const_mul]
  · exact integral_one

/-- The independently derived correction of Iwaniec's printed Eq. (7.8) on
the dimension-one first strip. -/
theorem dimensionOneRosserModelRawSum_strip
    {s : Real} (hs2 : 2 <= s) (hs3 : s <= 3) :
    dimensionOneRosserModelRawSum s =
      dimensionOneRosserModelPlusAffineConstant +
        dimensionOneRosserModelMinusAffineConstant -
          dimensionOneRosserModelPlusAffineConstant *
            (∫ t in (2 : Real)..s, 1 / (t - 1)) := by
  have hplus := dimensionOneRosserModelPlusRaw_add_eq_affineConstant
    (by linarith) hs3
  have hminus := dimensionOneRosserModelMinusRaw_sub_eq_intervalIntegral hs2
  have hshift := shiftedPlus_intervalIntegral_eq hs2 hs3
  have heval := shiftedAffine_intervalIntegral_eval hs2
  rw [hshift, heval] at hminus
  unfold dimensionOneRosserModelRawSum
    dimensionOneRosserModelMinusAffineConstant
  linarith

end PrimesRestrictedDigits
