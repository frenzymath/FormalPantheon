import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondWeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Restricted Eq. (8.10) for the second Rosser weight

This file integrates the negative derivative of the target-sign artificial auxiliary and
retains Iwaniec's exact `(1-1/s0)^(2/3)` coefficient.
-/

open MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

noncomputable def dimensionOneRosserSecondEndpointFactor (t : Real) : Real :=
  Real.exp ((2 / 3 : Real) * Real.log (1 - 1 / t))

theorem dimensionOneRosserSecondEndpointFactor_eq_rpow
    {t : Real} (ht : 1 < t) :
    dimensionOneRosserSecondEndpointFactor t =
      (1 - 1 / t) ^ (2 / 3 : Real) := by
  have ht0 : 0 < t := by linarith
  have hbase : 0 < 1 - 1 / t := by
    rw [sub_pos, div_lt_one ht0]
    exact ht
  unfold dimensionOneRosserSecondEndpointFactor
  rw [Real.rpow_def_of_pos hbase]
  congr 1
  ring

theorem dimensionOneRosserSecondEndpointFactor_pos (t : Real) :
    0 < dimensionOneRosserSecondEndpointFactor t := Real.exp_pos _

theorem dimensionOneRosserSecondEndpointFactor_monotoneOn :
    MonotoneOn dimensionOneRosserSecondEndpointFactor (Ioi 1) := by
  intro x hx y hy hxy
  change 1 < x at hx
  change 1 < y at hy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hbaseX : 0 < 1 - 1 / x := by
    rw [sub_pos, div_lt_one hx0]
    exact hx
  have hinv : 1 / y <= 1 / x := one_div_le_one_div_of_le hx0 hxy
  have hbase : 1 - 1 / x <= 1 - 1 / y := by linarith
  have hlog : Real.log (1 - 1 / x) <= Real.log (1 - 1 / y) :=
    Real.log_le_log hbaseX hbase
  unfold dimensionOneRosserSecondEndpointFactor
  rw [Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_left hlog (by norm_num)

private theorem secondKernel_div_eq_normalized
    {L t kernel scaled oppositeQ : Real} (hL : 0 < L) (ht : 1 < t)
    (hKernel : kernel =
      (1 - 1 / t) ^ (-4 / 3 : Real) *
        (1 + t ^ 50 / L) ^ (t - 1) * scaled)
    (hScaled : (t - 1) ^ 2 * oppositeQ = scaled) :
    kernel / t = dimensionOneRosserSecondEndpointFactor t *
      (dimensionOneRosserArtificialFactor L 0 t /
        dimensionOneRosserArtificialBase L 0 t * (t * oppositeQ)) := by
  have ht0 : 0 < t := by linarith
  have hbase : 0 < 1 - 1 / t := by
    rw [sub_pos, div_lt_one ht0]
    linarith
  have hB : 0 < 1 + t ^ 50 / L := by positivity
  rw [hKernel, dimensionOneRosserSecondEndpointFactor_eq_rpow
    (by linarith), dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  rw [<- hScaled]
  have hbasePower :
      (1 - 1 / t) ^ (-4 / 3 : Real) * (t - 1) ^ 2 / t =
        (1 - 1 / t) ^ (2 / 3 : Real) * t := by
    rw [show (t - 1) ^ 2 = (1 - 1 / t) ^ 2 * t ^ 2 by
      field_simp]
    have hp : (1 - 1 / t) ^ (-4 / 3 : Real) *
        (1 - 1 / t) ^ (2 : Real) =
          (1 - 1 / t) ^ (2 / 3 : Real) := by
      rw [<- Real.rpow_add hbase]
      congr 1
      norm_num
    rw [show (1 - 1 / t) ^ 2 =
      (1 - 1 / t) ^ (2 : Real) by
        exact (Real.rpow_natCast _ 2).symm]
    calc
      (1 - 1 / t) ^ (-4 / 3 : Real) *
          ((1 - 1 / t) ^ (2 : Real) * t ^ 2) / t =
          ((1 - 1 / t) ^ (-4 / 3 : Real) *
            (1 - 1 / t) ^ (2 : Real)) * (t ^ 2 / t) := by ring
      _ = (1 - 1 / t) ^ (2 / 3 : Real) * (t ^ 2 / t) := by
        rw [hp]
      _ = (1 - 1 / t) ^ (2 / 3 : Real) * t := by field_simp
  simp only [add_zero]
  rw [<- Real.rpow_sub_one hB.ne' t]
  calc
    (1 - 1 / t) ^ (-4 / 3 : Real) *
        (1 + t ^ 50 / L) ^ (t - 1) *
          ((t - 1) ^ 2 * oppositeQ) / t =
        ((1 - 1 / t) ^ (-4 / 3 : Real) * (t - 1) ^ 2 / t) *
          ((1 + t ^ 50 / L) ^ (t - 1) * oppositeQ) := by ring
    _ = ((1 - 1 / t) ^ (2 / 3 : Real) * t) *
          ((1 + t ^ 50 / L) ^ (t - 1) * oppositeQ) := by
      rw [hbasePower]
    _ = (1 - 1 / t) ^ (2 / 3 : Real) *
        ((1 + t ^ 50 / L) ^ (t - 1) * (t * oppositeQ)) := by ring

theorem dimensionOneRosserPlusSecondKernel_div_eq
    {L t : Real} (hL : 0 < L) (ht : 1 < t) :
    dimensionOneRosserPlusSecondKernel L t / t =
      dimensionOneRosserSecondEndpointFactor t *
        (dimensionOneRosserArtificialFactor L 0 t /
          dimensionOneRosserArtificialBase L 0 t *
            (t * dimensionOneDelayQMinus (t - 1))) := by
  apply secondKernel_div_eq_normalized hL ht
  · exact dimensionOneRosserPlusSecondKernel_eq_source hL (by linarith)
  · exact sq_mul_dimensionOneDelayQMinus (by linarith)

theorem dimensionOneRosserMinusSecondKernel_div_eq
    {L t : Real} (hL : 0 < L) (ht : 1 < t) :
    dimensionOneRosserMinusSecondKernel L t / t =
      dimensionOneRosserSecondEndpointFactor t *
        (dimensionOneRosserArtificialFactor L 0 t /
          dimensionOneRosserArtificialBase L 0 t *
            (t * dimensionOneDelayQPlus (t - 1))) := by
  apply secondKernel_div_eq_normalized hL ht
  · exact dimensionOneRosserMinusSecondKernel_eq_source hL (by linarith)
  · exact sq_mul_dimensionOneDelayQPlus (by linarith)

theorem dimensionOneRosserArtificialError_lt_of_margin
    {L t scaled currentQ oppositeQ : Real} (hL : 0 < L) (ht : 3 < t)
    (hCurrent : 0 < currentQ)
    (hCross : t * Real.log t * currentQ < 48 * oppositeQ)
    (hScaled : t ^ 2 * currentQ = scaled)
    (hMargin : 48 * dimensionOneRosserArtificialSlope L 0 t <=
      Real.log t *
        (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹)) :
    dimensionOneRosserArtificialSlope L 0 t * scaled <
      t * oppositeQ *
        (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹) := by
  have ht0 : 0 < t := by linarith
  have hbaseOne : 1 < dimensionOneRosserArtificialBase L 0 t := by
    unfold dimensionOneRosserArtificialBase
    have hpow : 0 < t ^ 50 := pow_pos ht0 _
    have hdiv : 0 < t ^ 50 / L := div_pos hpow hL
    norm_num at hdiv ⊢
    linarith
  have htheta :
      0 < 1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹ := by
    rw [sub_pos]
    exact (inv_lt_one₀ (dimensionOneRosserArtificialBase_pos hL)).2
      hbaseOne
  have hmul := mul_le_mul_of_nonneg_right hMargin
    (mul_nonneg ht0.le hCurrent.le)
  have hcrossMul := mul_lt_mul_of_pos_right hCross htheta
  have hcore : dimensionOneRosserArtificialSlope L 0 t * t * currentQ <
      oppositeQ *
        (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹) := by
    have h48 : 48 *
        (dimensionOneRosserArtificialSlope L 0 t * t * currentQ) <
      48 * (oppositeQ *
        (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹)) := by
      calc
        _ <= (t * Real.log t * currentQ) *
            (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹) := by
          nlinarith
        _ < _ := by nlinarith
    nlinarith
  rw [<- hScaled]
  have := mul_lt_mul_of_pos_left hcore ht0
  nlinarith

noncomputable def dimensionOneRosserPlusDerivativeMajorant
    (L t : Real) : Real :=
  dimensionOneRosserArtificialFactor L 0 t *
    (t * dimensionOneDelayQMinus (t - 1) -
      dimensionOneRosserArtificialSlope L 0 t *
        dimensionOneDelayScaledPlus t)

noncomputable def dimensionOneRosserMinusDerivativeMajorant
    (L t : Real) : Real :=
  dimensionOneRosserArtificialFactor L 0 t *
    (t * dimensionOneDelayQPlus (t - 1) -
      dimensionOneRosserArtificialSlope L 0 t *
        dimensionOneDelayScaledMinus t)

theorem dimensionOneRosserArtificialSlope_continuousOn
    {L epsilon a b : Real} (hL : 0 < L) :
    ContinuousOn (dimensionOneRosserArtificialSlope L epsilon) (Icc a b) := by
  have hbase : ContinuousOn
      (dimensionOneRosserArtificialBase L epsilon) (Icc a b) := by
    unfold dimensionOneRosserArtificialBase
    exact continuousOn_const.add
      (((continuousOn_id.add continuousOn_const).pow 50).div_const L)
  have hbase0 : ∀ t ∈ Icc a b,
      dimensionOneRosserArtificialBase L epsilon t ≠ 0 := by
    intro t ht
    exact (dimensionOneRosserArtificialBase_pos
      (epsilon := epsilon) (t := t) hL).ne'
  have hlog : ContinuousOn (fun t => Real.log
      (dimensionOneRosserArtificialBase L epsilon t)) (Icc a b) :=
    Real.continuousOn_log.comp hbase hbase0
  have hpow : ContinuousOn (fun t : Real =>
      50 * (t + epsilon) ^ 49 / L) (Icc a b) :=
    (continuousOn_const.mul
      ((continuousOn_id.add continuousOn_const).pow 49)).div_const L
  unfold dimensionOneRosserArtificialSlope
  exact hlog.add (continuousOn_id.mul (hbase.inv₀ hbase0 |>.mul hpow))

theorem dimensionOneRosserPlusDerivativeMajorant_continuousOn
    {L s s0 : Real} (hL : 0 < L) (hs : 4 <= s) :
    ContinuousOn (dimensionOneRosserPlusDerivativeMajorant L) (Icc s s0) := by
  have hQ : ContinuousOn (fun t : Real =>
      dimensionOneDelayQMinus (t - 1)) (Icc s s0) := by
    apply dimensionOneDelayQMinus_continuousOn.comp
      (continuousOn_id.sub continuousOn_const)
    intro t ht
    change 0 < t - 1
    linarith [hs, ht.1]
  unfold dimensionOneRosserPlusDerivativeMajorant
  exact (dimensionOneRosserArtificialFactor_continuous hL).continuousOn.mul
    ((continuousOn_id.mul hQ).sub
      ((dimensionOneRosserArtificialSlope_continuousOn hL).mul
        dimensionOneDelayScaledPlus_continuous.continuousOn))

theorem dimensionOneRosserMinusDerivativeMajorant_continuousOn
    {L s s0 : Real} (hL : 0 < L) (hs : 4 <= s) :
    ContinuousOn (dimensionOneRosserMinusDerivativeMajorant L) (Icc s s0) := by
  have hQ : ContinuousOn (fun t : Real =>
      dimensionOneDelayQPlus (t - 1)) (Icc s s0) := by
    apply dimensionOneDelayQPlus_continuousOn.comp
      (continuousOn_id.sub continuousOn_const)
    intro t ht
    change 0 < t - 1
    linarith [hs, ht.1]
  unfold dimensionOneRosserMinusDerivativeMajorant
  exact (dimensionOneRosserArtificialFactor_continuous hL).continuousOn.mul
    ((continuousOn_id.mul hQ).sub
      ((dimensionOneRosserArtificialSlope_continuousOn hL).mul
        dimensionOneDelayScaledMinus_continuous.continuousOn))

private theorem plusSecondKernel_pointwise_lt
    {L s s0 t : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) (ht : t ∈ Icc s s0) :
    dimensionOneRosserPlusSecondKernel L t / t <
      dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserPlusDerivativeMajorant L t := by
  have ht3 : 3 < t := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith [hs, ht.1]
  have hmargin := dimensionOneRosserArtificialSlope_zero_margin
    hL hs hss0 hcap ht
  have herror := dimensionOneRosserArtificialError_lt_of_margin hL ht3
    (dimensionOneDelayQPlus_pos (by linarith))
    (dimensionOneDelayQPlus_to_QMinus_log_shift_lt (by linarith))
    (sq_mul_dimensionOneDelayQPlus (by linarith))
    (by simpa [mul_comm] using hmargin)
  let core := dimensionOneRosserArtificialFactor L 0 t /
    dimensionOneRosserArtificialBase L 0 t *
      (t * dimensionOneDelayQMinus (t - 1))
  have hcorePos : 0 < core := by
    dsimp [core]
    exact mul_pos (div_pos (Real.exp_pos _)
      (dimensionOneRosserArtificialBase_pos hL))
      (mul_pos (by linarith)
        (dimensionOneDelayQMinus_pos (by linarith)))
  have hinner : t * dimensionOneDelayQMinus (t - 1) *
      (dimensionOneRosserArtificialBase L 0 t)⁻¹ <
      t * dimensionOneDelayQMinus (t - 1) -
        dimensionOneRosserArtificialSlope L 0 t *
          dimensionOneDelayScaledPlus t := by
    nlinarith [herror]
  have hcoreMajorant : core < dimensionOneRosserPlusDerivativeMajorant L t := by
    calc
      core = dimensionOneRosserArtificialFactor L 0 t *
          (t * dimensionOneDelayQMinus (t - 1) *
            (dimensionOneRosserArtificialBase L 0 t)⁻¹) := by
        dsimp [core]
        ring
      _ < dimensionOneRosserArtificialFactor L 0 t *
          (t * dimensionOneDelayQMinus (t - 1) -
            dimensionOneRosserArtificialSlope L 0 t *
              dimensionOneDelayScaledPlus t) :=
        mul_lt_mul_of_pos_left hinner (Real.exp_pos _)
      _ = dimensionOneRosserPlusDerivativeMajorant L t := rfl
  have hend : dimensionOneRosserSecondEndpointFactor t <=
      dimensionOneRosserSecondEndpointFactor s0 :=
    dimensionOneRosserSecondEndpointFactor_monotoneOn
      (by change 1 < t; linarith) (by
        change 1 < s0
        have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
        linarith [hs, hss0])
      ht.2
  rw [dimensionOneRosserPlusSecondKernel_div_eq hL (by linarith)]
  change dimensionOneRosserSecondEndpointFactor t * core < _
  exact (mul_le_mul_of_nonneg_right hend hcorePos.le).trans_lt
    (mul_lt_mul_of_pos_left hcoreMajorant
      (dimensionOneRosserSecondEndpointFactor_pos s0))

private theorem minusSecondKernel_pointwise_lt
    {L s s0 t : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) (ht : t ∈ Icc s s0) :
    dimensionOneRosserMinusSecondKernel L t / t <
      dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserMinusDerivativeMajorant L t := by
  have ht3 : 3 < t := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith [hs, ht.1]
  have hmargin := dimensionOneRosserArtificialSlope_zero_margin
    hL hs hss0 hcap ht
  have herror := dimensionOneRosserArtificialError_lt_of_margin hL ht3
    (dimensionOneDelayQMinus_pos (by linarith))
    (dimensionOneDelayQMinus_to_QPlus_log_shift_lt (by linarith))
    (sq_mul_dimensionOneDelayQMinus (by linarith))
    (by simpa [mul_comm] using hmargin)
  let core := dimensionOneRosserArtificialFactor L 0 t /
    dimensionOneRosserArtificialBase L 0 t *
      (t * dimensionOneDelayQPlus (t - 1))
  have hcorePos : 0 < core := by
    dsimp [core]
    exact mul_pos (div_pos (Real.exp_pos _)
      (dimensionOneRosserArtificialBase_pos hL))
      (mul_pos (by linarith)
        (dimensionOneDelayQPlus_pos (by linarith)))
  have hinner : t * dimensionOneDelayQPlus (t - 1) *
      (dimensionOneRosserArtificialBase L 0 t)⁻¹ <
      t * dimensionOneDelayQPlus (t - 1) -
        dimensionOneRosserArtificialSlope L 0 t *
          dimensionOneDelayScaledMinus t := by
    nlinarith [herror]
  have hcoreMajorant : core < dimensionOneRosserMinusDerivativeMajorant L t := by
    calc
      core = dimensionOneRosserArtificialFactor L 0 t *
          (t * dimensionOneDelayQPlus (t - 1) *
            (dimensionOneRosserArtificialBase L 0 t)⁻¹) := by
        dsimp [core]
        ring
      _ < dimensionOneRosserArtificialFactor L 0 t *
          (t * dimensionOneDelayQPlus (t - 1) -
            dimensionOneRosserArtificialSlope L 0 t *
              dimensionOneDelayScaledMinus t) :=
        mul_lt_mul_of_pos_left hinner (Real.exp_pos _)
      _ = dimensionOneRosserMinusDerivativeMajorant L t := rfl
  have hend : dimensionOneRosserSecondEndpointFactor t <=
      dimensionOneRosserSecondEndpointFactor s0 :=
    dimensionOneRosserSecondEndpointFactor_monotoneOn
      (by change 1 < t; linarith) (by
        change 1 < s0
        have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
        linarith [hs, hss0])
      ht.2
  rw [dimensionOneRosserMinusSecondKernel_div_eq hL (by linarith)]
  change dimensionOneRosserSecondEndpointFactor t * core < _
  exact (mul_le_mul_of_nonneg_right hend hcorePos.le).trans_lt
    (mul_lt_mul_of_pos_left hcoreMajorant
      (dimensionOneRosserSecondEndpointFactor_pos s0))

theorem dimensionOneRosserIntegralSecondKernelDivLt
    (kernel aux majorant : Real -> Real) {s s0 : Real}
    (hs : 4 <= s) (hss0 : s < s0)
    (hKernelCont : ContinuousOn kernel (Ioi 1))
    (hAuxCont : Continuous aux) (hAuxPos : 0 < aux s0)
    (hMajorantCont : ContinuousOn majorant (Icc s s0))
    (hDeriv : ∀ t ∈ Icc s s0, HasDerivAt aux (-majorant t) t)
    (hPoint : ∀ t ∈ Icc s s0,
      kernel t / t < dimensionOneRosserSecondEndpointFactor s0 *
        majorant t) :
    (∫ t in s..s0, kernel t / t) <
      dimensionOneRosserSecondEndpointFactor s0 * aux s := by
  have hfcont : ContinuousOn (fun t => kernel t / t) (Icc s s0) := by
    apply (hKernelCont.mono (fun t ht => by
      change 1 < t
      linarith [hs, ht.1])).div continuousOn_id
    intro t ht
    change t ≠ 0
    linarith [hs, ht.1]
  have hgcont : ContinuousOn (fun t =>
      dimensionOneRosserSecondEndpointFactor s0 * majorant t)
      (Icc s s0) := continuousOn_const.mul hMajorantCont
  have hintlt : (∫ t in s..s0, kernel t / t) <
      ∫ t in s..s0,
        dimensionOneRosserSecondEndpointFactor s0 * majorant t := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hss0 hfcont hgcont
    · intro t ht
      exact (hPoint t ⟨ht.1.le, ht.2⟩).le
    · exact ⟨s, left_mem_Icc.mpr hss0.le,
        hPoint s (left_mem_Icc.mpr hss0.le)⟩
  have hmajorantInt : (∫ t in s..s0, majorant t) =
      aux s - aux s0 := by
    have hnegFTC : (∫ t in s..s0, -majorant t) = aux s0 - aux s := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (f' := fun t => -majorant t) hss0.le hAuxCont.continuousOn
      · intro t ht
        exact hDeriv t ⟨ht.1.le, ht.2.le⟩
      exact hMajorantCont.neg.intervalIntegrable_of_Icc hss0.le
    rw [intervalIntegral.integral_neg] at hnegFTC
    linarith
  have hfactorPos : 0 < dimensionOneRosserSecondEndpointFactor s0 :=
    dimensionOneRosserSecondEndpointFactor_pos s0
  calc
    (∫ t in s..s0, kernel t / t) <
        ∫ t in s..s0,
          dimensionOneRosserSecondEndpointFactor s0 * majorant t := hintlt
    _ = dimensionOneRosserSecondEndpointFactor s0 *
        (aux s - aux s0) := by
      rw [intervalIntegral.integral_const_mul, hmajorantInt]
    _ < dimensionOneRosserSecondEndpointFactor s0 * aux s := by
      nlinarith

/-- Restricted large-`s` target-plus specialization of Iwaniec's Eq. (8.10). -/
theorem integral_dimensionOneRosserPlusSecondKernel_div_lt
    {L s s0 : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) :
    (∫ t in s..s0, dimensionOneRosserPlusSecondKernel L t / t) <
      (1 - 1 / s0) ^ (2 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledPlus s := by
  have hs4 : 4 <= s := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have h := dimensionOneRosserIntegralSecondKernelDivLt
    (dimensionOneRosserPlusSecondKernel L)
    (dimensionOneRosserPlusArtificialAux L 0)
    (dimensionOneRosserPlusDerivativeMajorant L) hs4 hss0
    (dimensionOneRosserPlusSecondKernel_continuousOn hL)
    (dimensionOneRosserPlusArtificialAux_continuous hL)
    (dimensionOneRosserPlusArtificialAux_pos hL (by linarith))
    (dimensionOneRosserPlusDerivativeMajorant_continuousOn hL hs4)
    (fun t ht => by
      have hderiv := dimensionOneRosserPlusArtificialAux_hasDerivAt
        (epsilon := (0 : Real)) (t := t) hL (by linarith [hs4, ht.1])
      apply hderiv.congr_deriv
      unfold dimensionOneRosserPlusDerivativeMajorant
      ring)
    (fun t ht => plusSecondKernel_pointwise_lt hL hs hss0 hcap ht)
  calc
    (∫ t in s..s0, dimensionOneRosserPlusSecondKernel L t / t) <
        dimensionOneRosserSecondEndpointFactor s0 *
          dimensionOneRosserPlusArtificialAux L 0 s := h
    _ = _ := by
      rw [dimensionOneRosserSecondEndpointFactor_eq_rpow (by linarith)]
      unfold dimensionOneRosserPlusArtificialAux
      rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
      unfold dimensionOneRosserArtificialBase
      ring_nf

/-- Restricted large-`s` target-minus specialization of Iwaniec's Eq. (8.10). -/
theorem integral_dimensionOneRosserMinusSecondKernel_div_lt
    {L s s0 : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) :
    (∫ t in s..s0, dimensionOneRosserMinusSecondKernel L t / t) <
      (1 - 1 / s0) ^ (2 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledMinus s := by
  have hs4 : 4 <= s := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have h := dimensionOneRosserIntegralSecondKernelDivLt
    (dimensionOneRosserMinusSecondKernel L)
    (dimensionOneRosserMinusArtificialAux L 0)
    (dimensionOneRosserMinusDerivativeMajorant L) hs4 hss0
    (dimensionOneRosserMinusSecondKernel_continuousOn hL)
    (dimensionOneRosserMinusArtificialAux_continuous hL)
    (dimensionOneRosserMinusArtificialAux_pos hL (by linarith))
    (dimensionOneRosserMinusDerivativeMajorant_continuousOn hL hs4)
    (fun t ht => by
      have hderiv := dimensionOneRosserMinusArtificialAux_hasDerivAt
        (epsilon := (0 : Real)) (t := t) hL (by linarith [hs4, ht.1])
      apply hderiv.congr_deriv
      unfold dimensionOneRosserMinusDerivativeMajorant
      ring)
    (fun t ht => minusSecondKernel_pointwise_lt hL hs hss0 hcap ht)
  calc
    (∫ t in s..s0, dimensionOneRosserMinusSecondKernel L t / t) <
        dimensionOneRosserSecondEndpointFactor s0 *
          dimensionOneRosserMinusArtificialAux L 0 s := h
    _ = _ := by
      rw [dimensionOneRosserSecondEndpointFactor_eq_rpow (by linarith)]
      unfold dimensionOneRosserMinusArtificialAux
      rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
      unfold dimensionOneRosserArtificialBase
      ring_nf

end PrimesRestrictedDigits
