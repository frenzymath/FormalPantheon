import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondIntegral

/-!
# Cap-free source high-range second-weight integrals

This file separates the high-coordinate Eq. (8.10) calculus from the older `s0^50 <= L`
sufficient margin.
-/

open MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private theorem plusSecondKernel_pointwise_lt_of_margin
    {L s s0 t : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hMargin : ∀ u ∈ Icc s s0,
      48 * dimensionOneRosserArtificialSlope L 0 u <=
        (1 - (dimensionOneRosserArtificialBase L 0 u)⁻¹) * Real.log u)
    (ht : t ∈ Icc s s0) :
    dimensionOneRosserPlusSecondKernel L t / t <
      dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserPlusDerivativeMajorant L t := by
  have ht3 : 3 < t := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith [hs, ht.1]
  have herror := dimensionOneRosserArtificialError_lt_of_margin hL ht3
    (dimensionOneDelayQPlus_pos (by linarith))
    (dimensionOneDelayQPlus_to_QMinus_log_shift_lt (by linarith))
    (sq_mul_dimensionOneDelayQPlus (by linarith))
    (by simpa [mul_comm] using hMargin t ht)
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
  have hcoreMajorant : core <
      dimensionOneRosserPlusDerivativeMajorant L t := by
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
      (by change 1 < t; linarith)
      (by
        change 1 < s0
        have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
        linarith [hs, hss0]) ht.2
  rw [dimensionOneRosserPlusSecondKernel_div_eq hL (by linarith)]
  change dimensionOneRosserSecondEndpointFactor t * core < _
  exact (mul_le_mul_of_nonneg_right hend hcorePos.le).trans_lt
    (mul_lt_mul_of_pos_left hcoreMajorant
      (dimensionOneRosserSecondEndpointFactor_pos s0))

private theorem minusSecondKernel_pointwise_lt_of_margin
    {L s s0 t : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hMargin : ∀ u ∈ Icc s s0,
      48 * dimensionOneRosserArtificialSlope L 0 u <=
        (1 - (dimensionOneRosserArtificialBase L 0 u)⁻¹) * Real.log u)
    (ht : t ∈ Icc s s0) :
    dimensionOneRosserMinusSecondKernel L t / t <
      dimensionOneRosserSecondEndpointFactor s0 *
        dimensionOneRosserMinusDerivativeMajorant L t := by
  have ht3 : 3 < t := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith [hs, ht.1]
  have herror := dimensionOneRosserArtificialError_lt_of_margin hL ht3
    (dimensionOneDelayQMinus_pos (by linarith))
    (dimensionOneDelayQMinus_to_QPlus_log_shift_lt (by linarith))
    (sq_mul_dimensionOneDelayQMinus (by linarith))
    (by simpa [mul_comm] using hMargin t ht)
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
  have hcoreMajorant : core <
      dimensionOneRosserMinusDerivativeMajorant L t := by
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
      (by change 1 < t; linarith)
      (by
        change 1 < s0
        have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
        linarith [hs, hss0]) ht.2
  rw [dimensionOneRosserMinusSecondKernel_div_eq hL (by linarith)]
  change dimensionOneRosserSecondEndpointFactor t * core < _
  exact (mul_le_mul_of_nonneg_right hend hcorePos.le).trans_lt
    (mul_lt_mul_of_pos_left hcoreMajorant
      (dimensionOneRosserSecondEndpointFactor_pos s0))

theorem integral_dimensionOneRosserPlusSecondKernel_div_lt_of_margin
    {L s s0 : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hMargin : ∀ t ∈ Icc s s0,
      48 * dimensionOneRosserArtificialSlope L 0 t <=
        (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹) * Real.log t) :
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
    (fun t ht => plusSecondKernel_pointwise_lt_of_margin hL hs hss0
      hMargin ht)
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

theorem integral_dimensionOneRosserMinusSecondKernel_div_lt_of_margin
    {L s s0 : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hMargin : ∀ t ∈ Icc s s0,
      48 * dimensionOneRosserArtificialSlope L 0 t <=
        (1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹) * Real.log t) :
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
    (fun t ht => minusSecondKernel_pointwise_lt_of_margin hL hs hss0
      hMargin ht)
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
