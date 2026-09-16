import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayShiftLower

/-!
# Artificial factors for the second dimension-one Rosser weight

This is the large-parameter calculus behind Iwaniec's Eq. (8.10). See
`IWANIEC-ROSSER-SIEVE-1980`, printed pp. 199--200.
-/

open Set

namespace PrimesRestrictedDigits

/-- The positive base in Iwaniec's artificial Section 8 factor. -/
noncomputable def dimensionOneRosserArtificialBase
    (L epsilon t : Real) : Real :=
  1 + (t + epsilon) ^ 50 / L

/-- Exponential-log presentation of the source real power. -/
noncomputable def dimensionOneRosserArtificialFactor
    (L epsilon t : Real) : Real :=
  Real.exp (t * Real.log (dimensionOneRosserArtificialBase L epsilon t))

/-- Logarithmic derivative of the artificial factor. -/
noncomputable def dimensionOneRosserArtificialSlope
    (L epsilon t : Real) : Real :=
  Real.log (dimensionOneRosserArtificialBase L epsilon t) +
    t * ((dimensionOneRosserArtificialBase L epsilon t)⁻¹ *
      (50 * (t + epsilon) ^ 49 / L))

/-- Target-plus artificial auxiliary `A_epsilon^+`. -/
noncomputable def dimensionOneRosserPlusArtificialAux
    (L epsilon t : Real) : Real :=
  dimensionOneRosserArtificialFactor L epsilon t *
    dimensionOneDelayScaledPlus t

/-- Target-minus artificial auxiliary `A_epsilon^-`. -/
noncomputable def dimensionOneRosserMinusArtificialAux
    (L epsilon t : Real) : Real :=
  dimensionOneRosserArtificialFactor L epsilon t *
    dimensionOneDelayScaledMinus t

theorem dimensionOneRosserArtificialBase_pos
    {L epsilon t : Real} (hL : 0 < L) :
    0 < dimensionOneRosserArtificialBase L epsilon t := by
  unfold dimensionOneRosserArtificialBase
  have hp : 0 <= (t + epsilon) ^ 50 := by positivity
  have hd : 0 <= (t + epsilon) ^ 50 / L := div_nonneg hp hL.le
  linarith

theorem dimensionOneRosserArtificialFactor_eq_rpow
    {L epsilon t : Real} (hL : 0 < L) :
    dimensionOneRosserArtificialFactor L epsilon t =
      dimensionOneRosserArtificialBase L epsilon t ^ t := by
  unfold dimensionOneRosserArtificialFactor
  rw [Real.rpow_def_of_pos
    (dimensionOneRosserArtificialBase_pos
      (epsilon := epsilon) (t := t) hL)]
  congr 1
  ring

theorem dimensionOneRosserArtificialBase_hasDerivAt
    {L epsilon t : Real} (_hL : L ≠ 0) :
    HasDerivAt (dimensionOneRosserArtificialBase L epsilon)
      (50 * (t + epsilon) ^ 49 / L) t := by
  have hpow := ((hasDerivAt_id t).add_const epsilon).pow 50
  simp only [ id_eq, Nat.cast_ofNat, Nat.reduceSub,
    mul_one] at hpow
  have h := (hpow.div_const L).const_add 1
  change HasDerivAt (fun x : Real => 1 + (x + epsilon) ^ 50 / L)
    (50 * (t + epsilon) ^ 49 / L) t at h
  exact h

theorem dimensionOneRosserArtificialFactor_hasDerivAt
    {L epsilon t : Real} (hL : 0 < L) :
    HasDerivAt (dimensionOneRosserArtificialFactor L epsilon)
      (dimensionOneRosserArtificialFactor L epsilon t *
        dimensionOneRosserArtificialSlope L epsilon t) t := by
  have hbase := dimensionOneRosserArtificialBase_hasDerivAt
    (epsilon := epsilon) (t := t) hL.ne'
  have hlog := (Real.hasDerivAt_log
    (dimensionOneRosserArtificialBase_pos
      (epsilon := epsilon) (t := t) hL).ne').comp t hbase
  have hexponent : HasDerivAt
      (fun x : Real => x * Real.log
        (dimensionOneRosserArtificialBase L epsilon x))
      (dimensionOneRosserArtificialSlope L epsilon t) t := by
    have hraw := (hasDerivAt_id t).mul hlog
    simp only [ Function.comp_apply, id_eq, one_mul] at hraw
    unfold dimensionOneRosserArtificialSlope
    exact hraw
  unfold dimensionOneRosserArtificialFactor
  exact (Real.hasDerivAt_exp
    (t * Real.log (dimensionOneRosserArtificialBase L epsilon t))).comp
      t hexponent

theorem dimensionOneRosserArtificialSlope_eq
    {L epsilon t : Real} (hL : 0 < L) :
    dimensionOneRosserArtificialSlope L epsilon t =
      Real.log (dimensionOneRosserArtificialBase L epsilon t) +
        50 * t * (t + epsilon) ^ 49 /
          (L * dimensionOneRosserArtificialBase L epsilon t) := by
  have hbase := (dimensionOneRosserArtificialBase_pos
    (epsilon := epsilon) (t := t) hL).ne'
  unfold dimensionOneRosserArtificialSlope
  field_simp

theorem dimensionOneRosserArtificialFactor_continuous
    {L epsilon : Real} (hL : 0 < L) :
    Continuous (dimensionOneRosserArtificialFactor L epsilon) := by
  apply continuous_iff_continuousAt.2
  intro t
  exact (dimensionOneRosserArtificialFactor_hasDerivAt
    (epsilon := epsilon) (t := t) hL).continuousAt

theorem dimensionOneRosserPlusArtificialAux_continuous
    {L epsilon : Real} (hL : 0 < L) :
    Continuous (dimensionOneRosserPlusArtificialAux L epsilon) := by
  unfold dimensionOneRosserPlusArtificialAux
  exact (dimensionOneRosserArtificialFactor_continuous hL).mul
    dimensionOneDelayScaledPlus_continuous

theorem dimensionOneRosserMinusArtificialAux_continuous
    {L epsilon : Real} (hL : 0 < L) :
    Continuous (dimensionOneRosserMinusArtificialAux L epsilon) := by
  unfold dimensionOneRosserMinusArtificialAux
  exact (dimensionOneRosserArtificialFactor_continuous hL).mul
    dimensionOneDelayScaledMinus_continuous

theorem dimensionOneRosserPlusArtificialAux_pos
    {L epsilon t : Real} (_hL : 0 < L) (ht : 0 < t) :
    0 < dimensionOneRosserPlusArtificialAux L epsilon t := by
  unfold dimensionOneRosserPlusArtificialAux
  have hscaled : 0 < dimensionOneDelayScaledPlus t := by
    rw [<- sq_mul_dimensionOneDelayQPlus ht.ne']
    exact mul_pos (sq_pos_of_pos ht) (dimensionOneDelayQPlus_pos ht)
  exact mul_pos (Real.exp_pos _) hscaled

theorem dimensionOneRosserMinusArtificialAux_pos
    {L epsilon t : Real} (_hL : 0 < L) (ht : 0 < t) :
    0 < dimensionOneRosserMinusArtificialAux L epsilon t := by
  unfold dimensionOneRosserMinusArtificialAux
  have hscaled : 0 < dimensionOneDelayScaledMinus t := by
    rw [<- sq_mul_dimensionOneDelayQMinus ht.ne']
    exact mul_pos (sq_pos_of_pos ht) (dimensionOneDelayQMinus_pos ht)
  exact mul_pos (Real.exp_pos _) hscaled

theorem dimensionOneRosserPlusArtificialAux_hasDerivAt
    {L epsilon t : Real} (hL : 0 < L) (ht : 3 < t) :
    HasDerivAt (dimensionOneRosserPlusArtificialAux L epsilon)
      (dimensionOneRosserArtificialFactor L epsilon t *
        (dimensionOneRosserArtificialSlope L epsilon t *
            dimensionOneDelayScaledPlus t -
          t * dimensionOneDelayQMinus (t - 1))) t := by
  unfold dimensionOneRosserPlusArtificialAux
  have h := (dimensionOneRosserArtificialFactor_hasDerivAt
    (epsilon := epsilon) (t := t) hL).mul
      (dimensionOneDelayScaledPlus_hasDerivAt ht)
  apply h.congr_deriv
  ring

theorem dimensionOneRosserMinusArtificialAux_hasDerivAt
    {L epsilon t : Real} (hL : 0 < L) (ht : 2 < t) :
    HasDerivAt (dimensionOneRosserMinusArtificialAux L epsilon)
      (dimensionOneRosserArtificialFactor L epsilon t *
        (dimensionOneRosserArtificialSlope L epsilon t *
            dimensionOneDelayScaledMinus t -
          t * dimensionOneDelayQPlus (t - 1))) t := by
  unfold dimensionOneRosserMinusArtificialAux
  have h := (dimensionOneRosserArtificialFactor_hasDerivAt
    (epsilon := epsilon) (t := t) hL).mul
      (dimensionOneDelayScaledMinus_hasDerivAt ht)
  apply h.congr_deriv
  ring

theorem dimensionOneRosserPlusArtificial_derivCore_neg_of_slope
    {L epsilon t : Real} (ht : 3 < t)
    (hSlope : 48 * dimensionOneRosserArtificialSlope L epsilon t <=
      Real.log t) :
    dimensionOneRosserArtificialSlope L epsilon t *
        dimensionOneDelayScaledPlus t -
      t * dimensionOneDelayQMinus (t - 1) < 0 := by
  have ht0 : 0 < t := by linarith
  have hQ : 0 < dimensionOneDelayQPlus t :=
    dimensionOneDelayQPlus_pos ht0
  have hmul := mul_le_mul_of_nonneg_right hSlope
    (mul_nonneg ht0.le hQ.le)
  have hcross := dimensionOneDelayQPlus_to_QMinus_log_shift_lt
    (s := t) (by linarith)
  have hscaled := sq_mul_dimensionOneDelayQPlus ht0.ne'
  have hcore : dimensionOneRosserArtificialSlope L epsilon t * t *
      dimensionOneDelayQPlus t < dimensionOneDelayQMinus (t - 1) := by
    have h48 : 48 * (dimensionOneRosserArtificialSlope L epsilon t * t *
        dimensionOneDelayQPlus t) <
        48 * dimensionOneDelayQMinus (t - 1) := by
      calc
        _ <= t * Real.log t * dimensionOneDelayQPlus t := by
          nlinarith
        _ < _ := hcross
    nlinarith
  rw [<- hscaled]
  nlinarith

theorem dimensionOneRosserMinusArtificial_derivCore_neg_of_slope
    {L epsilon t : Real} (ht : 2 < t)
    (hSlope : 48 * dimensionOneRosserArtificialSlope L epsilon t <=
      Real.log t) :
    dimensionOneRosserArtificialSlope L epsilon t *
        dimensionOneDelayScaledMinus t -
      t * dimensionOneDelayQPlus (t - 1) < 0 := by
  have ht0 : 0 < t := by linarith
  have hQ : 0 < dimensionOneDelayQMinus t :=
    dimensionOneDelayQMinus_pos ht0
  have hmul := mul_le_mul_of_nonneg_right hSlope
    (mul_nonneg ht0.le hQ.le)
  have hcross := dimensionOneDelayQMinus_to_QPlus_log_shift_lt
    (s := t) (by linarith)
  have hscaled := sq_mul_dimensionOneDelayQMinus ht0.ne'
  have hcore : dimensionOneRosserArtificialSlope L epsilon t * t *
      dimensionOneDelayQMinus t < dimensionOneDelayQPlus (t - 1) := by
    have h48 : 48 * (dimensionOneRosserArtificialSlope L epsilon t * t *
        dimensionOneDelayQMinus t) <
        48 * dimensionOneDelayQPlus (t - 1) := by
      calc
        _ <= t * Real.log t * dimensionOneDelayQMinus t := by
          nlinarith
        _ < _ := hcross
    nlinarith
  rw [<- hscaled]
  nlinarith

end PrimesRestrictedDigits
