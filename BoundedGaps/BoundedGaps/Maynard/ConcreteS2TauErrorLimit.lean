import BoundedGaps.Maynard.ConcreteS2TauEnvelopeLimit

noncomputable section

/-!
# Vanishing of the normalized concrete S2 error

The arbitrary logarithmic power in the prime-level hypothesis absorbs the
tau, coefficient, and pre-sieve factors in the concrete signed S2 error.
-/

namespace BoundedGaps.Maynard

open Filter

private abbrev tauLogPower : ℕ :=
  (3 * Fintype.card BoundedGaps.engelsmaTuple) ^ 2

private abbrev coefficientLogPower : ℕ :=
  4 * (Fintype.card BoundedGaps.engelsmaTuple) ^ 2

private abbrev envelopeLogPower : ℕ := tauLogPower + coefficientLogPower

set_option maxRecDepth 3000 in
theorem tendsto_engelsmaMaynardS2TauErrorEnvelope_div_scale
    {theta delta C : ℝ} (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hC : 0 ≤ C) :
    Tendsto
      (fun N : ℕ =>
        engelsmaMaynardS2TauErrorEnvelope (theta / 2 - delta)
            ((engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ) C N /
          engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds 0) := by
  let alpha := theta / 2 - delta
  let K := engelsmaS2TauEnvelopeConstant alpha C
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have hK : 0 ≤ K := engelsmaS2TauEnvelopeConstant_nonneg halpha hC
  have hEnvelope := eventually_engelsmaMaynardS2TauErrorEnvelope_le_log_ratio
    htheta hthetaHalf hdelta hdeltaTheta hC
  have hScale := eventually_engelsmaMaynardScale_ge_nat_div_modulus_pow halpha
  have hScalePos := eventually_engelsmaMaynardScale_pos halpha
  have hW := eventually_engelsmaMaynardModulus_le_log_cube
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop 1)
  have hmajorant : Tendsto
      (fun N : ℕ => K / (Real.log (N : ℝ)) ^ 2) atTop (nhds 0) := by
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ((tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hlog).const_div_atTop K
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hmajorant
  filter_upwards [hEnvelope, hScale, hScalePos, hW, hlogN,
    eventually_ge_atTop 1] with N hEnvelope hScale hScalePos hW hlogN hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hWpos : 0 < (engelsmaMaynardModulus N : ℝ) := by
    exact_mod_cast primorial_pos (tripleLogCutoff (N - 1))
  have hLN : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlogN
  have hWpow : (engelsmaMaynardModulus N : ℝ) ^ 106 ≤
      (Real.log (N : ℝ)) ^ 318 := by
    calc
      (engelsmaMaynardModulus N : ℝ) ^ 106 ≤
          ((Real.log (N : ℝ)) ^ 3) ^ 106 :=
        pow_le_pow_left₀ hWpos.le hW 106
      _ = (Real.log (N : ℝ)) ^ 318 := by
        rw [← pow_mul]
  have hLowerPos : 0 < (N : ℝ) /
      (engelsmaMaynardModulus N : ℝ) ^ 106 := div_pos hNreal (pow_pos hWpos _)
  have hMajorNonneg : 0 ≤
      K * (N : ℝ) * (Real.log (N : ℝ)) ^ envelopeLogPower /
        (Real.log (N : ℝ)) ^ engelsmaS2TauHalfLogExponent := by positivity
  have hEnvelopeNonneg : 0 ≤
      engelsmaMaynardS2TauErrorEnvelope alpha
        ((engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ) C N := by
    unfold engelsmaMaynardS2TauErrorEnvelope
    apply mul_nonneg (sq_nonneg _)
    apply add_nonneg <;> apply Finset.sum_nonneg <;> intro h _ <;>
      unfold tauIndexedEndpointEnvelope <;> positivity
  rw [abs_of_nonneg (div_nonneg hEnvelopeNonneg hScalePos.le)]
  calc
    engelsmaMaynardS2TauErrorEnvelope alpha
          ((engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ) C N /
        engelsmaMaynardScale alpha N ≤
        (K * (N : ℝ) * (Real.log (N : ℝ)) ^ envelopeLogPower /
          (Real.log (N : ℝ)) ^ engelsmaS2TauHalfLogExponent) /
            engelsmaMaynardScale alpha N :=
      div_le_div_of_nonneg_right hEnvelope hScalePos.le
    _ ≤ (K * (N : ℝ) * (Real.log (N : ℝ)) ^ envelopeLogPower /
          (Real.log (N : ℝ)) ^ engelsmaS2TauHalfLogExponent) /
            ((N : ℝ) / (engelsmaMaynardModulus N : ℝ) ^ 106) := by
      apply div_le_div_of_nonneg_left hMajorNonneg hLowerPos hScale
    _ = K * (engelsmaMaynardModulus N : ℝ) ^ 106 *
          (Real.log (N : ℝ)) ^ envelopeLogPower /
            (Real.log (N : ℝ)) ^ engelsmaS2TauHalfLogExponent := by
      field_simp
    _ ≤ K * (Real.log (N : ℝ)) ^ 318 *
          (Real.log (N : ℝ)) ^ envelopeLogPower /
            (Real.log (N : ℝ)) ^ engelsmaS2TauHalfLogExponent := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hWpow hK)
          (pow_nonneg hLN.le _)
      · positivity
    _ = K / (Real.log (N : ℝ)) ^ 2 := by
      have hExp : engelsmaS2TauHalfLogExponent =
          318 + envelopeLogPower + 2 := by
        unfold engelsmaS2TauHalfLogExponent
        dsimp [envelopeLogPower, coefficientLogPower, tauLogPower]
        omega
      rw [hExp, pow_add, pow_add]
      field_simp
      rw [pow_add]
      rw [show (Real.log (N : ℝ)) ^ envelopeLogPower =
          (Real.log (N : ℝ)) ^ tauLogPower *
            (Real.log (N : ℝ)) ^ coefficientLogPower by
        dsimp [envelopeLogPower]
        rw [pow_add]]
      ring

theorem tendsto_engelsmaMaynardS2Error_zero_of_primeLevel
    {theta delta : ℝ} (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hlevel : hasPrimeLevel theta) :
    Tendsto
      (fun N : ℕ => engelsmaMaynardS2Error (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds 0) := by
  let A : ℝ := ((engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ)
  have hA : 0 < A := by
    dsimp [A, engelsmaS2TauHalfLogExponent]
    positivity
  have herror := exists_engelsmaMaynardS2Error_tau_envelope
    htheta.le hthetaHalf hdelta hlevel hA
  obtain ⟨C', X₀', hw', hbound⟩ := herror
  have henv := tendsto_engelsmaMaynardS2TauErrorEnvelope_div_scale
    htheta hthetaHalf hdelta hdeltaTheta hw'.1
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
  filter_upwards [hbound, eventually_engelsmaMaynardScale_pos
    (sub_pos.mpr hdeltaTheta)] with N hbound hscale
  rw [abs_div, abs_of_pos hscale]
  exact div_le_div_of_nonneg_right hbound hscale.le

end BoundedGaps.Maynard
