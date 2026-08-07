import BoundedGaps.Maynard.ConcreteS2TauAsymptotics

noncomputable section

/-!
# A vanishing logarithmic majorant for the concrete S2 tau envelope

This module collects the fixed-shift endpoint estimates and reduces the
normalized concrete tau envelope to two spare powers of `log N`.
-/

namespace BoundedGaps.Maynard

open Filter

private abbrev engelsmaCard : ℕ := Fintype.card BoundedGaps.engelsmaTuple

private abbrev tauLogPower : ℕ := (3 * engelsmaCard) ^ 2

private abbrev coefficientLogPower : ℕ := 4 * engelsmaCard ^ 2

private abbrev envelopeLogPower : ℕ := tauLogPower + coefficientLogPower

noncomputable def engelsmaS2TauEnvelopeConstant (alpha C : ℝ) : ℝ :=
  smallKCandidateBound ^ 2 * (1 + alpha) ^ coefficientLogPower *
    ((2 * engelsmaCard : ℕ) *
      ((engelsmaCard : ℝ) * (3 * (C + 1)) * 3 *
        4 ^ tauLogPower * 2 ^ engelsmaS2TauHalfLogExponent))

theorem engelsmaS2TauEnvelopeConstant_nonneg
    {alpha C : ℝ} (halpha : 0 < alpha) (hC : 0 ≤ C) :
    0 ≤ engelsmaS2TauEnvelopeConstant alpha C := by
  unfold engelsmaS2TauEnvelopeConstant
  positivity

set_option maxRecDepth 3000 in
theorem eventually_engelsmaMaynardS2TauErrorEnvelope_le_log_ratio
    {theta delta C : ℝ} (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaMaynardS2TauErrorEnvelope (theta / 2 - delta)
          ((engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ) C N ≤
        engelsmaS2TauEnvelopeConstant (theta / 2 - delta) C * (N : ℝ) *
          (Real.log (N : ℝ)) ^ envelopeLogPower /
            (Real.log (N : ℝ)) ^ engelsmaS2TauHalfLogExponent := by
  let alpha := theta / 2 - delta
  let B := engelsmaS2TauHalfLogExponent
  let Q := fun N => engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
    engelsmaMaynardRadius alpha N
  let E : ℝ := (engelsmaCard : ℝ) * (3 * (C + 1)) * 3 *
    4 ^ tauLogPower * 2 ^ B
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have htheta0 : 0 ≤ theta := htheta.le
  have hthetaOne : theta ≤ 1 := by linarith
  have hcut := eventually_engelsmaMaynardS2_endpoint_cutoffs htheta0 hdelta
  have hlogR := eventually_one_add_log_engelsmaMaynardRadius_le halpha
  have hlogN : ∀ᶠ N : ℕ in atTop,
      max 2 (2 * Real.log 2) ≤ Real.log (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop (max 2 (2 * Real.log 2)))
  have hRpos : ∀ᶠ N : ℕ in atTop, 1 ≤ engelsmaMaynardRadius alpha N := by
    filter_upwards [eventually_ge_atTop 3] with N hN
    unfold engelsmaMaynardRadius maynardDivisorCutoff
    apply Nat.le_floor
    have hreal := maynardRealCutoff_gt_one
      (alpha := alpha) (N := N - 1) (show 1 < N - 1 by omega) halpha
    unfold maynardRealCutoff at hreal
    simpa only [Nat.cast_one] using hreal.le
  filter_upwards [hcut, hlogR, hlogN, hRpos, eventually_ge_atTop 600] with
      N hcut hlogR hlogN hRpos hN
  have hLN : 2 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hlogN
  have hLNpos : 0 < Real.log (N : ℝ) := by linarith
  have hQpos : 1 ≤ Q N := by
    dsimp [Q]
    have hW : 1 ≤ engelsmaMaynardModulus N := (primorial_pos _)
    exact one_le_mul (one_le_mul hW hRpos) hRpos
  have hlogQnonneg : 0 ≤ 1 + Real.log (Q N) := by
    have hQreal : (1 : ℝ) ≤ (Q N : ℝ) := by exact_mod_cast hQpos
    linarith [Real.log_nonneg hQreal]
  have hendpoint (h : BoundedGaps.engelsmaTuple) (x : ℕ)
      (hcutx : Q N ≤ modulusCutoff theta x)
      (hxLower : N - 1 ≤ x) (hxUpper : x + 1 ≤ 3 * N) :
      tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple (Q N) C
          ((B * 2 : ℕ) : ℝ) x ≤
        E * (N : ℝ) * (Real.log (N : ℝ)) ^ tauLogPower /
          (Real.log (N : ℝ)) ^ B := by
    have hxOne : 1 ≤ x := by omega
    have hQx : Q N ≤ x := hcutx.trans (modulusCutoff_le_self hxOne hthetaOne)
    have hxcast : ((x + 1 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast hxUpper
    have hhalfCast : (N : ℝ) / 2 ≤ (x : ℝ) := by
      have hxcast' : ((N - 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxLower
      have hNcast : (N : ℝ) / 2 ≤ ((N - 1 : ℕ) : ℝ) := by
        have hcast : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
          exact_mod_cast (show N ≤ 2 * (N - 1) by omega)
        linarith
      exact hNcast.trans hxcast'
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
    have hNpos : (0 : ℝ) < N := by positivity
    have hlogHalf : Real.log (N : ℝ) / 2 ≤ Real.log ((N : ℝ) / 2) := by
      rw [Real.log_div hNpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
      have hlog2 := (le_max_right 2 (2 * Real.log 2)).trans hlogN
      linarith
    have hlogx : Real.log (N : ℝ) / 2 ≤ Real.log (x : ℝ) :=
      hlogHalf.trans (Real.log_le_log (by positivity) hhalfCast)
    have hQle : (Q N : ℝ) ≤ 3 * (N : ℝ) := by
      have hQleNat : Q N ≤ 3 * N := by omega
      exact_mod_cast hQleNat
    have hlogQle : Real.log (Q N) ≤ Real.log (3 * (N : ℝ)) := by
      exact Real.log_le_log (by exact_mod_cast (show 0 < Q N by omega)) hQle
    have hlog3 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      norm_num at h
      exact h
    have hlogQBound : 1 + Real.log (Q N) ≤ 4 * Real.log (N : ℝ) := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hNpos.ne'] at hlogQle
      nlinarith
    simpa [E, B, tauLogPower] using
      tauIndexedEndpointEnvelope_le_nat_log_ratio
        (H := BoundedGaps.engelsmaTuple) (Q := Q N) (x := x)
        (N := N) (B := B) hC hLN hxcast hlogx hlogQnonneg hlogQBound
  have hupper : ∀ h : BoundedGaps.engelsmaTuple,
      tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple (Q N) C
          ((B * 2 : ℕ) : ℝ) (2 * N + h.1 - 1) ≤
        E * (N : ℝ) * (Real.log (N : ℝ)) ^ tauLogPower /
          (Real.log (N : ℝ)) ^ B := by
    intro h
    apply hendpoint h
    · exact (hcut h).2
    · omega
    · have hh := BoundedGaps.engelsmaTuple_le_six_hundred h.2
      omega
  have hlower : ∀ h : BoundedGaps.engelsmaTuple,
      tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple (Q N) C
          ((B * 2 : ℕ) : ℝ) (N + h.1 - 1) ≤
        E * (N : ℝ) * (Real.log (N : ℝ)) ^ tauLogPower /
          (Real.log (N : ℝ)) ^ B := by
    intro h
    apply hendpoint h
    · exact (hcut h).1
    · omega
    · have hh := BoundedGaps.engelsmaTuple_le_six_hundred h.2
      omega
  have hsumUpper :
      (∑ h : BoundedGaps.engelsmaTuple,
        tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple (Q N) C
          ((B * 2 : ℕ) : ℝ) (2 * N + h.1 - 1)) ≤
        ∑ _h : BoundedGaps.engelsmaTuple,
          E * (N : ℝ) * (Real.log (N : ℝ)) ^ tauLogPower /
            (Real.log (N : ℝ)) ^ B := by
    apply Finset.sum_le_sum
    intro h _
    exact hupper h
  have hsumLower :
      (∑ h : BoundedGaps.engelsmaTuple,
        tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple (Q N) C
          ((B * 2 : ℕ) : ℝ) (N + h.1 - 1)) ≤
        ∑ _h : BoundedGaps.engelsmaTuple,
          E * (N : ℝ) * (Real.log (N : ℝ)) ^ tauLogPower /
            (Real.log (N : ℝ)) ^ B := by
    apply Finset.sum_le_sum
    intro h _
    exact hlower h
  have hsum :
      (∑ h : BoundedGaps.engelsmaTuple,
          tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple (Q N) C
            ((B * 2 : ℕ) : ℝ) (2 * N + h.1 - 1)) +
        ∑ h : BoundedGaps.engelsmaTuple,
          tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple (Q N) C
            ((B * 2 : ℕ) : ℝ) (N + h.1 - 1) ≤
        (2 * engelsmaCard : ℕ) *
          (E * (N : ℝ) * (Real.log (N : ℝ)) ^ tauLogPower /
            (Real.log (N : ℝ)) ^ B) := by
    calc
      _ ≤ (engelsmaCard : ℝ) *
            (E * (N : ℝ) * (Real.log (N : ℝ)) ^ tauLogPower /
              (Real.log (N : ℝ)) ^ B) +
          (engelsmaCard : ℝ) *
            (E * (N : ℝ) * (Real.log (N : ℝ)) ^ tauLogPower /
              (Real.log (N : ℝ)) ^ B) := by
        simpa [Finset.sum_const, nsmul_eq_mul] using
          add_le_add hsumUpper hsumLower
      _ = (2 * engelsmaCard : ℕ) *
          (E * (N : ℝ) * (Real.log (N : ℝ)) ^ tauLogPower /
            (Real.log (N : ℝ)) ^ B) := by
        push_cast
        ring
  have hLRnonneg : 0 ≤ 1 + Real.log (engelsmaMaynardRadius alpha N) := by
    have hRreal : (1 : ℝ) ≤ engelsmaMaynardRadius alpha N := by
      exact_mod_cast hRpos
    linarith [Real.log_nonneg hRreal]
  have hCoeffPow :
      (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ coefficientLogPower ≤
        ((1 + alpha) * Real.log (N : ℝ)) ^ coefficientLogPower :=
    pow_le_pow_left₀ hLRnonneg hlogR coefficientLogPower
  have hCoeff :
      (engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 ≤
        smallKCandidateBound ^ 2 *
          ((1 + alpha) * Real.log (N : ℝ)) ^ coefficientLogPower := by
    unfold engelsmaMaynardSharpCoefficientEnvelope
    calc
      (smallKCandidateBound *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
            (2 * engelsmaCard ^ 2)) ^ 2 =
          smallKCandidateBound ^ 2 *
            (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
              coefficientLogPower := by
        rw [mul_pow, ← pow_mul]
        congr 2
      _ ≤ smallKCandidateBound ^ 2 *
          ((1 + alpha) * Real.log (N : ℝ)) ^ coefficientLogPower :=
        mul_le_mul_of_nonneg_left hCoeffPow (sq_nonneg _)
  have hTauSumNonneg : 0 ≤
      (∑ h : BoundedGaps.engelsmaTuple,
          tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple (Q N) C
            ((B * 2 : ℕ) : ℝ) (2 * N + h.1 - 1)) +
        ∑ h : BoundedGaps.engelsmaTuple,
          tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple (Q N) C
            ((B * 2 : ℕ) : ℝ) (N + h.1 - 1) := by
    apply add_nonneg <;> apply Finset.sum_nonneg <;> intro h _ <;>
      unfold tauIndexedEndpointEnvelope <;> positivity
  have hlogPower :
      (Real.log (N : ℝ)) ^ coefficientLogPower *
          (Real.log (N : ℝ)) ^ tauLogPower =
        (Real.log (N : ℝ)) ^ envelopeLogPower := by
    dsimp [envelopeLogPower]
    rw [pow_add]
    ring
  unfold engelsmaMaynardS2TauErrorEnvelope
  change (engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 * _ ≤ _
  calc
    (engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 * _ ≤
        (smallKCandidateBound ^ 2 *
          ((1 + alpha) * Real.log (N : ℝ)) ^ coefficientLogPower) *
          ((2 * engelsmaCard : ℕ) *
            (E * (N : ℝ) * (Real.log (N : ℝ)) ^ tauLogPower /
              (Real.log (N : ℝ)) ^ B)) :=
      mul_le_mul hCoeff hsum hTauSumNonneg (by positivity)
    _ = engelsmaS2TauEnvelopeConstant alpha C * (N : ℝ) *
          (Real.log (N : ℝ)) ^ envelopeLogPower /
            (Real.log (N : ℝ)) ^ engelsmaS2TauHalfLogExponent := by
      rw [← hlogPower]
      dsimp [engelsmaS2TauEnvelopeConstant, E, B, envelopeLogPower,
        coefficientLogPower, tauLogPower]
      rw [mul_pow]
      ring

end BoundedGaps.Maynard
