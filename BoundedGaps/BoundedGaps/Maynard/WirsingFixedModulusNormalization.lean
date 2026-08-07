import BoundedGaps.Maynard.ReciprocalTotientCorrectionEndpoint
import BoundedGaps.Maynard.CoprimeHarmonicErrorBound

noncomputable section

/-!
# Fixed-modulus normalization for the squarefree reciprocal-totient mean

This identifies the normalization constant left undetermined by the finite
Volterra balance.  It is pointwise in a fixed squarefree modulus and does not
provide the uniform varying-modulus error required by GGPY2009, Lemma
`L:Wirsing` (source lines 803--842).
-/

namespace BoundedGaps.Maynard

open Filter Real

theorem tendsto_squarefreeCoprimeInvTotientMean_div_log
    {W : ℕ} (hW : 0 < W) (hSq : Squarefree W) :
    Tendsto (fun Q : ℕ =>
      squarefreeCoprimeInvTotientMean W Q / Real.log Q)
      atTop (nhds (coprimeHarmonicDensity W)) := by
  let Ccorr : ℝ := 2 * (Real.exp 16 +
    4 * reciprocalTotientCorrectionQuarterConstant)
  let Charm : ℝ := Real.log 2 *
    ∑ d ∈ W.divisors, (1 : ℝ) / d
  have hlog : Tendsto (fun Q : ℕ => Real.log Q) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogPos : ∀ᶠ Q : ℕ in atTop, 0 < Real.log Q :=
    hlog.eventually (eventually_gt_atTop 0)
  have hCorrEnvelope :
      Tendsto (fun _Q : ℕ => Ccorr / Real.log _Q)
        atTop (nhds 0) := hlog.const_div_atTop Ccorr
  have hCorr : Tendsto (fun Q : ℕ =>
      (squarefreeCoprimeInvTotientMean W Q -
        coprimeHarmonicSum W Q) / Real.log Q)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun Q => abs_nonneg _) ?_
      hCorrEnvelope
    filter_upwards [hlogPos] with Q hQlog
    rw [abs_div, abs_of_pos hQlog]
    exact div_le_div_of_nonneg_right
      (abs_squarefreeCoprimeInvTotientMean_sub_coprimeHarmonicSum_le W Q)
      hQlog.le
  have hFirst : Tendsto (fun Q : ℕ =>
      2 * (W.divisors.card : ℝ) / Q) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop
      (2 * (W.divisors.card : ℝ))
  have hHarmEnvelope : Tendsto (fun Q : ℕ =>
      (2 * (W.divisors.card : ℝ) / Q + Charm) / Real.log Q)
      atTop (nhds 0) := by
    exact (hFirst.add_const Charm).div_atTop hlog
  have hHarmError : Tendsto (fun Q : ℕ =>
      (coprimeHarmonicSum W Q -
        coprimeHarmonicMainTerm W Q) / Real.log Q)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun Q => abs_nonneg _) ?_
      hHarmEnvelope
    filter_upwards [eventually_ge_atTop W, hlogPos] with Q hWQ hQlog
    rw [abs_div, abs_of_pos hQlog]
    exact div_le_div_of_nonneg_right
      (by simpa [coprimeHarmonicError, Charm] using
        abs_coprimeHarmonicError_le_divisor_envelope hW hSq hWQ)
      hQlog.le
  let B : ℝ := Real.eulerMascheroniConstant +
    primeLogPredecessorDivisorMass W
  have hB : Tendsto (fun Q : ℕ => B / Real.log Q)
      atTop (nhds 0) := hlog.const_div_atTop B
  have hMainModel : Tendsto (fun Q : ℕ =>
      coprimeHarmonicDensity W * (1 + B / Real.log Q))
      atTop (nhds (coprimeHarmonicDensity W)) := by
    have hDensity : Tendsto (fun _Q : ℕ => coprimeHarmonicDensity W)
        atTop (nhds (coprimeHarmonicDensity W)) := tendsto_const_nhds
    have hOne : Tendsto (fun _Q : ℕ => (1 : ℝ))
        atTop (nhds (1 : ℝ)) := tendsto_const_nhds
    simpa using hDensity.mul (hOne.add hB)
  have hMain : Tendsto (fun Q : ℕ =>
      coprimeHarmonicMainTerm W Q / Real.log Q)
      atTop (nhds (coprimeHarmonicDensity W)) := by
    apply hMainModel.congr'
    filter_upwards [hlogPos] with Q hQlog
    unfold coprimeHarmonicMainTerm
    dsimp [B]
    field_simp [hQlog.ne']
    ring
  have hHarm : Tendsto (fun Q : ℕ =>
      coprimeHarmonicSum W Q / Real.log Q)
      atTop (nhds (coprimeHarmonicDensity W)) := by
    have h := hHarmError.add hMain
    simpa only [zero_add] using h.congr'
      (Eventually.of_forall fun Q => by ring)
  have h := hCorr.add hHarm
  simpa only [zero_add] using h.congr'
    (Eventually.of_forall fun Q => by ring)

end BoundedGaps.Maynard
