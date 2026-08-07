import BoundedGaps.Maynard.ConcreteS1CrossGrowth
import BoundedGaps.Maynard.ConcreteS2TauAsymptotics

noncomputable section

/-!
# Vanishing of the normalized concrete S1 cross correction

The pre-sieve density factors cancel exactly against the Maynard scale.  The
remaining bounded logarithm ratio is multiplied by the reciprocal shifted
triple-log cutoff.
-/

namespace BoundedGaps.Maynard

open Filter Set

noncomputable def engelsmaS1CrossNormalizationConstant : ℝ :=
  smallKCandidateBound ^ 2 * (8 * Real.exp 8) *
    ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
      (Real.exp 8) ^
        ((offDiagonalPairs BoundedGaps.engelsmaTuple).card - 1) * 8 ^ 105

theorem engelsmaS1CrossNormalizationConstant_nonneg :
    0 ≤ engelsmaS1CrossNormalizationConstant := by
  unfold engelsmaS1CrossNormalizationConstant
  positivity

theorem log_natCast_le_two_mul_log_sub
    {N : ℕ} (hN : 3 ≤ N) :
    Real.log (N : ℝ) ≤ 2 * Real.log ((N - 1 : ℕ) : ℝ) := by
  have hMtwo : 2 ≤ N - 1 := by omega
  have hNle : N ≤ 2 * (N - 1) := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hMpos : (0 : ℝ) < (N - 1 : ℕ) := by positivity
  have hlogMono : Real.log (N : ℝ) ≤
      Real.log ((2 : ℝ) * (N - 1 : ℕ)) := by
    apply Real.strictMonoOn_log.monotoneOn hNpos
      (mul_pos (by norm_num) hMpos)
    exact_mod_cast hNle
  have hlogTwo : Real.log 2 ≤ Real.log ((N - 1 : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn (by norm_num) hMpos
    exact_mod_cast hMtwo
  rw [Real.log_mul (by norm_num) hMpos.ne'] at hlogMono
  linarith

theorem eventually_engelsmaRadiusLogRatio_bounded
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤ (1 + Real.log (engelsmaMaynardRadius alpha N)) /
        Real.log (engelsmaMaynardRealRadius alpha N) ∧
      (1 + Real.log (engelsmaMaynardRadius alpha N)) /
          Real.log (engelsmaMaynardRealRadius alpha N) ≤
        2 * (1 + alpha) / alpha := by
  have hupper := eventually_one_add_log_engelsmaMaynardRadius_le halpha
  have hconditions := eventually_engelsmaMaynardCrossBound_conditions halpha
  filter_upwards [hupper, hconditions, eventually_ge_atTop 3] with
      N hupperN hconditionsN hN
  have hMpos : (0 : ℝ) < (N - 1 : ℕ) := by
    exact_mod_cast (show 0 < N - 1 by omega)
  have hlogMpos : 0 < Real.log ((N - 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N - 1 by omega)
  have hrealLog : Real.log (engelsmaMaynardRealRadius alpha N) =
      alpha * Real.log ((N - 1 : ℕ) : ℝ) := by
    unfold engelsmaMaynardRealRadius maynardRealCutoff
    simpa using Real.log_rpow hMpos alpha
  have hrealLogPos : 0 < Real.log (engelsmaMaynardRealRadius alpha N) := by
    rw [hrealLog]
    positivity
  have hnatLogNonneg :
      0 ≤ 1 + Real.log (engelsmaMaynardRadius alpha N) := by
    have hWpos : (0 : ℝ) < engelsmaMaynardModulus N := by
      exact_mod_cast primorial_pos (tripleLogCutoff (N - 1))
    exact hWpos.le.trans hconditionsN.2.2
  constructor
  · exact div_nonneg hnatLogNonneg hrealLogPos.le
  · apply (div_le_iff₀ hrealLogPos).2
    rw [hrealLog]
    have hlogN := log_natCast_le_two_mul_log_sub hN
    have halphaNonzero : alpha ≠ 0 := halpha.ne'
    field_simp [halphaNonzero]
    nlinarith [mul_le_mul_of_nonneg_left hlogN (by positivity : 0 ≤ 1 + alpha)]

theorem tendsto_shifted_tripleLogCutoff :
    Tendsto (fun N : ℕ => tripleLogCutoff (N - 1)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro K
  obtain ⟨M₀, hM₀⟩ := exists_tripleLogCutoff_ge K
  exact ⟨M₀ + 1, fun N hN => hM₀ (N - 1) (by omega)⟩

theorem eventually_abs_normalized_engelsmaS1Cross_le
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      |((N : ℝ) / engelsmaMaynardModulus N *
          engelsmaMaynardS1CrossCorrection alpha N) /
          engelsmaMaynardScale alpha N| ≤
        (engelsmaS1CrossNormalizationConstant /
          (tripleLogCutoff (N - 1) : ℝ)) *
            (2 * (1 + alpha) / alpha) ^ 105 := by
  have hconditions := eventually_engelsmaMaynardCrossBound_conditions halpha
  have hratio := eventually_engelsmaRadiusLogRatio_bounded halpha
  have hscale := eventually_engelsmaMaynardScale_pos halpha
  filter_upwards [hconditions, hratio, hscale, eventually_ge_atTop 3] with
      N hconditionsN hratioN hscaleN hN
  let W : ℝ := engelsmaMaynardModulus N
  let phiW : ℝ := Nat.totient (engelsmaMaynardModulus N)
  let D : ℝ := tripleLogCutoff (N - 1)
  let Lnat : ℝ := 1 + Real.log (engelsmaMaynardRadius alpha N)
  let Lreal : ℝ := Real.log (engelsmaMaynardRealRadius alpha N)
  let A : ℝ := smallKCandidateBound ^ 2 * (8 * Real.exp 8) *
      ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
        (Real.exp 8) ^
          ((offDiagonalPairs BoundedGaps.engelsmaTuple).card - 1)
  let C : ℝ := (A / D) * (8 * (phiW / W) * Lnat) ^ 105
  have hCorr : |engelsmaMaynardS1CrossCorrection alpha N| ≤ C := by
    have h := abs_engelsmaMaynardS1CrossCorrection_le_log
      hconditionsN.1 hconditionsN.2.1 hconditionsN.2.2
    have hk : Fintype.card BoundedGaps.engelsmaTuple = 105 := by
      simpa only [Fintype.card_coe] using BoundedGaps.engelsmaTuple_card
    rw [hk] at h
    change |engelsmaMaynardS1CrossCorrection alpha N| ≤
      smallKCandidateBound ^ 2 *
        ((8 * Real.exp 8 / D) *
          ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
            (Real.exp 8) ^
              ((offDiagonalPairs BoundedGaps.engelsmaTuple).card - 1)) *
        (8 * (phiW / W) * Lnat) ^ 105 at h
    calc
      |engelsmaMaynardS1CrossCorrection alpha N| ≤
          smallKCandidateBound ^ 2 *
            ((8 * Real.exp 8 / D) *
              ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
                (Real.exp 8) ^
                  ((offDiagonalPairs BoundedGaps.engelsmaTuple).card - 1)) *
            (8 * (phiW / W) * Lnat) ^ 105 := h
      _ = C := by
        unfold C A
        ring
  have hW : 0 < W := by
    unfold W
    exact_mod_cast primorial_pos (tripleLogCutoff (N - 1))
  have hphi : 0 < phiW := by
    unfold phiW
    exact_mod_cast Nat.totient_pos.mpr
      (primorial_pos (tripleLogCutoff (N - 1)))
  have hD : 0 < D := by
    unfold D
    exact_mod_cast hconditionsN.2.1
  have hNpos : (0 : ℝ) < N := by positivity
  have hLreal : 0 < Lreal := by
    unfold Lreal
    have hreal := maynardRealCutoff_gt_one
      (alpha := alpha) (N := N - 1) (by omega) halpha
    exact Real.log_pos hreal
  have hconstant : engelsmaS1CrossNormalizationConstant = A * 8 ^ 105 := by
    unfold engelsmaS1CrossNormalizationConstant A
    ring
  have hnormalized :
      ((N : ℝ) / W * C) / engelsmaMaynardScale alpha N =
        (engelsmaS1CrossNormalizationConstant / D) *
          (Lnat / Lreal) ^ 105 := by
    rw [hconstant]
    unfold C
    change ((N : ℝ) / W * ((A / D) *
        (8 * (phiW / W) * Lnat) ^ 105)) /
          ((phiW ^ 105 * (N : ℝ) * Lreal ^ 105) / W ^ 106) =
      (A * 8 ^ 105 / D) * (Lnat / Lreal) ^ 105
    field_simp [hW.ne', hphi.ne', hD.ne', hNpos.ne', hLreal.ne']
  calc
    |((N : ℝ) / engelsmaMaynardModulus N *
        engelsmaMaynardS1CrossCorrection alpha N) /
        engelsmaMaynardScale alpha N| =
        ((N : ℝ) / W *
          |engelsmaMaynardS1CrossCorrection alpha N|) /
            engelsmaMaynardScale alpha N := by
      rw [abs_div, abs_mul, abs_div, abs_of_nonneg (Nat.cast_nonneg N),
        abs_of_pos hW, abs_of_pos hscaleN]
    _ ≤ ((N : ℝ) / W * C) / engelsmaMaynardScale alpha N := by
      apply div_le_div_of_nonneg_right _ hscaleN.le
      exact mul_le_mul_of_nonneg_left hCorr (div_nonneg hNpos.le hW.le)
    _ = (engelsmaS1CrossNormalizationConstant / D) *
        (Lnat / Lreal) ^ 105 := hnormalized
    _ ≤ (engelsmaS1CrossNormalizationConstant / D) *
        (2 * (1 + alpha) / alpha) ^ 105 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hratioN.1 hratioN.2 105)
        (div_nonneg engelsmaS1CrossNormalizationConstant_nonneg hD.le)

theorem tendsto_normalized_engelsmaMaynardS1CrossCorrection_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto
      (fun N : ℕ =>
        ((N : ℝ) / engelsmaMaynardModulus N *
          engelsmaMaynardS1CrossCorrection alpha N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  let C : ℝ := engelsmaS1CrossNormalizationConstant *
    (2 * (1 + alpha) / alpha) ^ 105
  have henvelope : Tendsto
      (fun N : ℕ => C / (tripleLogCutoff (N - 1) : ℝ))
      atTop (nhds 0) := by
    exact (tendsto_const_div_atTop_nhds_zero_nat C).comp
      tendsto_shifted_tripleLogCutoff
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henvelope
  filter_upwards [eventually_abs_normalized_engelsmaS1Cross_le halpha] with
      N hN
  unfold C
  calc
    |((N : ℝ) / engelsmaMaynardModulus N *
        engelsmaMaynardS1CrossCorrection alpha N) /
        engelsmaMaynardScale alpha N| ≤
        (engelsmaS1CrossNormalizationConstant /
          (tripleLogCutoff (N - 1) : ℝ)) *
            (2 * (1 + alpha) / alpha) ^ 105 := hN
    _ = (engelsmaS1CrossNormalizationConstant *
        (2 * (1 + alpha) / alpha) ^ 105) /
          (tripleLogCutoff (N - 1) : ℝ) := by ring

end BoundedGaps.Maynard
