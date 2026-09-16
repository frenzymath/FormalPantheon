import PrimesRestrictedDigits.Fourier.HybridDenominatorSplit
import PrimesRestrictedDigits.Fourier.HybridSigmaGrid

/-!
# Explicit scale losses for the hybrid Sigma grids

This module exposes the comparison constants suppressed in equations (10.14)--(10.15) of
published Lemma 10.7.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The exact real-power loss when a grid modulus is at most `C` times the
transform scale. -/
theorem sigmaGrid_tail_le_of_le_mul_rpow
    {q Y C : Real} (hq : 0 < q) (_hY : 0 < Y) (hC : 0 < C)
    (hqY : q ≤ C * Y) :
    q * Y ^ (-largeSieveSigma) ≤
      C ^ largeSieveSigma * q ^ largeSieveAlpha := by
  have hqDiv : q / C ≤ Y :=
    (div_le_iff₀ hC).2 (by simpa [mul_comm] using hqY)
  have hnegative :
      Y ^ (-largeSieveSigma) ≤ (q / C) ^ (-largeSieveSigma) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hq hC) hqDiv
      (neg_nonpos.mpr largeSieveSigma_nonneg)
  have hrewrite :
      q * (q / C) ^ (-largeSieveSigma) =
        C ^ largeSieveSigma * q ^ largeSieveAlpha := by
    rw [Real.div_rpow hq.le hC.le]
    rw [Real.rpow_neg hq.le, Real.rpow_neg hC.le]
    rw [div_eq_mul_inv, inv_inv]
    calc
      q * ((q ^ largeSieveSigma)⁻¹ * C ^ largeSieveSigma) =
          C ^ largeSieveSigma *
            (q ^ (1 : Real) * q ^ (-largeSieveSigma)) := by
        rw [Real.rpow_one, Real.rpow_neg hq.le]
        ring
      _ = C ^ largeSieveSigma *
          q ^ ((1 : Real) + (-largeSieveSigma)) := by
        rw [Real.rpow_add hq]
      _ = C ^ largeSieveSigma * q ^ largeSieveAlpha := by
        congr 2
        norm_num [largeSieveAlpha, largeSieveSigma]
  calc
    q * Y ^ (-largeSieveSigma) ≤
        q * (q / C) ^ (-largeSieveSigma) :=
      mul_le_mul_of_nonneg_left hnegative hq.le
    _ = _ := hrewrite

/-- The coarse tail loss used when the scale comparison constant is at least
one. -/
theorem sigmaGrid_tail_le_of_le_mul
    {q Y C : Real} (hq : 0 < q) (hY : 0 < Y) (hC : 1 ≤ C)
    (hqY : q ≤ C * Y) :
    q * Y ^ (-largeSieveSigma) ≤ C * q ^ largeSieveAlpha := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have htail := sigmaGrid_tail_le_of_le_mul_rpow hq hY hC0 hqY
  have hCpow : C ^ largeSieveSigma ≤ C := by
    calc
      C ^ largeSieveSigma ≤ C ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hC (by
          norm_num [largeSieveSigma])
      _ = C := Real.rpow_one C
  exact htail.trans (mul_le_mul_of_nonneg_right hCpow <|
    Real.rpow_nonneg hq.le _)

/-- The sharp pure-power upper bound for the explicit complete-grid sampler
factor. -/
theorem sigmaGrid_samplingFactor_le_power_of_le_mul_rpow
    (length q : Nat) (hq : 0 < q)
    {delta C K : Real} (_hdelta : 0 ≤ delta) (hC : 0 < C)
    (hK : 0 ≤ K)
    (hqY : (q : Real) ≤ C * ((10 ^ length : Nat) : Real))
    (hdeltaq : delta * (q : Real) ≤ K) :
    largeSieveSamplingConstant * (1 + delta * (q : Real)) *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) ≤
      largeSieveSamplingConstant * (1 + K) *
        (1 + C ^ largeSieveSigma) *
          (q : Real) ^ largeSieveAlpha := by
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  have hY0 : (0 : Real) < ((10 ^ length : Nat) : Real) := by positivity
  have htail := sigmaGrid_tail_le_of_le_mul_rpow hq0 hY0 hC hqY
  have hpower0 : 0 ≤ (q : Real) ^ largeSieveAlpha :=
    Real.rpow_nonneg hq0.le _
  have hCpower0 : 0 ≤ C ^ largeSieveSigma :=
    Real.rpow_nonneg hC.le _
  have hsum :
      (q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)) ≤
        (1 + C ^ largeSieveSigma) *
          (q : Real) ^ largeSieveAlpha := by
    nlinarith
  have hsum0 :
      0 ≤ (q : Real) ^ largeSieveAlpha +
        (q : Real) *
          (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)) := by
    positivity
  have hconstant : 0 ≤ largeSieveSamplingConstant := by
    norm_num [largeSieveSamplingConstant]
  calc
    _ ≤ largeSieveSamplingConstant * (1 + K) *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hconstant) hsum0
    _ ≤ largeSieveSamplingConstant * (1 + K) *
        ((1 + C ^ largeSieveSigma) *
          (q : Real) ^ largeSieveAlpha) := by
      exact mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hconstant (by linarith))
    _ = _ := by ring

/-- A coarse sampler-factor bound with a linear loss in `C`. -/
theorem sigmaGrid_samplingFactor_le_power_of_le_mul
    (length q : Nat) (hq : 0 < q)
    {delta C K : Real} (hdelta : 0 ≤ delta) (hC : 1 ≤ C)
    (hK : 0 ≤ K)
    (hqY : (q : Real) ≤ C * ((10 ^ length : Nat) : Real))
    (hdeltaq : delta * (q : Real) ≤ K) :
    largeSieveSamplingConstant * (1 + delta * (q : Real)) *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) ≤
      2 * largeSieveSamplingConstant * C * (1 + K) *
        (q : Real) ^ largeSieveAlpha := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hsharp := sigmaGrid_samplingFactor_le_power_of_le_mul_rpow
    length q hq hdelta hC0 hK hqY hdeltaq
  have hCpow : C ^ largeSieveSigma ≤ C := by
    calc
      C ^ largeSieveSigma ≤ C ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hC (by
          norm_num [largeSieveSigma])
      _ = C := Real.rpow_one C
  have hcoefficient : 1 + C ^ largeSieveSigma ≤ 2 * C := by linarith
  have hconstant : 0 ≤ largeSieveSamplingConstant := by
    norm_num [largeSieveSamplingConstant]
  have hfront : 0 ≤ largeSieveSamplingConstant * (1 + K) :=
    mul_nonneg hconstant (by linarith)
  have hpower : 0 ≤ (q : Real) ^ largeSieveAlpha := by positivity
  calc
    _ ≤ largeSieveSamplingConstant * (1 + K) *
        (1 + C ^ largeSieveSigma) *
          (q : Real) ^ largeSieveAlpha := hsharp
    _ ≤ largeSieveSamplingConstant * (1 + K) * (2 * C) *
          (q : Real) ^ largeSieveAlpha :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoefficient hfront) hpower
    _ = _ := by ring

/-- The sharp generalized pure-power estimate for the exact complete grid. -/
theorem completeFinGrid_largeSieveSampling_le_power_of_le_mul_rpow
    (digit : Fin 10) (length q : Nat) (hq : 0 < q)
    {delta C K : Real} (hdelta : 0 ≤ delta) (hC : 0 < C)
    (hK : 0 ≤ K)
    (hqY : (q : Real) ≤ C * ((10 ^ length : Nat) : Real))
    (hdeltaq : delta * (q : Real) ≤ K) (beta : Real) :
    (∑ a : Fin q, closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
        ((a.val : Real) / q + beta)) ≤
      largeSieveSamplingConstant * (1 + K) *
        (1 + C ^ largeSieveSigma) *
          (q : Real) ^ largeSieveAlpha := by
  calc
    _ ≤ largeSieveSamplingConstant * (1 + delta * (q : Real)) *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) :=
      completeFinGrid_largeSieveSampling digit length q hq hdelta beta
    _ ≤ _ := sigmaGrid_samplingFactor_le_power_of_le_mul_rpow
      length q hq hdelta hC hK hqY hdeltaq

/-- The generalized complete-grid estimate with a coarse linear scale loss. -/
theorem completeFinGrid_largeSieveSampling_le_power_of_le_mul
    (digit : Fin 10) (length q : Nat) (hq : 0 < q)
    {delta C K : Real} (hdelta : 0 ≤ delta) (hC : 1 ≤ C)
    (hK : 0 ≤ K)
    (hqY : (q : Real) ≤ C * ((10 ^ length : Nat) : Real))
    (hdeltaq : delta * (q : Real) ≤ K) (beta : Real) :
    (∑ a : Fin q, closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
        ((a.val : Real) / q + beta)) ≤
      2 * largeSieveSamplingConstant * C * (1 + K) *
        (q : Real) ^ largeSieveAlpha := by
  calc
    _ ≤ largeSieveSamplingConstant * (1 + delta * (q : Real)) *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) :=
      completeFinGrid_largeSieveSampling digit length q hq hdelta beta
    _ ≤ _ := sigmaGrid_samplingFactor_le_power_of_le_mul
      length q hq hdelta hC hK hqY hdeltaq

/-- Scale and window-density data for both canonical decimal hybrid grids. -/
theorem hybridSigmaGrid_scale_data
    {d D k v : Nat} (hd : 0 < d) (hdD : d ≤ D)
    {E Y C K : Real} (hE : 0 ≤ E) (hY : 0 < Y)
    (hDscale : (D : Real) ≤ C * ((10 ^ k : Nat) : Real))
    (hDEY : E * (D : Real) ≤ K * Y) :
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    let d₂₃ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) * d₃
    0 < d₃ ∧
    d₃ ≤ 10 ^ k ∧
    (E / Y) * (d₃ : Real) ≤ K ∧
    0 < d₂₃ ∧
    (d₂₃ : Real) ≤ C * ((10 ^ k : Nat) : Real) ∧
    (E / Y) * (d₂₃ : Real) ≤ K := by
  dsimp only
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  let d₂₃ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) * d₃
  have hd₃pos : 0 < d₃ := hybridDenominatorThirdFactor_pos hd
  have hd₂₃pos : 0 < d₂₃ := by
    exact Nat.mul_pos (hybridDenominatorSecondFactor_pos hd)
      (hybridDenominatorThirdFactor_pos hd)
  have hd₃scale : d₃ ≤ 10 ^ k :=
    Nat.le_of_dvd (by positivity)
      (hybridDenominatorThirdFactor_dvd_scale d (10 ^ k))
  have hd₂₃d : d₂₃ ≤ d := by
    apply Nat.le_of_dvd hd
    rw [show d₂₃ = Nat.gcd d (10 ^ k * 10 ^ v) by
      exact hybridDenominatorSecondThird_eq_gcd d (10 ^ k) (10 ^ v)]
    exact Nat.gcd_dvd_left _ _
  have hd₂₃scale :
      (d₂₃ : Real) ≤ C * ((10 ^ k : Nat) : Real) := by
    have hd₂₃D : (d₂₃ : Real) ≤ (D : Real) := by
      exact_mod_cast hd₂₃d.trans hdD
    exact hd₂₃D.trans hDscale
  have hd₃d : d₃ ≤ d :=
    Nat.le_of_dvd hd (Nat.gcd_dvd_left d (10 ^ k))
  have density_of_le {q : Nat} (hqd : q ≤ d) :
      (E / Y) * (q : Real) ≤ K := by
    have hqD : (q : Real) ≤ (D : Real) := by
      exact_mod_cast hqd.trans hdD
    have hEY0 : 0 ≤ E / Y := div_nonneg hE hY.le
    calc
      (E / Y) * (q : Real) ≤ (E / Y) * (D : Real) :=
        mul_le_mul_of_nonneg_left hqD hEY0
      _ = (E * (D : Real)) / Y := by ring
      _ ≤ (K * Y) / Y := div_le_div_of_nonneg_right hDEY hY.le
      _ = K := by field_simp
  exact ⟨hd₃pos, hd₃scale, density_of_le hd₃d,
    hd₂₃pos, hd₂₃scale, density_of_le hd₂₃d⟩

/-- The hybrid scale data under the weak factor-ten comparisons supplied by a
later source block selector. -/
theorem hybridSigmaGrid_scale_data_of_factorTenBounds
    {d D k v length : Nat} (hd : 0 < d) (hdD : d ≤ D)
    {E : Real} (hE : 0 ≤ E)
    (hDscale : (D : Real) ≤ 10 * ((10 ^ k : Nat) : Real))
    (hDEY : 10 * (D : Real) * E ≤ ((10 ^ length : Nat) : Real)) :
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    let d₂₃ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) * d₃
    0 < d₃ ∧
    d₃ ≤ 10 ^ k ∧
    (E / ((10 ^ length : Nat) : Real)) * (d₃ : Real) ≤ (1 : Real) / 10 ∧
    0 < d₂₃ ∧
    (d₂₃ : Real) ≤ 10 * ((10 ^ k : Nat) : Real) ∧
    (E / ((10 ^ length : Nat) : Real)) * (d₂₃ : Real) ≤ (1 : Real) / 10 := by
  have hY : (0 : Real) < ((10 ^ length : Nat) : Real) := by positivity
  have hEDY :
      E * (D : Real) ≤ (1 / 10 : Real) *
        ((10 ^ length : Nat) : Real) := by
    nlinarith
  exact hybridSigmaGrid_scale_data hd hdD hE hY hDscale hEDY

end

end PrimesRestrictedDigits
