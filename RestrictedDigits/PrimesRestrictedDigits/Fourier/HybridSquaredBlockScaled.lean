import PrimesRestrictedDigits.Fourier.HybridSquaredBlockSplit
import PrimesRestrictedDigits.Fourier.HybridSigmaScaledBranches

/-!
# Scaled squared-block estimate for the alternative hybrid bound

This module composes the exact squared-block split with the two pure-power Sigma branch
bounds. It stops before estimating either residual sum.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The unsplit squared-block sum after applying the canonical first and
sharp second pure-power Sigma estimates. -/
theorem sum_decimalHybridSquaredBlock_le_power_branches
    (digit : Fin 10) {q d k v u D : Nat}
    (hq : 0 < q) (hd : 0 < d) (hdD : d ≤ D) (hdvd : d ∣ 10 ^ u)
    (hq10 : q.Coprime 10) {E Y C K : Real}
    (hE : 0 ≤ E) (hY : 0 < Y)
    (hDscale : (D : Real) ≤ C * ((10 ^ k : Nat) : Real))
    (hDEY : E * (D : Real) ≤ K * Y) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    (∑ a : ReducedResidue q,
      ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / d₃ + gamma) *
              normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                (((10 ^ k : Nat) : Real) *
                  (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                    (b.2.val : Real) / d₃ + gamma)))
          (E / Y) 0) ≤
      (2 * largeSieveSamplingConstant * (1 + K) *
          (d₃ : Real) ^ largeSieveAlpha) *
        decimalHybridFirstSquaredResidualSum digit q d k v (E / Y) +
      (largeSieveSamplingConstant * (1 + K) *
        (1 + C ^ largeSieveSigma) *
          ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha) *
        decimalHybridSecondSquaredResidualSum digit q d k v (E / Y) := by
  dsimp only
  have hdelta : 0 ≤ E / Y := div_nonneg hE hY.le
  have hscaleData := hybridSigmaGrid_scale_data
    (v := v) hd hdD hE hY hDscale hDEY
  dsimp only at hscaleData
  rcases hscaleData with
    ⟨hd₃, hd₃scale, hd₃density, hd₂₃, hd₂₃scale, hd₂₃density⟩
  have hsplit := sum_decimalHybridSquaredBlock_le_add_branches
    (q := q) (d := d) (k := k) (v := v) digit hd hdelta
  dsimp only at hsplit
  have hfirst := decimalHybridFirstSigmaBranch_le_power
    digit (k := k) (v := v) hq hd hdvd hq10 hdelta hd₃density
  dsimp only at hfirst
  have hsecond := decimalHybridSecondSigmaBranch_le_power_rpow
    digit (k := k) (v := v) hq hd hdvd hq10 hdelta
      hd₂₃scale hd₂₃density
  dsimp only at hsecond
  exact hsplit.trans (add_le_add hfirst hsecond)

/-- The source-facing factor-ten specialization. Its second branch uses the
coarse linear scale loss, so no `10 ^ largeSieveSigma` factor remains. -/
theorem sum_decimalHybridSquaredBlock_le_power_branches_of_factorTenBounds
    (digit : Fin 10) {q d k v u D length : Nat}
    (hq : 0 < q) (hd : 0 < d) (hdD : d ≤ D) (hdvd : d ∣ 10 ^ u)
    (hq10 : q.Coprime 10) {E : Real} (hE : 0 ≤ E)
    (hDscale : (D : Real) ≤ 10 * ((10 ^ k : Nat) : Real))
    (hDEY : 10 * (D : Real) * E ≤ ((10 ^ length : Nat) : Real)) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    (∑ a : ReducedResidue q,
      ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / d₃ + gamma) *
              normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                (((10 ^ k : Nat) : Real) *
                  (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                    (b.2.val : Real) / d₃ + gamma)))
          (E / ((10 ^ length : Nat) : Real)) 0) ≤
      (2 * largeSieveSamplingConstant * (1 + (1 : Real) / 10) *
          (d₃ : Real) ^ largeSieveAlpha) *
        decimalHybridFirstSquaredResidualSum digit q d k v
          (E / ((10 ^ length : Nat) : Real)) +
      (2 * largeSieveSamplingConstant * 10 * (1 + (1 : Real) / 10) *
          ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha) *
        decimalHybridSecondSquaredResidualSum digit q d k v
          (E / ((10 ^ length : Nat) : Real)) := by
  dsimp only
  have hY : (0 : Real) < ((10 ^ length : Nat) : Real) := by positivity
  have hdelta : 0 ≤ E / ((10 ^ length : Nat) : Real) :=
    div_nonneg hE hY.le
  have hscaleData := hybridSigmaGrid_scale_data_of_factorTenBounds
    (v := v) hd hdD hE hDscale hDEY
  dsimp only at hscaleData
  rcases hscaleData with
    ⟨hd₃, hd₃scale, hd₃density, hd₂₃, hd₂₃scale, hd₂₃density⟩
  have hsplit := sum_decimalHybridSquaredBlock_le_add_branches
    (q := q) (d := d) (k := k) (v := v) digit hd hdelta
  dsimp only at hsplit
  have hfirst := decimalHybridFirstSigmaBranch_le_power
    digit (k := k) (v := v) hq hd hdvd hq10 hdelta hd₃density
  dsimp only at hfirst
  have hsecond := decimalHybridSecondSigmaBranch_le_power
    digit (k := k) (v := v) hq hd hdvd hq10 hdelta
      (C := (10 : Real)) (K := (1 : Real) / 10) (by norm_num)
      hd₂₃scale hd₂₃density
  dsimp only at hsecond
  exact hsplit.trans (add_le_add hfirst hsecond)

end

end PrimesRestrictedDigits
