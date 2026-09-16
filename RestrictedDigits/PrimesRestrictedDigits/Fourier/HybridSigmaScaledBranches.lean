import PrimesRestrictedDigits.Fourier.HybridSigmaFirstBranch
import PrimesRestrictedDigits.Fourier.HybridSigmaSecondBranch
import PrimesRestrictedDigits.Fourier.HybridSigmaScale
import PrimesRestrictedDigits.Fourier.HybridSigmaResidualSums

/-!
# Pure-power forms of the two hybrid Sigma branches

This module applies the scale-loss inequalities to the exact branch majorants. The residual
squared-transform sums are retained without further estimation.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

private theorem scaleConstant_pos_of_natCast_le_mul_pow
    {m k : Nat} (hm : 0 < m) {C : Real}
    (hscale : (m : Real) ≤ C * ((10 ^ k : Nat) : Real)) :
    0 < C := by
  by_contra hC
  have hCnonpos : C ≤ 0 := le_of_not_gt hC
  have hpowerNonneg : (0 : Real) ≤ ((10 ^ k : Nat) : Real) := by
    positivity
  have hproduct : C * ((10 ^ k : Nat) : Real) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hCnonpos hpowerNonneg
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  linarith

private theorem densityConstant_nonneg
    {m : Nat} {delta K : Real} (hdelta : 0 ≤ delta)
    (hdensity : delta * (m : Real) ≤ K) :
    0 ≤ K :=
  (mul_nonneg hdelta (Nat.cast_nonneg m)).trans hdensity

/-- The first exact Sigma branch after replacing its sampling factor by the
canonical pure-power bound. -/
theorem decimalHybridFirstSigmaBranch_le_power
    (digit : Fin 10) {q d k v u : Nat}
    (hq : 0 < q) (hd : 0 < d) (hdvd : d ∣ 10 ^ u)
    (hq10 : q.Coprime 10) {delta K : Real}
    (hdelta : 0 ≤ delta)
    (hdensity :
      delta * ((hybridDenominatorThirdFactor d (10 ^ k) : Nat) : Real) ≤ K) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    (∑ a : ReducedResidue q,
      ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / (d₃ : Real) + gamma) *
              normalizedPaddedDigitFourierMagnitudeSqAt digit v
                (((10 ^ k : Nat) : Real) *
                    hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  ((10 ^ k : Nat) : Real) * gamma))
          delta 0) ≤
      (2 * largeSieveSamplingConstant * (1 + K) *
          (d₃ : Real) ^ largeSieveAlpha) *
        decimalHybridFirstSquaredResidualSum digit q d k v delta := by
  dsimp only
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  let R := decimalHybridFirstSquaredResidualSum digit q d k v delta
  have hbranch := decimalHybridFirstSigmaBranch_le
    digit (k := k) (v := v) hq hd hdvd hq10 hdelta
  dsimp only at hbranch
  have hd₃ : 0 < d₃ := hybridDenominatorThirdFactor_pos hd
  have hK : 0 ≤ K := densityConstant_nonneg hdelta hdensity
  have hscaleNat : d₃ ≤ 10 ^ k :=
    Nat.le_of_dvd (by positivity)
      (hybridDenominatorThirdFactor_dvd_scale d (10 ^ k))
  have hscale : (d₃ : Real) ≤ (1 : Real) * ((10 ^ k : Nat) : Real) := by
    norm_num
    exact_mod_cast hscaleNat
  have hfactor := sigmaGrid_samplingFactor_le_power_of_le_mul
    k d₃ hd₃ hdelta (C := (1 : Real)) (K := K) (by norm_num) hK
      hscale hdensity
  have hfactor' :
      largeSieveSamplingConstant * (1 + delta * (d₃ : Real)) *
          ((d₃ : Real) ^ largeSieveAlpha +
            (d₃ : Real) *
              (((10 ^ k : Nat) : Real) ^ (-largeSieveSigma))) ≤
        2 * largeSieveSamplingConstant * (1 + K) *
          (d₃ : Real) ^ largeSieveAlpha := by
    simpa only [mul_one] using hfactor
  have hR : 0 ≤ R := by
    exact decimalHybridFirstSquaredResidualSum_nonneg
      digit q d k v hdelta
  have hscaled := hbranch.trans (mul_le_mul_of_nonneg_right hfactor' hR)
  simpa [R, decimalHybridFirstSquaredResidualSum, d₁, d₂] using hscaled

/-- The sharp second exact Sigma branch after replacing its sampling factor
by a pure-power bound with a real-power scale loss. -/
theorem decimalHybridSecondSigmaBranch_le_power_rpow
    (digit : Fin 10) {q d k v u : Nat}
    (hq : 0 < q) (hd : 0 < d) (hdvd : d ∣ 10 ^ u)
    (hq10 : q.Coprime 10) {delta C K : Real}
    (hdelta : 0 ≤ delta)
    (hscale :
      ((hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) *
        hybridDenominatorThirdFactor d (10 ^ k) : Nat) : Real) ≤
          C * ((10 ^ k : Nat) : Real))
    (hdensity :
      delta * ((hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) *
        hybridDenominatorThirdFactor d (10 ^ k) : Nat) : Real) ≤ K) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    (∑ a : ReducedResidue q,
      ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / (d₃ : Real) + gamma) *
              normalizedPaddedDigitFourierMagnitudeSqAt digit v
                (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
                    a b.1.1 +
                  (((10 ^ k * 10 ^ v : Nat) : Real) * gamma)))
          delta 0) ≤
      (largeSieveSamplingConstant * (1 + K) *
        (1 + C ^ largeSieveSigma) *
          ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha) *
        decimalHybridSecondSquaredResidualSum digit q d k v delta := by
  dsimp only
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  let R := decimalHybridSecondSquaredResidualSum digit q d k v delta
  have hbranch := decimalHybridSecondSigmaBranch_le
    digit (k := k) (v := v) hq hd hdvd hq10 hdelta
  dsimp only at hbranch
  have hd₂ : 0 < d₂ := hybridDenominatorSecondFactor_pos hd
  have hd₃ : 0 < d₃ := hybridDenominatorThirdFactor_pos hd
  have hd₂₃ : 0 < d₂ * d₃ := Nat.mul_pos hd₂ hd₃
  have hC : 0 < C := scaleConstant_pos_of_natCast_le_mul_pow hd₂₃ hscale
  have hK : 0 ≤ K := densityConstant_nonneg hdelta hdensity
  have hfactor := sigmaGrid_samplingFactor_le_power_of_le_mul_rpow
    k (d₂ * d₃) hd₂₃ hdelta hC hK hscale hdensity
  have hR : 0 ≤ R := by
    exact decimalHybridSecondSquaredResidualSum_nonneg
      digit q d k v hdelta
  have hscaled := hbranch.trans (mul_le_mul_of_nonneg_right hfactor hR)
  simpa [R, decimalHybridSecondSquaredResidualSum, d₁] using hscaled

/-- A coarse second-branch bound with a linear scale loss. -/
theorem decimalHybridSecondSigmaBranch_le_power
    (digit : Fin 10) {q d k v u : Nat}
    (hq : 0 < q) (hd : 0 < d) (hdvd : d ∣ 10 ^ u)
    (hq10 : q.Coprime 10) {delta C K : Real}
    (hdelta : 0 ≤ delta) (hC : 1 ≤ C)
    (hscale :
      ((hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) *
        hybridDenominatorThirdFactor d (10 ^ k) : Nat) : Real) ≤
          C * ((10 ^ k : Nat) : Real))
    (hdensity :
      delta * ((hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) *
        hybridDenominatorThirdFactor d (10 ^ k) : Nat) : Real) ≤ K) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    (∑ a : ReducedResidue q,
      ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / (d₃ : Real) + gamma) *
              normalizedPaddedDigitFourierMagnitudeSqAt digit v
                (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
                    a b.1.1 +
                  (((10 ^ k * 10 ^ v : Nat) : Real) * gamma)))
          delta 0) ≤
      (2 * largeSieveSamplingConstant * C * (1 + K) *
          ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha) *
        decimalHybridSecondSquaredResidualSum digit q d k v delta := by
  dsimp only
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  let R := decimalHybridSecondSquaredResidualSum digit q d k v delta
  have hbranch := decimalHybridSecondSigmaBranch_le
    digit (k := k) (v := v) hq hd hdvd hq10 hdelta
  dsimp only at hbranch
  have hd₂ : 0 < d₂ := hybridDenominatorSecondFactor_pos hd
  have hd₃ : 0 < d₃ := hybridDenominatorThirdFactor_pos hd
  have hK : 0 ≤ K := densityConstant_nonneg hdelta hdensity
  have hfactor := sigmaGrid_samplingFactor_le_power_of_le_mul
    k (d₂ * d₃) (Nat.mul_pos hd₂ hd₃) hdelta hC hK hscale hdensity
  have hR : 0 ≤ R := by
    exact decimalHybridSecondSquaredResidualSum_nonneg
      digit q d k v hdelta
  have hscaled := hbranch.trans (mul_le_mul_of_nonneg_right hfactor hR)
  simpa [R, decimalHybridSecondSquaredResidualSum, d₁] using hscaled

end

end PrimesRestrictedDigits
