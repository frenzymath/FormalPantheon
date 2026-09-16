import PrimesRestrictedDigits.Fourier.HybridResidualBranchBounds
import PrimesRestrictedDigits.Fourier.HybridSquaredBlockScaled

/-!
# Outer Squared-Block Source Sum

This file sums the scaled squared-block estimate over the literal source `q2` band and inserts
both equation (10.16) residual bounds. See `MAYNARD-PRD-PUBLISHED`, pp. 182--185.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The source-band sum of the unsplit `D'` times `V^2` squared-block input,
after the separate `E'` factor has been removed. -/
noncomputable def decimalHybridSquaredBlockSourceBandSum
    (digit : Fin 10) (q₁ d k v Q₂ : Nat) (delta : Real) : Real :=
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  ∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
    ∑ a : ReducedResidue (q₁ * q₂),
      ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo (q₁ * q₂) d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / d₃ + gamma) *
              normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                (((10 ^ k : Nat) : Real) *
                  (hybridSourceBetaTwo (q₁ * q₂) d₁ d₂ d₃ a b.1 +
                    (b.2.val : Real) / d₃ + gamma)))
          delta 0

/-- Summing the fixed-denominator squared-block estimate extracts the two
grid coefficients without changing any source-band multiplicity. -/
theorem decimalHybridSquaredBlockSourceBandSum_le_power_residualSums
    (digit : Fin 10) {q₁ d k v u D Q₂ : Nat}
    (hq₁ : 0 < q₁) (hd : 0 < d) (hdD : d <= D)
    (hdvd : d ∣ 10 ^ u) (hq₁10 : q₁.Coprime 10)
    {E Y C K : Real} (hE : 0 <= E) (hY : 0 < Y)
    (hDscale : (D : Real) <= C * ((10 ^ k : Nat) : Real))
    (hDEY : E * (D : Real) <= K * Y) :
    let _d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    decimalHybridSquaredBlockSourceBandSum digit q₁ d k v Q₂ (E / Y) <=
      (2 * largeSieveSamplingConstant * (1 + K) *
          (d₃ : Real) ^ largeSieveAlpha) *
        (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
          decimalHybridFirstSquaredResidualSum digit (q₁ * q₂) d k v
            (E / Y)) +
      (largeSieveSamplingConstant * (1 + K) *
        (1 + C ^ largeSieveSigma) *
          ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha) *
        (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
          decimalHybridSecondSquaredResidualSum digit (q₁ * q₂) d k v
            (E / Y)) := by
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  let A₁ : Real := 2 * largeSieveSamplingConstant * (1 + K) *
    (d₃ : Real) ^ largeSieveAlpha
  let A₂ : Real := largeSieveSamplingConstant * (1 + K) *
    (1 + C ^ largeSieveSigma) *
      ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha
  let R₁ (q₂ : Nat) :=
    decimalHybridFirstSquaredResidualSum digit (q₁ * q₂) d k v (E / Y)
  let R₂ (q₂ : Nat) :=
    decimalHybridSecondSquaredResidualSum digit (q₁ * q₂) d k v (E / Y)
  change decimalHybridSquaredBlockSourceBandSum digit q₁ d k v Q₂
      (E / Y) <=
    A₁ * (∑ q₂ ∈ hybridResidualSourceDenominators Q₂, R₁ q₂) +
      A₂ * (∑ q₂ ∈ hybridResidualSourceDenominators Q₂, R₂ q₂)
  unfold decimalHybridSquaredBlockSourceBandSum
  dsimp only
  calc
    (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
        ∑ a : ReducedResidue (q₁ * q₂),
          ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
            closedWindowMaximum
              (fun gamma =>
                normalizedPaddedDigitFourierMagnitudeAt digit k
                    (hybridSourceBetaTwo (q₁ * q₂) d₁ d₂ d₃ a b.1 +
                      (b.2.val : Real) / d₃ + gamma) *
                  normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                    (((10 ^ k : Nat) : Real) *
                      (hybridSourceBetaTwo (q₁ * q₂) d₁ d₂ d₃ a b.1 +
                        (b.2.val : Real) / d₃ + gamma)))
              (E / Y) 0) <=
        ∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
          (A₁ * R₁ q₂ + A₂ * R₂ q₂) := by
      apply Finset.sum_le_sum
      intro q₂ hq₂
      have hq₂Data := mem_hybridResidualSourceDenominators_iff.mp hq₂
      have hq₂Pos : 0 < q₂ := by omega
      have hqProd : 0 < q₁ * q₂ := Nat.mul_pos hq₁ hq₂Pos
      have hqProd10 : (q₁ * q₂).Coprime 10 :=
        hq₁10.mul_left hq₂Data.2.2.2
      have hbound :=
        sum_decimalHybridSquaredBlock_le_power_branches
          digit (q := q₁ * q₂) (d := d) (k := k) (v := v) (u := u)
            (D := D) hqProd hd hdD hdvd hqProd10
            (E := E) (Y := Y) (C := C) (K := K)
            hE hY hDscale hDEY
      simpa [A₁, A₂, R₁, R₂, d₁, d₂, d₃] using hbound
    _ = A₁ * (∑ q₂ ∈ hybridResidualSourceDenominators Q₂, R₁ q₂) +
        A₂ * (∑ q₂ ∈ hybridResidualSourceDenominators Q₂, R₂ q₂) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Source-loss specialization after both residual sums have been bounded by
the explicit coarse equation (10.16) estimate. -/
theorem decimalHybridSquaredBlockSourceBandSum_le_source_branches
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength q₁ d u Q₁ Q₂ : Nat}
    (hscale : dLength + eLength <= length + loss)
    (hq₁ : 0 < q₁) (hd : 0 < d) (hdD : d <= 10 ^ dLength)
    (hdvd : d ∣ 10 ^ u) (hq₁10 : q₁.Coprime 10)
    (hQ₂ : 0 < Q₂) (hq₁Upper : q₁ <= Q₁) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    let d₁ := hybridDenominatorFirstFactor d (10 ^ dAux) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ dAux) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ dAux)
    let C : Real := ((10 ^ loss : Nat) : Real)
    let B : Real := 3600 * (1 + 2 * C)
    let A₁ : Real := 2 * largeSieveSamplingConstant * (1 + C) *
      (d₃ : Real) ^ largeSieveAlpha
    let A₂ : Real := largeSieveSamplingConstant * (1 + C) *
      (1 + C ^ largeSieveSigma) *
        ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha
    let P₁ : Real := (((d₁ * d₂) * Q₁ * Q₂ ^ 2 : Nat) : Real)
    let P₂ : Real := ((d₁ * Q₁ * Q₂ ^ 2 : Nat) : Real)
    let Z : Real :=
      ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real))
    decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
        (((10 ^ eLength : Nat) : Real) /
          ((10 ^ length : Nat) : Real)) <=
      B *
        (A₁ * (P₁ ^ hybridResidualGrowth +
            P₁ * Z ^ (-hybridResidualHalfDecay)) +
          A₂ * (P₂ ^ hybridResidualGrowth +
            P₂ * Z ^ (-hybridResidualHalfDecay))) := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  let d₁ := hybridDenominatorFirstFactor d (10 ^ dAux) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ dAux) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ dAux)
  let C : Real := ((10 ^ loss : Nat) : Real)
  let B : Real := 3600 * (1 + 2 * C)
  let A₁ : Real := 2 * largeSieveSamplingConstant * (1 + C) *
    (d₃ : Real) ^ largeSieveAlpha
  let A₂ : Real := largeSieveSamplingConstant * (1 + C) *
    (1 + C ^ largeSieveSigma) *
      ((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha
  let P₁ : Real := (((d₁ * d₂) * Q₁ * Q₂ ^ 2 : Nat) : Real)
  let P₂ : Real := ((d₁ * Q₁ * Q₂ ^ 2 : Nat) : Real)
  let Z : Real :=
    ((10 ^ length : Nat) : Real) /
      (((10 ^ dLength : Nat) : Real) *
        ((10 ^ eLength : Nat) : Real))
  let E : Real := ((10 ^ eLength : Nat) : Real)
  let Y : Real := ((10 ^ length : Nat) : Real)
  change decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
      (E / Y) <=
    B *
      (A₁ * (P₁ ^ hybridResidualGrowth +
          P₁ * Z ^ (-hybridResidualHalfDecay)) +
        A₂ * (P₂ ^ hybridResidualGrowth +
          P₂ * Z ^ (-hybridResidualHalfDecay)))
  have hpowers := decimalHybridAuxiliaryPowers_data hscale
  change 10 ^ dAux <= 10 ^ dLength ∧
    10 ^ dLength <= 10 ^ loss * 10 ^ dAux ∧
    10 ^ eAux <= 10 ^ eLength ∧
    10 ^ eLength <= 10 ^ loss * 10 ^ eAux ∧
    10 ^ dAux * 10 ^ eAux <= 10 ^ length at hpowers
  have hDscale : ((10 ^ dLength : Nat) : Real) <=
      C * ((10 ^ dAux : Nat) : Real) := by
    dsimp [C]
    exact_mod_cast hpowers.2.1
  have hexponent : 10 ^ (dLength + eLength) <=
      10 ^ (length + loss) :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 10)).2 hscale
  have hDEYNat : 10 ^ eLength * 10 ^ dLength <=
      10 ^ loss * 10 ^ length := by
    simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hexponent
  have hDEY : E * ((10 ^ dLength : Nat) : Real) <= C * Y := by
    dsimp [C, E, Y]
    exact_mod_cast hDEYNat
  have houter := decimalHybridSquaredBlockSourceBandSum_le_power_residualSums
    digit (q₁ := q₁) (d := d) (k := dAux) (v := v) (u := u)
      (D := 10 ^ dLength) (Q₂ := Q₂) hq₁ hd hdD hdvd hq₁10
      (E := E) (Y := Y) (C := C) (K := C)
      (by dsimp [E]; positivity) (by dsimp [Y]; positivity)
      hDscale hDEY
  change decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
      (E / Y) <=
    A₁ *
        (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
          decimalHybridFirstSquaredResidualSum digit (q₁ * q₂) d dAux v
            (E / Y)) +
      A₂ *
        (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
          decimalHybridSecondSquaredResidualSum digit (q₁ * q₂) d dAux v
            (E / Y)) at houter
  have hfirst :=
    sum_decimalHybridFirstSquaredResidualSum_le_source_branches_coarse
      loss digit (length := length) (dLength := dLength)
        (eLength := eLength) (q₁ := q₁) (d := d) (Q₁ := Q₁) (Q₂ := Q₂)
        hscale hq₁ hd hQ₂ hq₁Upper
  change (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
      decimalHybridFirstSquaredResidualSum digit (q₁ * q₂) d dAux v
        (E / Y)) <=
    B * (P₁ ^ hybridResidualGrowth +
      P₁ * Z ^ (-hybridResidualHalfDecay)) at hfirst
  have hsecond :=
    sum_decimalHybridSecondSquaredResidualSum_le_source_branches_coarse
      loss digit (length := length) (dLength := dLength)
        (eLength := eLength) (q₁ := q₁) (d := d) (Q₁ := Q₁) (Q₂ := Q₂)
        hscale hq₁ hd hQ₂ hq₁Upper
  change (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
      decimalHybridSecondSquaredResidualSum digit (q₁ * q₂) d dAux v
        (E / Y)) <=
    B * (P₂ ^ hybridResidualGrowth +
      P₂ * Z ^ (-hybridResidualHalfDecay)) at hsecond
  have hA₁ : 0 <= A₁ := by
    dsimp [A₁, C, largeSieveSamplingConstant]
    positivity
  have hA₂ : 0 <= A₂ := by
    dsimp [A₂, C, largeSieveSamplingConstant]
    positivity
  calc
    decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
        (E / Y) <=
      A₁ *
          (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
            decimalHybridFirstSquaredResidualSum digit (q₁ * q₂) d dAux v
              (E / Y)) +
        A₂ *
          (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
            decimalHybridSecondSquaredResidualSum digit (q₁ * q₂) d dAux v
              (E / Y)) := houter
    _ <= A₁ * (B * (P₁ ^ hybridResidualGrowth +
          P₁ * Z ^ (-hybridResidualHalfDecay))) +
        A₂ * (B * (P₂ ^ hybridResidualGrowth +
          P₂ * Z ^ (-hybridResidualHalfDecay))) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hA₁)
        (mul_le_mul_of_nonneg_left hsecond hA₂)
    _ = B *
        (A₁ * (P₁ ^ hybridResidualGrowth +
            P₁ * Z ^ (-hybridResidualHalfDecay)) +
          A₂ * (P₂ ^ hybridResidualGrowth +
            P₂ * Z ^ (-hybridResidualHalfDecay))) := by ring

end

end PrimesRestrictedDigits
