import PrimesRestrictedDigits.Fourier.HybridResidualAssembly
import PrimesRestrictedDigits.Fourier.HybridResidualBranchReindex

/-!
# Residual Branch Bounds

This file applies the explicit equation (10.16) estimate to the source's literal `Sigma3'` and
`Sigma5'` residual sums. See `MAYNARD-PRD-PUBLISHED`, pp. 183--185.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- Coarse equation (10.16) bound for the first residual branch at its
smaller source window `D' * E / Y`. -/
theorem sum_decimalHybridFirstSquaredResidualSum_le_source_branches_coarse
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength q₁ d Q₁ Q₂ : Nat}
    (hscale : dLength + eLength <= length + loss)
    (hq₁ : 0 < q₁) (hd : 0 < d) (hQ₂ : 0 < Q₂)
    (hq₁Upper : q₁ <= Q₁) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    let d₁ := hybridDenominatorFirstFactor d (10 ^ dAux) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ dAux) (10 ^ v)
    let P : Real := (((d₁ * d₂) * Q₁ * Q₂ ^ 2 : Nat) : Real)
    let Z : Real :=
      ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real))
    (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
      decimalHybridFirstSquaredResidualSum digit (q₁ * q₂) d dAux v
        (((10 ^ eLength : Nat) : Real) /
          ((10 ^ length : Nat) : Real))) <=
      3600 * (1 + 2 * ((10 ^ loss : Nat) : Real)) *
        (P ^ hybridResidualGrowth +
          P * Z ^ (-hybridResidualHalfDecay)) := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  let d₁ := hybridDenominatorFirstFactor d (10 ^ dAux) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ dAux) (10 ^ v)
  let D' : Real := ((10 ^ dAux : Nat) : Real)
  let E : Real := ((10 ^ eLength : Nat) : Real)
  let V : Real := ((10 ^ v : Nat) : Real)
  let Y : Real := ((10 ^ length : Nat) : Real)
  let P : Real := (((d₁ * d₂) * Q₁ * Q₂ ^ 2 : Nat) : Real)
  let Z : Real :=
    ((10 ^ length : Nat) : Real) /
      (((10 ^ dLength : Nat) : Real) *
        ((10 ^ eLength : Nat) : Real))
  change (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
      decimalHybridFirstSquaredResidualSum digit (q₁ * q₂) d dAux v
        (E / Y)) <=
    3600 * (1 + 2 * ((10 ^ loss : Nat) : Real)) *
      (P ^ hybridResidualGrowth +
        P * Z ^ (-hybridResidualHalfDecay))
  rw [sum_decimalHybridFirstSquaredResidualSum_eq_hybridResidualReducedSourceSum]
  have hd₁ : 0 < d₁ := hybridDenominatorFirstFactor_pos hd
  have hd₂ : 0 < d₂ := hybridDenominatorSecondFactor_pos hd
  have hm : 0 < d₁ * d₂ := Nat.mul_pos hd₁ hd₂
  have hY : 0 < Y := by
    dsimp [Y]
    positivity
  have hVNat : 1 <= 10 ^ v := by
    exact one_le_pow₀ (by norm_num)
  have hV : (1 : Real) <= V := by
    dsimp [V]
    exact_mod_cast hVNat
  have hdelta : 0 <= D' * (E / Y) := by
    dsimp [D', E, Y]
    positivity
  have hdeltaUpper : D' * (E / Y) <= D' * E * V / Y := by
    rw [show D' * (E / Y) = D' * E / Y by ring]
    apply (div_le_div_iff_of_pos_right hY).2
    calc
      D' * E = D' * E * 1 := by ring
      _ <= D' * E * V :=
        mul_le_mul_of_nonneg_left hV (by positivity)
  have hbound := hybridResidualReducedSourceSum_le_source_branches_coarse
    loss digit (length := length) (dLength := dLength)
      (eLength := eLength) (m := d₁ * d₂) (q := q₁)
      (Q1 := Q₁) (Q2 := Q₂) (delta := D' * (E / Y))
      hscale hm hq₁ hQ₂ hq₁Upper hdelta (by
        simpa [D', E, V, Y, dAux, eAux, v] using hdeltaUpper)
  simpa [P, Z, dAux, eAux, v, d₁, d₂, D', E, V, Y] using hbound

/-- Coarse equation (10.16) bound for the second residual branch at the
common source window `D' * E * V / Y`. -/
theorem sum_decimalHybridSecondSquaredResidualSum_le_source_branches_coarse
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength q₁ d Q₁ Q₂ : Nat}
    (hscale : dLength + eLength <= length + loss)
    (hq₁ : 0 < q₁) (hd : 0 < d) (hQ₂ : 0 < Q₂)
    (hq₁Upper : q₁ <= Q₁) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    let d₁ := hybridDenominatorFirstFactor d (10 ^ dAux) (10 ^ v)
    let P : Real := ((d₁ * Q₁ * Q₂ ^ 2 : Nat) : Real)
    let Z : Real :=
      ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real))
    (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
      decimalHybridSecondSquaredResidualSum digit (q₁ * q₂) d dAux v
        (((10 ^ eLength : Nat) : Real) /
          ((10 ^ length : Nat) : Real))) <=
      3600 * (1 + 2 * ((10 ^ loss : Nat) : Real)) *
        (P ^ hybridResidualGrowth +
          P * Z ^ (-hybridResidualHalfDecay)) := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  let d₁ := hybridDenominatorFirstFactor d (10 ^ dAux) (10 ^ v)
  let D' : Real := ((10 ^ dAux : Nat) : Real)
  let E : Real := ((10 ^ eLength : Nat) : Real)
  let V : Real := ((10 ^ v : Nat) : Real)
  let Y : Real := ((10 ^ length : Nat) : Real)
  let P : Real := ((d₁ * Q₁ * Q₂ ^ 2 : Nat) : Real)
  let Z : Real :=
    ((10 ^ length : Nat) : Real) /
      (((10 ^ dLength : Nat) : Real) *
        ((10 ^ eLength : Nat) : Real))
  change (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
      decimalHybridSecondSquaredResidualSum digit (q₁ * q₂) d dAux v
        (E / Y)) <=
    3600 * (1 + 2 * ((10 ^ loss : Nat) : Real)) *
      (P ^ hybridResidualGrowth +
        P * Z ^ (-hybridResidualHalfDecay))
  rw [sum_decimalHybridSecondSquaredResidualSum_eq_hybridResidualReducedSourceSum]
  have hm : 0 < d₁ := hybridDenominatorFirstFactor_pos hd
  have hdelta : 0 <= (D' * V) * (E / Y) := by
    dsimp [D', E, V, Y]
    positivity
  have hdeltaUpper : (D' * V) * (E / Y) <= D' * E * V / Y := by
    exact le_of_eq (by ring)
  have hbound := hybridResidualReducedSourceSum_le_source_branches_coarse
    loss digit (length := length) (dLength := dLength)
      (eLength := eLength) (m := d₁) (q := q₁)
      (Q1 := Q₁) (Q2 := Q₂) (delta := (D' * V) * (E / Y))
      hscale hm hq₁ hQ₂ hq₁Upper hdelta (by
        simpa [D', E, V, Y, dAux, eAux, v] using hdeltaUpper)
  simpa [P, Z, dAux, eAux, v, d₁, D', E, V, Y,
    Nat.cast_mul] using hbound

end

end PrimesRestrictedDigits
