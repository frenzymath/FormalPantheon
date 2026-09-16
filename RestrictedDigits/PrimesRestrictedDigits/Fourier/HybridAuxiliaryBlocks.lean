import PrimesRestrictedDigits.Fourier.HybridSquareScale

/-!
# Auxiliary Decimal Blocks for the Hybrid Estimate

This file makes the comparison constants in the opening block choice of
Maynard's Lemma 10.7 explicit. See `MAYNARD-PRD-PUBLISHED`, pp. 180--181.
-/

namespace PrimesRestrictedDigits

/-- Keep as much of the source `D` block as fits below the total scale. -/
def decimalHybridAuxiliaryDLength (length dLength : Nat) : Nat :=
  min dLength length

/-- Keep as much of the source `E` block as fits after the auxiliary `D`. -/
def decimalHybridAuxiliaryELength
    (length dLength eLength : Nat) : Nat :=
  min eLength (length - decimalHybridAuxiliaryDLength length dLength)

theorem decimalHybridAuxiliaryLengths_spec
    {length dLength eLength loss : Nat}
    (hscale : dLength + eLength <= length + loss) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    dAux <= dLength ∧
      dLength <= dAux + loss ∧
      eAux <= eLength ∧
      eLength <= eAux + loss ∧
      dAux + eAux <= length := by
  dsimp only [decimalHybridAuxiliaryDLength,
    decimalHybridAuxiliaryELength]
  omega

theorem decimalHybridAuxiliaryLengths_eq_self
    {length dLength eLength : Nat}
    (hscale : dLength + eLength <= length) :
    decimalHybridAuxiliaryDLength length dLength = dLength ∧
      decimalHybridAuxiliaryELength length dLength eLength = eLength := by
  dsimp only [decimalHybridAuxiliaryDLength,
    decimalHybridAuxiliaryELength]
  omega

theorem decimalHybridAuxiliaryPowers_data
    {length dLength eLength loss : Nat}
    (hscale : dLength + eLength <= length + loss) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    10 ^ dAux <= 10 ^ dLength ∧
      10 ^ dLength <= 10 ^ loss * 10 ^ dAux ∧
      10 ^ eAux <= 10 ^ eLength ∧
      10 ^ eLength <= 10 ^ loss * 10 ^ eAux ∧
      10 ^ dAux * 10 ^ eAux <= 10 ^ length := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  change 10 ^ dAux <= 10 ^ dLength ∧
    10 ^ dLength <= 10 ^ loss * 10 ^ dAux ∧
    10 ^ eAux <= 10 ^ eLength ∧
    10 ^ eLength <= 10 ^ loss * 10 ^ eAux ∧
    10 ^ dAux * 10 ^ eAux <= 10 ^ length
  have hspec := decimalHybridAuxiliaryLengths_spec hscale
  dsimp only at hspec
  have hten : 1 < (10 : Nat) := by norm_num
  refine ⟨(Nat.pow_le_pow_iff_right hten).2 hspec.1, ?_,
    (Nat.pow_le_pow_iff_right hten).2 hspec.2.2.1, ?_, ?_⟩
  · have hpow := (Nat.pow_le_pow_iff_right hten).2
      (show dLength <= loss + dAux by omega)
    simpa [pow_add] using hpow
  · have hpow := (Nat.pow_le_pow_iff_right hten).2
      (show eLength <= loss + eAux by omega)
    simpa [pow_add] using hpow
  · exact decimalPowers_mul_le_iff.mpr hspec.2.2.2.2

theorem decimalHybridAuxiliary_residualWindowDensity
    {length dLength eLength loss r : Nat}
    (hscale : dLength + eLength <= length + loss)
    (hr : r <= decimalHybridSquareScaleLength length
      (decimalHybridAuxiliaryDLength length dLength)
      (decimalHybridAuxiliaryELength length dLength eLength)) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    ((((10 ^ dAux : Nat) : Real) * ((10 ^ eLength : Nat) : Real) *
          ((10 ^ v : Nat) : Real)) /
        ((10 ^ length : Nat) : Real)) *
        ((10 ^ r : Nat) : Real) <=
      ((10 ^ loss : Nat) : Real) := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  change ((((10 ^ dAux : Nat) : Real) * ((10 ^ eLength : Nat) : Real) *
        ((10 ^ v : Nat) : Real)) /
      ((10 ^ length : Nat) : Real)) *
      ((10 ^ r : Nat) : Real) <=
    ((10 ^ loss : Nat) : Real)
  have haux := decimalHybridAuxiliaryLengths_spec hscale
  change dAux <= dLength ∧ dLength <= dAux + loss ∧
    eAux <= eLength ∧ eLength <= eAux + loss ∧
    dAux + eAux <= length at haux
  have hv := decimalHybridSquareScaleLength_spec haux.2.2.2.2
  change dAux + 2 * v + eAux <= length ∧
    (length = dAux + 2 * v + eAux ∨
      length = dAux + 2 * v + eAux + 1) at hv
  have hexponent : dAux + eLength + v + r <= length + loss := by
    change r <= v at hr
    omega
  have hpower :
      10 ^ dAux * 10 ^ eLength * 10 ^ v * 10 ^ r <=
        10 ^ length * 10 ^ loss := by
    have hten : 1 < (10 : Nat) := by norm_num
    have hp := (Nat.pow_le_pow_iff_right hten).2 hexponent
    simpa [pow_add, mul_assoc] using hp
  have hpowerReal :
      ((10 ^ dAux : Nat) : Real) * ((10 ^ eLength : Nat) : Real) *
          ((10 ^ v : Nat) : Real) * ((10 ^ r : Nat) : Real) <=
        ((10 ^ length : Nat) : Real) * ((10 ^ loss : Nat) : Real) := by
    exact_mod_cast hpower
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : Real) < (10 ^ length : Nat))).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hpowerReal

end PrimesRestrictedDigits
