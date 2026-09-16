import PrimesRestrictedDigits.Foundations.DecimalScale

/-!
# Decimal square-scale selection

This module selects the largest decimal square scale between two already feasible auxiliary
blocks in published Lemma 10.7.
-/

namespace PrimesRestrictedDigits

/-- Half the decimal exponent left between two feasible auxiliary blocks. -/
def decimalHybridSquareScaleLength
    (length dLength eLength : Nat) : Nat :=
  (length - (dLength + eLength)) / 2

theorem decimalPowers_mul_le_iff
    {length dLength eLength : Nat} :
    10 ^ dLength * 10 ^ eLength <= 10 ^ length ↔
      dLength + eLength <= length := by
  rw [← pow_add, Nat.pow_le_pow_iff_right (by norm_num : 1 < 10)]

theorem decimalHybridSquareScaleLength_spec
    {length dLength eLength : Nat}
    (hblocks : dLength + eLength <= length) :
    let v := decimalHybridSquareScaleLength length dLength eLength
    dLength + 2 * v + eLength <= length ∧
      (length = dLength + 2 * v + eLength ∨
        length = dLength + 2 * v + eLength + 1) := by
  dsimp only [decimalHybridSquareScaleLength]
  omega

theorem decimalHybridSquareScaleLength_isGreatest
    {length dLength eLength candidate : Nat}
    (hblocks : dLength + eLength <= length)
    (hfits : dLength + 2 * candidate + eLength <= length) :
    candidate <= decimalHybridSquareScaleLength length dLength eLength := by
  dsimp only [decimalHybridSquareScaleLength]
  omega

theorem decimalHybridSquareScale_power_data
    {length dLength eLength : Nat}
    (hblocks : dLength + eLength <= length) :
    let v := decimalHybridSquareScaleLength length dLength eLength
    10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2 <= 10 ^ length ∧
      10 ^ length <=
        10 * (10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2) ∧
      10 ^ length <
        10 ^ dLength * 10 ^ eLength * (10 ^ (v + 1)) ^ 2 := by
  let v := decimalHybridSquareScaleLength length dLength eLength
  change 10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2 <= 10 ^ length ∧
    10 ^ length <=
      10 * (10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2) ∧
    10 ^ length <
      10 ^ dLength * 10 ^ eLength * (10 ^ (v + 1)) ^ 2
  have hspec := decimalHybridSquareScaleLength_spec hblocks
  dsimp only at hspec
  have hnext : length < dLength + 2 * (v + 1) + eLength := by
    rcases hspec.2 with h | h <;> omega
  have hlo : 10 ^ (dLength + 2 * v + eLength) <= 10 ^ length :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 10)).2 hspec.1
  have hhi : 10 ^ length <= 10 ^ (dLength + 2 * v + eLength + 1) := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 10)).2
    rcases hspec.2 with h | h <;> omega
  have hmax : 10 ^ length < 10 ^ (dLength + 2 * (v + 1) + eLength) :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).2 hnext
  have hvpow : 10 ^ (2 * v) = (10 ^ v) ^ 2 := by
    rw [mul_comm, pow_mul]
  have hvnextpow : 10 ^ (2 * (v + 1)) = (10 ^ (v + 1)) ^ 2 := by
    rw [mul_comm, pow_mul]
  refine ⟨?_, ?_, ?_⟩
  · simpa [pow_add, hvpow, mul_comm, mul_left_comm, mul_assoc] using hlo
  · simpa [pow_add, hvpow, mul_comm, mul_left_comm, mul_assoc] using hhi
  · simpa [pow_add, hvnextpow, mul_comm, mul_left_comm, mul_assoc] using hmax

theorem decimalHybridSquareScale_power_eq_or_ten_mul
    {length dLength eLength : Nat}
    (hblocks : dLength + eLength <= length) :
    let v := decimalHybridSquareScaleLength length dLength eLength
    10 ^ length = 10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2 ∨
      10 ^ length =
        10 * (10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2) := by
  let v := decimalHybridSquareScaleLength length dLength eLength
  change 10 ^ length = 10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2 ∨
    10 ^ length = 10 * (10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2)
  rcases (decimalHybridSquareScaleLength_spec hblocks).2 with h | h
  · left
    rw [h, pow_add, pow_add]
    rw [show 10 ^ (2 * v) = (10 ^ v) ^ 2 by rw [mul_comm, pow_mul]]
    ring
  · right
    rw [h, pow_add, pow_add, pow_add]
    rw [show 10 ^ (2 * v) = (10 ^ v) ^ 2 by rw [mul_comm, pow_mul]]
    ring

theorem decimalHybridSquareScale_real_ratio
    {length dLength eLength : Nat}
    (hblocks : dLength + eLength <= length) :
    let v := decimalHybridSquareScaleLength length dLength eLength
    ((10 ^ eLength : Nat) : Real) <=
        ((10 ^ length : Nat) : Real) /
          (((10 ^ dLength : Nat) : Real) * ((10 ^ v : Nat) : Real) ^ 2) ∧
      ((10 ^ length : Nat) : Real) /
          (((10 ^ dLength : Nat) : Real) * ((10 ^ v : Nat) : Real) ^ 2) <=
        10 * ((10 ^ eLength : Nat) : Real) := by
  let v := decimalHybridSquareScaleLength length dLength eLength
  change ((10 ^ eLength : Nat) : Real) <=
      ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) * ((10 ^ v : Nat) : Real) ^ 2) ∧
    ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) * ((10 ^ v : Nat) : Real) ^ 2) <=
      10 * ((10 ^ eLength : Nat) : Real)
  have hdata := decimalHybridSquareScale_power_data hblocks
  change 10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2 <= 10 ^ length ∧
    10 ^ length <= 10 * (10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2) ∧
    10 ^ length <
      10 ^ dLength * 10 ^ eLength * (10 ^ (v + 1)) ^ 2 at hdata
  have hlowerNat :
      10 ^ eLength * (10 ^ dLength * (10 ^ v) ^ 2) <= 10 ^ length := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdata.1
  have hupperNat :
      10 ^ length <= 10 * 10 ^ eLength *
        (10 ^ dLength * (10 ^ v) ^ 2) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdata.2.1
  have hden :
      0 < ((10 ^ dLength : Nat) : Real) * ((10 ^ v : Nat) : Real) ^ 2 := by
    positivity
  constructor
  · apply (le_div_iff₀ hden).2
    exact_mod_cast hlowerNat
  · apply (div_le_iff₀ hden).2
    exact_mod_cast hupperNat

theorem decimalHybridSquareScale_real_square_ratio
    {length dLength eLength : Nat}
    (hblocks : dLength + eLength <= length) :
    let v := decimalHybridSquareScaleLength length dLength eLength
    ((10 ^ v : Nat) : Real) ^ 2 <=
        ((10 ^ length : Nat) : Real) /
          (((10 ^ dLength : Nat) : Real) *
            ((10 ^ eLength : Nat) : Real)) ∧
      ((10 ^ length : Nat) : Real) /
          (((10 ^ dLength : Nat) : Real) *
            ((10 ^ eLength : Nat) : Real)) <=
        10 * ((10 ^ v : Nat) : Real) ^ 2 := by
  let v := decimalHybridSquareScaleLength length dLength eLength
  change ((10 ^ v : Nat) : Real) ^ 2 <=
      ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real)) ∧
    ((10 ^ length : Nat) : Real) /
        (((10 ^ dLength : Nat) : Real) *
          ((10 ^ eLength : Nat) : Real)) <=
      10 * ((10 ^ v : Nat) : Real) ^ 2
  have hdata := decimalHybridSquareScale_power_data hblocks
  change 10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2 <= 10 ^ length ∧
    10 ^ length <= 10 * (10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2) ∧
    10 ^ length <
      10 ^ dLength * 10 ^ eLength * (10 ^ (v + 1)) ^ 2 at hdata
  have hden :
      0 < ((10 ^ dLength : Nat) : Real) *
        ((10 ^ eLength : Nat) : Real) := by
    positivity
  constructor
  · apply (le_div_iff₀ hden).2
    have hlowerNat :
        (10 ^ v) ^ 2 * (10 ^ dLength * 10 ^ eLength) <=
          10 ^ length := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdata.1
    exact_mod_cast hlowerNat
  · apply (div_le_iff₀ hden).2
    have hupperNat :
        10 ^ length <=
          (10 * (10 ^ v) ^ 2) * (10 ^ dLength * 10 ^ eLength) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdata.2.1
    exact_mod_cast hupperNat

theorem decimalHybridSquareScale_window_density
    {length dLength eLength : Nat}
    (hblocks : dLength + eLength <= length) :
    let v := decimalHybridSquareScaleLength length dLength eLength
    (((10 ^ dLength : Nat) : Real) * ((10 ^ eLength : Nat) : Real) *
        ((10 ^ v : Nat) : Real)) /
        ((10 ^ length : Nat) : Real) <=
      1 / ((10 ^ v : Nat) : Real) := by
  let v := decimalHybridSquareScaleLength length dLength eLength
  change (((10 ^ dLength : Nat) : Real) * ((10 ^ eLength : Nat) : Real) *
      ((10 ^ v : Nat) : Real)) /
      ((10 ^ length : Nat) : Real) <=
    1 / ((10 ^ v : Nat) : Real)
  have hdata := decimalHybridSquareScale_power_data hblocks
  change 10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2 <= 10 ^ length ∧
    10 ^ length <= 10 * (10 ^ dLength * 10 ^ eLength * (10 ^ v) ^ 2) ∧
    10 ^ length <
      10 ^ dLength * 10 ^ eLength * (10 ^ (v + 1)) ^ 2 at hdata
  have hY : (0 : Real) < (10 ^ length : Nat) := by positivity
  have hV : (0 : Real) < (10 ^ v : Nat) := by positivity
  rw [div_le_div_iff₀ hY hV]
  have hlowReal :
      ((10 ^ dLength : Nat) : Real) * ((10 ^ eLength : Nat) : Real) *
          ((10 ^ v : Nat) : Real) ^ 2 <=
        ((10 ^ length : Nat) : Real) := by
    exact_mod_cast hdata.1
  nlinarith

end PrimesRestrictedDigits
