import PrimesRestrictedDigits.LatticeEstimates.FinalSourceBounds

/-!
# Decimal scales for the final lattice estimate

These two bridges convert the source's decimal-power scale assumptions and the exact `S2`
hybrid scale into the scalar forms.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem finalSourceLengthBudget
    {loss length d0Length d1Length eLength : Nat} {P : Real}
    (hP : 1 <= P)
    (hscale :
      (((10 ^ eLength) *
        ((10 ^ d0Length) * (10 ^ d1Length)) : Nat) : Real) <=
        ((10 ^ loss : Nat) : Real) *
          ((10 ^ length : Nat) : Real) / P) :
    d0Length + d1Length + eLength <= length + loss := by
  have hscale' :
      (((10 ^ eLength) *
        ((10 ^ d0Length) * (10 ^ d1Length)) : Nat) : Real) <=
        ((10 ^ loss : Nat) : Real) *
          ((10 ^ length : Nat) : Real) := by
    calc
      (((10 ^ eLength) *
          ((10 ^ d0Length) * (10 ^ d1Length)) : Nat) : Real) <=
          ((10 ^ loss : Nat) : Real) *
            ((10 ^ length : Nat) : Real) / P := hscale
      _ <= ((10 ^ loss : Nat) : Real) *
          ((10 ^ length : Nat) : Real) := by
        apply (div_le_iff₀ (Real.zero_lt_one.trans_le hP)).2
        nlinarith [show 0 <= ((10 ^ loss : Nat) : Real) *
          ((10 ^ length : Nat) : Real) by positivity]
  have hpowProduct :
      10 ^ eLength * (10 ^ d0Length * 10 ^ d1Length) <=
        10 ^ loss * 10 ^ length := by
    exact_mod_cast hscale'
  have hpow :
      10 ^ (d0Length + d1Length + eLength) <=
        10 ^ (length + loss) := by
    simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using hpowProduct
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 10)).1 hpow

theorem finalSourceSTwoTarget_le
    {length Q1 G1 G2 D0 D1 E0 : Nat}
    (hQ1 : 0 < Q1) (hG1 : 0 < G1) (hG2 : 0 < G2)
    (hD0 : 0 < D0) (hD1 : 0 < D1) :
    let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
    latticeHybridTarget length
        (((D0 * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) * E0) <=
      (((Q0 : Real) ^ 2 * E0 /
          ((D0 : Real) * (D1 : Real) ^ 2 * (G1 : Real) ^ 2)) ^
            largeSieveAlpha +
        (Q0 : Real) ^ 2 * E0 /
          ((D0 : Real) * D1 * G1 *
            (((10 ^ length : Nat) : Real) ^ largeSieveSigma))) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
  let T : Real := (((D0 * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) * E0)
  have hX : 0 < X := by positivity
  have hfullDen : 0 < (D0 : Real) * D1 ^ 2 * G1 ^ 2 := by positivity
  have hsmallDen : 0 < (D0 : Real) * D1 * G1 := by positivity
  have hfactor : 1 <= (D1 : Real) * G1 := by
    have hD1One : (1 : Real) <= D1 := by exact_mod_cast hD1
    have hG1One : (1 : Real) <= G1 := by exact_mod_cast hG1
    calc
      (1 : Real) <= G1 := hG1One
      _ = 1 * G1 := by ring
      _ <= (D1 : Real) * G1 :=
        mul_le_mul_of_nonneg_right hD1One (by positivity)
  have hTExact :
      T = (Q0 : Real) ^ 2 * E0 /
        ((D0 : Real) * D1 ^ 2 * G1 ^ 2) := by
    dsimp only [T, Q0]
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    field_simp
  have hTCoarse :
      T <= (Q0 : Real) ^ 2 * E0 / ((D0 : Real) * D1 * G1) := by
    rw [hTExact]
    have hnum : 0 <= (Q0 : Real) ^ 2 * E0 := by positivity
    have hdenFactor :
        (D0 : Real) * D1 * G1 <= (D0 : Real) * D1 ^ 2 * G1 ^ 2 := by
      calc
        (D0 : Real) * D1 * G1 = (D0 : Real) * ((D1 : Real) * G1) := by ring
        _ <= (D0 : Real) * (((D1 : Real) * G1) * ((D1 : Real) * G1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hfactor (by positivity : 0 <= (D1 : Real) * G1)
        _ = (D0 : Real) * D1 ^ 2 * G1 ^ 2 := by ring
    exact div_le_div_of_nonneg_left hnum hsmallDen hdenFactor
  unfold latticeHybridTarget
  change T ^ largeSieveAlpha + T * X ^ (-largeSieveSigma) <= _
  apply add_le_add
  · rw [hTExact]
  · rw [Real.rpow_neg hX.le]
    calc
      T * (X ^ largeSieveSigma)⁻¹ <=
          ((Q0 : Real) ^ 2 * E0 / ((D0 : Real) * D1 * G1)) *
            (X ^ largeSieveSigma)⁻¹ := by gcongr
      _ = (Q0 : Real) ^ 2 * E0 /
          ((D0 : Real) * D1 * G1 * X ^ largeSieveSigma) := by ring

end

end PrimesRestrictedDigits
