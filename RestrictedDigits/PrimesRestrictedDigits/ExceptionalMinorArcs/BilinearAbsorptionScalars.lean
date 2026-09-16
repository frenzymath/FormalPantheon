import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearEnergyAggregation
import Mathlib.Tactic.GCongr

/-!
# Scalar bounds for the bilinear energy estimate

These inequalities absorb the explicit scale counts and rational-radius losses in repaired
Lemma 13.1.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The fixed coefficient in the estimate
`(Q + E)^(s/5) <= 101^(s/5) X^(s/10)`. -/
noncomputable def bilinearRadiusAbsorptionConstant : Real :=
  (101 : Real) ^ (latticeSumSaving / 5)

theorem bilinearRadiusAbsorptionConstant_pos :
    0 < bilinearRadiusAbsorptionConstant := by
  unfold bilinearRadiusAbsorptionConstant
  positivity

/-- Positive decimal lengths are bounded by their natural logarithmic
scale. -/
theorem bilinear_length_cast_le_log_decimalScale
    {length : Nat} (hlength : 1 <= length) :
    (length : Real) <= Real.log (((10 ^ length : Nat) : Real)) := by
  have hlogTenOne : (1 : Real) < Real.log 10 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2
      (Real.exp_one_lt_three.trans_le (by norm_num))
  have hlengthNonneg : (0 : Real) <= length := by positivity
  have hmul : (length : Real) <= (length : Real) * Real.log 10 := by
    calc
      (length : Real) = (length : Real) * 1 := by ring
      _ <= (length : Real) * Real.log 10 :=
        mul_le_mul_of_nonneg_left hlogTenOne.le hlengthNonneg
  rw [Nat.cast_pow, Real.log_pow]
  exact hmul

/-- The number of energy cells is at most twice the logarithmic scale. -/
theorem bilinear_energyCellCount_cast_le_log
    {length : Nat} (hlength : 1 <= length) :
    ((length + 1 : Nat) : Real) <=
      2 * Real.log (((10 ^ length : Nat) : Real)) := by
  have hnat : length + 1 <= 2 * length := by omega
  have hreal : ((length + 1 : Nat) : Real) <= 2 * (length : Real) := by
    exact_mod_cast hnat
  have hlengthLog := bilinear_length_cast_le_log_decimalScale hlength
  linarith

/-- The `4*length+1` width count is at most five logarithmic factors. -/
theorem bilinear_layerCount_cast_le_log
    {length : Nat} (hlength : 1 <= length) :
    (bilinearLayerCount length : Real) <=
      5 * Real.log (((10 ^ length : Nat) : Real)) := by
  have hnat : bilinearLayerCount length <= 5 * length := by
    simp only [bilinearLayerCount]
    omega
  have hreal : (bilinearLayerCount length : Real) <=
      5 * (length : Real) := by
    exact_mod_cast hnat
  have hlengthLog := bilinear_length_cast_le_log_decimalScale hlength
  linarith

/-- At positive decimal length, the logarithmic scale is at least one. -/
theorem one_le_log_decimalScale
    {length : Nat} (hlength : 1 <= length) :
    (1 : Real) <= Real.log (((10 ^ length : Nat) : Real)) := by
  have hone : (1 : Real) <= (length : Real) := by exact_mod_cast hlength
  exact hone.trans (bilinear_length_cast_le_log_decimalScale hlength)

/-- The source assumptions imply the fixed rational-radius bound
`Q+E <= 101*sqrt X`. -/
theorem bilinear_rationalRadius_le_sqrt
    {X Q E : Real} (hQ : 1 <= Q) (hQUpper : Q <= Real.sqrt X)
    (_hE : 0 <= E) (hEUpper : E <= 100 * Real.sqrt X / Q) :
    Q + E <= 101 * Real.sqrt X := by
  have hQPos : 0 < Q := zero_lt_one.trans_le hQ
  have hnumerator : 0 <= 100 * Real.sqrt X := by positivity
  have hdiv : 100 * Real.sqrt X / Q <= 100 * Real.sqrt X := by
    apply (div_le_iff₀ hQPos).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ hnumerator
  linarith

/-- Raising the rational-radius bound to `s/5` costs at most `X^(s/10)`
and one fixed coefficient. -/
theorem bilinear_rationalRadius_rpow_le
    {X Q E : Real} (hX : 1 <= X)
    (hQ : 1 <= Q) (hQUpper : Q <= Real.sqrt X)
    (hE : 0 <= E) (hEUpper : E <= 100 * Real.sqrt X / Q) :
    (Q + E) ^ (latticeSumSaving / 5) <=
      bilinearRadiusAbsorptionConstant *
        X ^ (latticeSumSaving / 10) := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hRNonneg : 0 <= Q + E := by linarith
  have hRadius := bilinear_rationalRadius_le_sqrt hQ hQUpper hE hEUpper
  calc
    (Q + E) ^ (latticeSumSaving / 5) <=
        (101 * Real.sqrt X) ^ (latticeSumSaving / 5) := by
      exact Real.rpow_le_rpow hRNonneg hRadius
        (by positivity [latticeSumSaving_pos])
    _ = (101 : Real) ^ (latticeSumSaving / 5) *
        (Real.sqrt X) ^ (latticeSumSaving / 5) := by
      rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg X)]
    _ = bilinearRadiusAbsorptionConstant *
        X ^ (latticeSumSaving / 10) := by
      unfold bilinearRadiusAbsorptionConstant
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hXPos.le]
      congr 2
      ring

/-- A power saving in `X` absorbs the `s/5` rational-radius factor. -/
theorem bilinear_powerDecay_mul_radius_rpow_le
    {X R a : Real} (hX : 1 <= X)
    (ha : latticeSumSaving / 10 <= a)
    (hRpow : R ^ (latticeSumSaving / 5) <=
      bilinearRadiusAbsorptionConstant *
        X ^ (latticeSumSaving / 10)) :
    X ^ (1 - a) * R ^ (latticeSumSaving / 5) <=
      bilinearRadiusAbsorptionConstant * X := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hconstantNonneg : 0 <= bilinearRadiusAbsorptionConstant :=
    bilinearRadiusAbsorptionConstant_pos.le
  calc
    X ^ (1 - a) * R ^ (latticeSumSaving / 5) <=
        X ^ (1 - a) *
          (bilinearRadiusAbsorptionConstant *
            X ^ (latticeSumSaving / 10)) := by
      exact mul_le_mul_of_nonneg_left hRpow (Real.rpow_nonneg hXPos.le _)
    _ = bilinearRadiusAbsorptionConstant *
        X ^ (1 - a + latticeSumSaving / 10) := by
      rw [Real.rpow_add hXPos]
      ring
    _ <= bilinearRadiusAbsorptionConstant * X := by
      apply mul_le_mul_of_nonneg_left _ hconstantNonneg
      calc
        X ^ (1 - a + latticeSumSaving / 10) <= X ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hX (by linarith)
        _ = X := Real.rpow_one X

/-- The lattice denominator with exponent `s/4` is at least the common
denominator with exponent `s/5`. -/
theorem bilinear_radius_rpow_fifth_le_quarter
    {R : Real} (hR : 1 <= R) :
    R ^ (latticeSumSaving / 5) <=
      R ^ (latticeSumSaving / 4) := by
  exact Real.rpow_le_rpow_of_exponent_le hR
    (by nlinarith [latticeSumSaving_pos])

/-- Multiplying the lattice term by the common denominator cancels its
stronger `s/4` denominator. -/
theorem bilinear_latticeQuotient_mul_radius_rpow_le
    {C L X R : Real} (hC : 0 <= C) (hL : 0 <= L)
    (hX : 0 <= X) (hR : 1 <= R) :
    (C * L ^ 5 * X / R ^ (latticeSumSaving / 4)) *
        R ^ (latticeSumSaving / 5) <=
      C * L ^ 5 * X := by
  have hquarterPos : 0 < R ^ (latticeSumSaving / 4) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hR) _
  have hquotientNonneg :
      0 <= C * L ^ 5 * X / R ^ (latticeSumSaving / 4) := by
    positivity
  calc
    (C * L ^ 5 * X / R ^ (latticeSumSaving / 4)) *
        R ^ (latticeSumSaving / 5) <=
        (C * L ^ 5 * X / R ^ (latticeSumSaving / 4)) *
          R ^ (latticeSumSaving / 4) := by
      exact mul_le_mul_of_nonneg_left
        (bilinear_radius_rpow_fifth_le_quarter hR) hquotientNonneg
    _ = C * L ^ 5 * X := by
      field_simp

end

end PrimesRestrictedDigits
