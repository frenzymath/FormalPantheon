import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exceptional-zero exponential absorption

This file isolates the scalar real-power calculation in Davenport's
Siegel--Walfisz argument. A Siegel-shaped zero gap at a modulus bounded by a
power of `log x` forces the exceptional numerator `x ^ beta` below an
`exp (-c * sqrt (log x))` error.

It does not prove the zero gap, bound the source's additional `1 / beta`
factor, or assert Siegel--Walfisz.

Sources: `DavenportMNTCh21Siegel1980`, equations (4)--(5), and
`DavenportMNTCh22SW1980`, equations (1)--(3). Semantic review: `SEM-465`.
-/

namespace BoundedGaps.Maynard

/-- If `q <= L ^ D` and `epsilon = (2 * D)⁻¹`, then the negative
`epsilon`-power of `q` is at least the negative half-power of `L`. -/
theorem rpow_neg_half_le_modulus_rpow_neg
    {D L q : ℝ} (hD : 0 < D) (hL : 1 ≤ L)
    (hq : 1 ≤ q) (hqL : q ≤ L ^ D) :
    L ^ (-(1 / 2 : ℝ)) ≤ q ^ (-(2 * D)⁻¹) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hexponent : D * (-(2 * D)⁻¹) = -(1 / 2 : ℝ) := by
    field_simp
  calc
    L ^ (-(1 / 2 : ℝ)) = (L ^ D) ^ (-(2 * D)⁻¹) := by
      rw [← Real.rpow_mul hLpos.le, hexponent]
    _ ≤ q ^ (-(2 * D)⁻¹) := by
      apply Real.rpow_le_rpow_of_nonpos hqpos hqL
      exact neg_nonpos.mpr (inv_nonneg.mpr (mul_nonneg (by norm_num) hD.le))

/-- Davenport's scalar exceptional-zero absorption at logarithmic modulus.
The strict gap is the renamed/shrunk Chapter 22 form of the closed Chapter 21
Siegel gap. No further loss in `c` occurs in this calculation. -/
theorem exceptionalZeroPower_lt_exp_neg_sqrtLog
    {D c x q beta : ℝ} (hD : 0 < D) (hc : 0 < c)
    (hx : 0 < x) (hxlog : 1 ≤ Real.log x)
    (hq : 1 ≤ q) (hqlog : q ≤ Real.log x ^ D)
    (hbeta : beta < 1 - c * q ^ (-(2 * D)⁻¹)) :
    x ^ beta < x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  let L := Real.log x
  have hLpos : 0 < L := zero_lt_one.trans_le hxlog
  have hinvPower : L ^ (-(1 / 2 : ℝ)) ≤ q ^ (-(2 * D)⁻¹) :=
    rpow_neg_half_le_modulus_rpow_neg hD hxlog hq hqlog
  have hscaled : c * L ^ (-(1 / 2 : ℝ)) ≤ c * q ^ (-(2 * D)⁻¹) :=
    mul_le_mul_of_nonneg_left hinvPower hc.le
  have hgap : beta < 1 - c * L ^ (-(1 / 2 : ℝ)) := by
    linarith
  have hhalf : L * L ^ (-(1 / 2 : ℝ)) = Real.sqrt L := by
    calc
      L * L ^ (-(1 / 2 : ℝ)) = L ^ (1 : ℝ) * L ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = L ^ ((1 : ℝ) + -(1 / 2 : ℝ)) :=
        (Real.rpow_add hLpos (1 : ℝ) (-(1 / 2 : ℝ))).symm
      _ = L ^ (1 / 2 : ℝ) := by norm_num
      _ = Real.sqrt L := (Real.sqrt_eq_rpow L).symm
  have hlogGap : L * beta < L - c * Real.sqrt L := by
    calc
      L * beta < L * (1 - c * L ^ (-(1 / 2 : ℝ))) :=
        mul_lt_mul_of_pos_left hgap hLpos
      _ = L - c * Real.sqrt L := by
        rw [mul_sub, mul_one]
        calc
          L - L * (c * L ^ (-(1 / 2 : ℝ))) =
              L - c * (L * L ^ (-(1 / 2 : ℝ))) := by ring
          _ = L - c * Real.sqrt L := by rw [hhalf]
  rw [Real.rpow_def_of_pos hx, ← Real.exp_log hx, ← Real.exp_add]
  rw [Real.exp_lt_exp]
  simpa [L, sub_eq_add_neg] using hlogGap

end BoundedGaps.Maynard
