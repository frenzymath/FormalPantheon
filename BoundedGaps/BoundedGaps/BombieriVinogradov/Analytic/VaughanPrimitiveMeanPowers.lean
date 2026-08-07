import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Power normalizations for the Vaughan primitive mean estimate

This file fixes the real cube- and sixth-root conventions used in the two
parameter choices after Akbary--Hambrook equation (6.15). It also owns the
power polynomial and logarithmic power in the equation-(1.1)-shaped bound.

Source: `AkbaryHambrook2013v2`, Theorem 1.2 and Section 6, printed pp. 23--24.
Semantic review: `SEM-460`.
-/

namespace BoundedGaps.Maynard

noncomputable section

/-- The nonnegative real cube root of a natural endpoint. -/
noncomputable def vaughanCubeRoot (x : ℕ) : ℝ :=
  Real.rpow (x : ℝ) (1 / 3 : ℝ)

/-- The nonnegative real sixth root of a natural endpoint. -/
noncomputable def vaughanSixthRoot (x : ℕ) : ℝ :=
  Real.rpow (x : ℝ) (1 / 6 : ℝ)

theorem vaughanCubeRoot_nonneg (x : ℕ) :
    0 ≤ vaughanCubeRoot x := by
  exact Real.rpow_nonneg (Nat.cast_nonneg x) _

theorem vaughanSixthRoot_nonneg (x : ℕ) :
    0 ≤ vaughanSixthRoot x := by
  exact Real.rpow_nonneg (Nat.cast_nonneg x) _

theorem vaughanCubeRoot_pos {x : ℕ} (hx : 1 ≤ x) :
    0 < vaughanCubeRoot x := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast (Nat.zero_lt_of_lt hx)

theorem vaughanSixthRoot_pos {x : ℕ} (hx : 1 ≤ x) :
    0 < vaughanSixthRoot x := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast (Nat.zero_lt_of_lt hx)

theorem one_le_vaughanCubeRoot {x : ℕ} (hx : 1 ≤ x) :
    1 ≤ vaughanCubeRoot x := by
  unfold vaughanCubeRoot
  apply Real.one_le_rpow
  · exact_mod_cast hx
  · norm_num

theorem one_le_vaughanSixthRoot {x : ℕ} (hx : 1 ≤ x) :
    1 ≤ vaughanSixthRoot x := by
  unfold vaughanSixthRoot
  apply Real.one_le_rpow
  · exact_mod_cast hx
  · norm_num

/-- Squaring the sixth root gives the cube root. -/
theorem vaughanSixthRoot_sq (x : ℕ) :
    vaughanSixthRoot x ^ 2 = vaughanCubeRoot x := by
  unfold vaughanSixthRoot vaughanCubeRoot
  calc
    Real.rpow (x : ℝ) (1 / 6 : ℝ) ^ 2 =
        Real.rpow (Real.rpow (x : ℝ) (1 / 6 : ℝ)) (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = Real.rpow (x : ℝ) ((1 / 6 : ℝ) * 2) :=
      (Real.rpow_mul (Nat.cast_nonneg x) (1 / 6 : ℝ) 2).symm
    _ = Real.rpow (x : ℝ) (1 / 3 : ℝ) := by norm_num

/-- Cubing the sixth root gives the ordinary nonnegative square root. -/
theorem vaughanSixthRoot_cube (x : ℕ) :
    vaughanSixthRoot x ^ 3 = Real.sqrt (x : ℝ) := by
  unfold vaughanSixthRoot
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (x : ℝ) (1 / 6 : ℝ) ^ 3 =
        Real.rpow (Real.rpow (x : ℝ) (1 / 6 : ℝ)) (3 : ℝ) :=
      (Real.rpow_natCast _ 3).symm
    _ = Real.rpow (x : ℝ) ((1 / 6 : ℝ) * 3) :=
      (Real.rpow_mul (Nat.cast_nonneg x) (1 / 6 : ℝ) 3).symm
    _ = Real.rpow (x : ℝ) (1 / 2 : ℝ) := by norm_num

/-- The sixth power of the sixth root recovers the natural endpoint. -/
theorem vaughanSixthRoot_pow_six (x : ℕ) :
    vaughanSixthRoot x ^ 6 = (x : ℝ) := by
  unfold vaughanSixthRoot
  calc
    Real.rpow (x : ℝ) (1 / 6 : ℝ) ^ 6 =
        Real.rpow (Real.rpow (x : ℝ) (1 / 6 : ℝ)) (6 : ℝ) :=
      (Real.rpow_natCast _ 6).symm
    _ = Real.rpow (x : ℝ) ((1 / 6 : ℝ) * 6) :=
      (Real.rpow_mul (Nat.cast_nonneg x) (1 / 6 : ℝ) 6).symm
    _ = (x : ℝ) := by norm_num [Real.rpow_one]

theorem vaughanSixthRoot_pow_four (x : ℕ) :
    vaughanSixthRoot x ^ 4 = vaughanCubeRoot x ^ 2 := by
  rw [show vaughanSixthRoot x ^ 4 = (vaughanSixthRoot x ^ 2) ^ 2 by ring,
    vaughanSixthRoot_sq]

theorem vaughanSixthRoot_pow_five (x : ℕ) :
    vaughanSixthRoot x ^ 5 =
      Real.sqrt (x : ℝ) * vaughanCubeRoot x := by
  rw [show vaughanSixthRoot x ^ 5 =
      vaughanSixthRoot x ^ 3 * vaughanSixthRoot x ^ 2 by ring,
    vaughanSixthRoot_cube, vaughanSixthRoot_sq]

theorem vaughanCubeRoot_cube (x : ℕ) :
    vaughanCubeRoot x ^ 3 = (x : ℝ) := by
  rw [← vaughanSixthRoot_sq]
  calc
    (vaughanSixthRoot x ^ 2) ^ 3 = vaughanSixthRoot x ^ 6 := by ring
    _ = (x : ℝ) := vaughanSixthRoot_pow_six x

theorem vaughanCubeRoot_le_sqrt {x : ℕ} (hx : 1 ≤ x) :
    vaughanCubeRoot x ≤ Real.sqrt (x : ℝ) := by
  rw [← vaughanSixthRoot_sq, ← vaughanSixthRoot_cube]
  nlinarith [one_le_vaughanSixthRoot hx,
    sq_nonneg (vaughanSixthRoot x),
    sq_nonneg (vaughanSixthRoot x - 1)]

theorem sqrt_natCast_le_vaughanCubeRoot_sq {x : ℕ} (hx : 1 ≤ x) :
    Real.sqrt (x : ℝ) ≤ vaughanCubeRoot x ^ 2 := by
  rw [← vaughanSixthRoot_cube, ← vaughanSixthRoot_pow_four]
  have hr := one_le_vaughanSixthRoot hx
  nlinarith [sq_nonneg (vaughanSixthRoot x),
    sq_nonneg (vaughanSixthRoot x - 1)]

/-- The high-range cutoff `x^(2/3)/q` is at least one throughout its source
range. -/
theorem one_le_vaughanPrimitiveMeanHighCutoff
    {x : ℕ} {q : ℝ} (hx : 4 ≤ x)
    (hq : vaughanCubeRoot x ≤ q)
    (hqsqrt : q ≤ Real.sqrt (x : ℝ)) :
    1 ≤ vaughanCubeRoot x ^ 2 / q := by
  have hcpos : 0 < vaughanCubeRoot x := vaughanCubeRoot_pos (by omega)
  have hqpos : 0 < q := hcpos.trans_le hq
  rw [le_div_iff₀ hqpos, one_mul]
  exact hqsqrt.trans (sqrt_natCast_le_vaughanCubeRoot_sq (by omega))

/-- The source polynomial
`4x + 2 sqrt(x) q^2 + 6 x^(2/3) q^(3/2) + 5 x^(5/6) q`. -/
noncomputable def vaughanPrimitiveMeanEquationOneOnePolynomial
    (x : ℕ) (q : ℝ) : ℝ :=
  4 * (x : ℝ) + 2 * Real.sqrt (x : ℝ) * q ^ 2 +
    6 * vaughanCubeRoot x ^ 2 * (q * Real.sqrt q) +
    5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) * q

theorem vaughanPrimitiveMeanEquationOneOnePolynomial_nonneg
    (x : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ vaughanPrimitiveMeanEquationOneOnePolynomial x q := by
  have hc := vaughanCubeRoot_nonneg x
  unfold vaughanPrimitiveMeanEquationOneOnePolynomial
  positivity

theorem vaughanPrimitiveMeanEquationOneOnePolynomial_mono
    (x : ℕ) {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) :
    vaughanPrimitiveMeanEquationOneOnePolynomial x q ≤
      vaughanPrimitiveMeanEquationOneOnePolynomial x r := by
  have hr : 0 ≤ r := hq.trans hqr
  have hsqrt : Real.sqrt q ≤ Real.sqrt r := Real.sqrt_le_sqrt hqr
  have hsq : q ^ 2 ≤ r ^ 2 := by nlinarith
  have hthreeHalves : q * Real.sqrt q ≤ r * Real.sqrt r :=
    mul_le_mul hqr hsqrt (Real.sqrt_nonneg q) hr
  have hc := vaughanCubeRoot_nonneg x
  unfold vaughanPrimitiveMeanEquationOneOnePolynomial
  gcongr

/-- The source factor `(log x)^(7/2)`, represented by integer powers and a
nonnegative square root. -/
noncomputable def vaughanPrimitiveMeanEquationOneOneLogPower
    (x : ℕ) : ℝ :=
  Real.log (x : ℝ) ^ 3 * Real.sqrt (Real.log (x : ℝ))

theorem vaughanPrimitiveMeanEquationOneOneLogPower_nonneg (x : ℕ) :
    0 ≤ vaughanPrimitiveMeanEquationOneOneLogPower x := by
  unfold vaughanPrimitiveMeanEquationOneOneLogPower
  positivity

theorem one_le_log_natCast {x : ℕ} (hx : 4 ≤ x) :
    1 ≤ Real.log (x : ℝ) := by
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  calc
    (1 : ℝ) ≤ 2 * Real.log 2 := by linarith
    _ = Real.log 4 := Real.log_four_eq.symm
    _ ≤ Real.log (x : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hx

theorem one_le_vaughanPrimitiveMeanEquationOneOneLogPower
    {x : ℕ} (hx : 4 ≤ x) :
    1 ≤ vaughanPrimitiveMeanEquationOneOneLogPower x := by
  have hlog := one_le_log_natCast hx
  unfold vaughanPrimitiveMeanEquationOneOneLogPower
  have hsqrt : 1 ≤ Real.sqrt (Real.log (x : ℝ)) :=
    Real.one_le_sqrt.mpr hlog
  have hcube : 1 ≤ Real.log (x : ℝ) ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog 3
  simpa only [one_mul] using
    mul_le_mul hcube hsqrt (by norm_num : (0 : ℝ) ≤ 1) (by linarith)

end

end BoundedGaps.Maynard
