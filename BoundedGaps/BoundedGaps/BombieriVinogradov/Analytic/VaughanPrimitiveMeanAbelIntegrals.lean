import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanPowers
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Scalar integrals for the Vaughan primitive mean Abel estimate

This file evaluates the polynomial integral in the partial-summation step of
Akbary--Hambrook's proof and records the resulting equation-(1.2) envelope.

Source: `AkbaryHambrook2013v2`, Section 7, printed p. 25. Semantic review:
`SEM-461`.
-/

namespace BoundedGaps.Maynard

open MeasureTheory
open scoped Interval

noncomputable section

/-- The exact upper-boundary-plus-integral polynomial before discarding the
two nonpositive lower-endpoint terms. -/
noncomputable def vaughanPrimitiveMeanAbelSharpPolynomial
    (x : ℕ) (Q1 Q : ℝ) : ℝ :=
  4 * (x : ℝ) / Q1 +
    4 * Real.sqrt (x : ℝ) * Q -
    2 * Real.sqrt (x : ℝ) * Q1 +
    18 * vaughanCubeRoot x ^ 2 * Real.sqrt Q -
    12 * vaughanCubeRoot x ^ 2 * Real.sqrt Q1 +
    5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) *
      (1 + Real.log (Q / Q1))

/-- The equation-(1.2)-shaped polynomial envelope after dropping the two
nonpositive lower-endpoint terms. -/
noncomputable def vaughanPrimitiveMeanAbelEnvelope
    (x : ℕ) (Q1 Q : ℝ) : ℝ :=
  4 * (x : ℝ) / Q1 +
    4 * Real.sqrt (x : ℝ) * Q +
    18 * vaughanCubeRoot x ^ 2 * Real.sqrt Q +
    5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) *
      Real.log (Real.exp 1 * Q / Q1)

private theorem zero_not_mem_uIcc {Q1 Q : ℝ}
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q) :
    (0 : ℝ) ∉ [[Q1, Q]] := by
  rw [Set.uIcc_of_le hQ]
  intro hzero
  linarith [hzero.1]

private theorem vaughanPrimitiveMeanPolynomial_div_sq_eq
    (x : ℕ) {t : ℝ} (ht : 0 < t) :
    vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2 =
      (4 * (x : ℝ)) * t ^ (-2 : ℝ) +
        2 * Real.sqrt (x : ℝ) +
        (6 * vaughanCubeRoot x ^ 2) * t ^ (-(1 / 2) : ℝ) +
        (5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x)) * t⁻¹ := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg ht.le,
    Real.rpow_two, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  unfold vaughanPrimitiveMeanEquationOneOnePolynomial
  have htne : t ≠ 0 := ne_of_gt ht
  have hsqrtne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  field_simp
  ring_nf
  rw [Real.sq_sqrt ht.le]
  ring

/-- The equation-(1.1) polynomial divided by `t^2` is integrable on every
positive compact interval used by partial summation. -/
theorem vaughanPrimitiveMeanPolynomial_div_sq_intervalIntegrable
    (x : ℕ) {Q1 Q : ℝ} (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q) :
    IntervalIntegrable
      (fun t ↦ vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2)
      volume Q1 Q := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · unfold vaughanPrimitiveMeanEquationOneOnePolynomial
    fun_prop
  · fun_prop
  · intro t ht
    rw [Set.uIcc_of_le hQ] at ht
    have htpos : 0 < t := zero_lt_one.trans_le (hQ1.trans ht.1)
    exact pow_ne_zero 2 htpos.ne'

/-- Direct evaluation of the scalar polynomial integral in the source's
partial-summation calculation. -/
theorem integral_vaughanPrimitiveMeanPolynomial_div_sq
    (x : ℕ) {Q1 Q : ℝ} (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q) :
    (∫ t in Set.Ioc Q1 Q,
      vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2) =
      4 * (x : ℝ) * (Q1⁻¹ - Q⁻¹) +
      2 * Real.sqrt (x : ℝ) * (Q - Q1) +
      12 * vaughanCubeRoot x ^ 2 *
        (Real.sqrt Q - Real.sqrt Q1) +
      5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) *
        Real.log (Q / Q1) := by
  have hQ1pos : 0 < Q1 := zero_lt_one.trans_le hQ1
  have hQpos : 0 < Q := hQ1pos.trans_le hQ
  have hzero : (0 : ℝ) ∉ [[Q1, Q]] := zero_not_mem_uIcc hQ1 hQ
  have hnegTwo : IntervalIntegrable (fun t : ℝ ↦ t ^ (-2 : ℝ)) volume Q1 Q :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have hnegHalf :
      IntervalIntegrable (fun t : ℝ ↦ t ^ (-(1 / 2) : ℝ)) volume Q1 Q :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hinv : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume Q1 Q :=
    intervalIntegral.intervalIntegrable_inv
      (fun t ht ↦ ne_of_mem_of_not_mem ht hzero) continuousOn_id
  have hfirst := hnegTwo.const_mul (4 * (x : ℝ))
  have hsecond : IntervalIntegrable
      (fun _ : ℝ ↦ 2 * Real.sqrt (x : ℝ)) volume Q1 Q :=
    intervalIntegrable_const
  have hthird := hnegHalf.const_mul (6 * vaughanCubeRoot x ^ 2)
  have hfourth := hinv.const_mul
    (5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x))
  have hnegTwoIntegral :
      (∫ t : ℝ in Q1..Q, t ^ (-2 : ℝ)) = Q1⁻¹ - Q⁻¹ := by
    rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
    norm_num [Real.rpow_neg_one]
    ring
  have hnegHalfIntegral :
      (∫ t : ℝ in Q1..Q, t ^ (-(1 / 2) : ℝ)) =
        2 * (Real.sqrt Q - Real.sqrt Q1) := by
    rw [integral_rpow (Or.inl (by norm_num))]
    norm_num
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    ring
  rw [← intervalIntegral.integral_of_le hQ]
  calc
    (∫ t : ℝ in Q1..Q,
        vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2) =
        ∫ t : ℝ in Q1..Q,
          (4 * (x : ℝ)) * t ^ (-2 : ℝ) +
            2 * Real.sqrt (x : ℝ) +
            (6 * vaughanCubeRoot x ^ 2) * t ^ (-(1 / 2) : ℝ) +
            (5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x)) * t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hQ] at ht
      exact vaughanPrimitiveMeanPolynomial_div_sq_eq x
        (zero_lt_one.trans_le (hQ1.trans ht.1))
    _ = 4 * (x : ℝ) * (Q1⁻¹ - Q⁻¹) +
        2 * Real.sqrt (x : ℝ) * (Q - Q1) +
        12 * vaughanCubeRoot x ^ 2 *
          (Real.sqrt Q - Real.sqrt Q1) +
        5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) *
          Real.log (Q / Q1) := by
      rw [intervalIntegral.integral_add ((hfirst.add hsecond).add hthird) hfourth,
        intervalIntegral.integral_add (hfirst.add hsecond) hthird,
        intervalIntegral.integral_add hfirst hsecond]
      simp only [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, hnegTwoIntegral, hnegHalfIntegral,
        integral_inv_of_pos hQ1pos hQpos, smul_eq_mul]
      ring

/-- Adding the polynomial's upper boundary to its integral gives the sharp
polynomial exactly. -/
theorem inv_mul_polynomial_add_integral_eq_abelSharp
    (x : ℕ) {Q1 Q : ℝ} (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q) :
    Q⁻¹ * vaughanPrimitiveMeanEquationOneOnePolynomial x Q +
        ∫ t in Set.Ioc Q1 Q,
          vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2 =
      vaughanPrimitiveMeanAbelSharpPolynomial x Q1 Q := by
  have hQ1pos : 0 < Q1 := zero_lt_one.trans_le hQ1
  have hQpos : 0 < Q := hQ1pos.trans_le hQ
  rw [integral_vaughanPrimitiveMeanPolynomial_div_sq x hQ1 hQ]
  unfold vaughanPrimitiveMeanEquationOneOnePolynomial
    vaughanPrimitiveMeanAbelSharpPolynomial
  field_simp [hQ1pos.ne', hQpos.ne']
  ring

private theorem abelEnvelope_log_eq
    {Q1 Q : ℝ} (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q) :
    Real.log (Real.exp 1 * Q / Q1) = 1 + Real.log (Q / Q1) := by
  have hQ1pos : 0 < Q1 := zero_lt_one.trans_le hQ1
  have hQpos : 0 < Q := hQ1pos.trans_le hQ
  rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero 1) hQpos.ne') hQ1pos.ne',
    Real.log_mul (Real.exp_ne_zero 1) hQpos.ne', Real.log_exp,
    Real.log_div hQpos.ne' hQ1pos.ne']
  ring

/-- The sharp polynomial is bounded by the equation-(1.2) envelope after
discarding its two nonpositive lower-endpoint terms. -/
theorem vaughanPrimitiveMeanAbelSharpPolynomial_le_envelope
    (x : ℕ) {Q1 Q : ℝ} (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q) :
    vaughanPrimitiveMeanAbelSharpPolynomial x Q1 Q ≤
      vaughanPrimitiveMeanAbelEnvelope x Q1 Q := by
  have hQ10 : 0 ≤ Q1 := zero_le_one.trans hQ1
  have hlowerSqrt :
      0 ≤ 2 * Real.sqrt (x : ℝ) * Q1 := by positivity
  have hlowerCube :
      0 ≤ 12 * vaughanCubeRoot x ^ 2 * Real.sqrt Q1 := by positivity
  unfold vaughanPrimitiveMeanAbelSharpPolynomial
    vaughanPrimitiveMeanAbelEnvelope
  rw [abelEnvelope_log_eq hQ1 hQ]
  linarith

/-- The upper polynomial boundary plus its integral is bounded by the
equation-(1.2) envelope. -/
theorem inv_mul_polynomial_add_integral_le_abelEnvelope
    (x : ℕ) {Q1 Q : ℝ} (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q) :
    Q⁻¹ * vaughanPrimitiveMeanEquationOneOnePolynomial x Q +
        ∫ t in Set.Ioc Q1 Q,
          vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2 ≤
      vaughanPrimitiveMeanAbelEnvelope x Q1 Q := by
  rw [inv_mul_polynomial_add_integral_eq_abelSharp x hQ1 hQ]
  exact vaughanPrimitiveMeanAbelSharpPolynomial_le_envelope x hQ1 hQ

/-- The equation-(1.2) envelope is nonnegative on its positive ordered
endpoint range. -/
theorem vaughanPrimitiveMeanAbelEnvelope_nonneg
    (x : ℕ) {Q1 Q : ℝ} (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q) :
    0 ≤ vaughanPrimitiveMeanAbelEnvelope x Q1 Q := by
  have hQ1pos : 0 < Q1 := zero_lt_one.trans_le hQ1
  have hQ0 : 0 ≤ Q := (zero_lt_one.trans_le hQ1).le.trans hQ
  have hratio : 1 ≤ Q / Q1 := by
    rw [le_div_iff₀ hQ1pos]
    simpa only [one_mul] using hQ
  have hlogRatio : 0 ≤ Real.log (Q / Q1) := Real.log_nonneg hratio
  have hcube : 0 ≤ vaughanCubeRoot x := vaughanCubeRoot_nonneg x
  unfold vaughanPrimitiveMeanAbelEnvelope
  rw [abelEnvelope_log_eq hQ1 hQ]
  positivity

end

end BoundedGaps.Maynard
