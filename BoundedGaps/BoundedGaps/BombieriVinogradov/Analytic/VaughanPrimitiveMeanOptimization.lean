import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanAlgebra
import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanLogOptimization

/-!
# Optimized Vaughan primitive mean majorants

This file combines the independently proved coefficient, algebraic, and
logarithmic comparisons in each of the two parameter regimes following
Akbary--Hambrook equation (6.15).

Source: `AkbaryHambrook2013v2`, Section 6, printed pp. 23--24. Semantic
review: `SEM-460`.
-/

namespace BoundedGaps.Maynard

noncomputable section

/-- The low-range cutoff `U=V=x^(1/3)` gives the common
equation-(1.1)-shaped majorant. -/
theorem vaughanPrimitiveMeanMajorant_low_le_equationOneOne
    {A : ℝ} (hA : 1 ≤ A) {x Q : ℕ} (hx : 4 ≤ x)
    (hQ : (Q : ℝ) ≤ vaughanCubeRoot x) :
    vaughanPrimitiveMeanMajorant
        A (vaughanCubeRoot x) (vaughanCubeRoot x) x Q ≤
      vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  have hx1 : 1 ≤ x := by omega
  have hc1 : 1 ≤ vaughanCubeRoot x := one_le_vaughanCubeRoot hx1
  have hcoefficient : 0 ≤ vaughanPrimitiveMeanCoefficient A :=
    vaughanPrimitiveMeanCoefficient_nonneg A
  have hscale : 0 ≤ vaughanPrimitiveMeanLogScale
      (vaughanCubeRoot x) (vaughanCubeRoot x) x :=
    vaughanPrimitiveMeanLogScale_nonneg _ _ _
  have hpolynomial : 0 ≤
      vaughanPrimitiveMeanEquationOneOnePolynomial x (Q : ℝ) :=
    vaughanPrimitiveMeanEquationOneOnePolynomial_nonneg x (by positivity)
  have hlogPower : 0 ≤ vaughanPrimitiveMeanEquationOneOneLogPower x :=
    vaughanPrimitiveMeanEquationOneOneLogPower_nonneg x
  have halgebraic :=
    vaughanPrimitiveMeanAlgebraicScale_low_le_polynomial
      hx (by positivity : (0 : ℝ) ≤ Q) hQ
  have hlog := vaughanPrimitiveMeanLogScale_low_le hx
  have hlogCoefficient :=
    vaughanPrimitiveMeanLowLogCoefficient_le_high
  calc
    vaughanPrimitiveMeanMajorant
        A (vaughanCubeRoot x) (vaughanCubeRoot x) x Q ≤
        vaughanPrimitiveMeanCoefficient A *
          vaughanPrimitiveMeanAlgebraicScale
            (vaughanCubeRoot x) (vaughanCubeRoot x) x (Q : ℝ) *
          vaughanPrimitiveMeanLogScale
            (vaughanCubeRoot x) (vaughanCubeRoot x) x :=
      vaughanPrimitiveMeanMajorant_le_coefficient_mul_scales
        hA hx hc1 hc1
    _ ≤ vaughanPrimitiveMeanCoefficient A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          vaughanPrimitiveMeanLogScale
            (vaughanCubeRoot x) (vaughanCubeRoot x) x := by
      apply mul_le_mul_of_nonneg_right _ hscale
      exact mul_le_mul_of_nonneg_left halgebraic hcoefficient
    _ ≤ vaughanPrimitiveMeanCoefficient A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          (vaughanPrimitiveMeanLowLogCoefficient *
            vaughanPrimitiveMeanEquationOneOneLogPower x) := by
      exact mul_le_mul_of_nonneg_left hlog
        (mul_nonneg hcoefficient hpolynomial)
    _ ≤ vaughanPrimitiveMeanCoefficient A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          (vaughanPrimitiveMeanHighLogCoefficient *
            vaughanPrimitiveMeanEquationOneOneLogPower x) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg hcoefficient hpolynomial)
      exact mul_le_mul_of_nonneg_right hlogCoefficient hlogPower
    _ = vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
      unfold vaughanPrimitiveMeanEquationOneOneConstant
      ring

/-- The high-range cutoff `U=V=x^(2/3)/Q` gives the same common
equation-(1.1)-shaped majorant. -/
theorem vaughanPrimitiveMeanMajorant_high_le_equationOneOne
    {A : ℝ} (hA : 1 ≤ A) {x Q : ℕ} (hx : 4 ≤ x)
    (hQ : vaughanCubeRoot x ≤ (Q : ℝ))
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    vaughanPrimitiveMeanMajorant
        A (vaughanCubeRoot x ^ 2 / (Q : ℝ))
          (vaughanCubeRoot x ^ 2 / (Q : ℝ)) x Q ≤
      vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  let U : ℝ := vaughanCubeRoot x ^ 2 / (Q : ℝ)
  have hU : 1 ≤ U :=
    one_le_vaughanPrimitiveMeanHighCutoff hx hQ hQsqrt
  have hcoefficient : 0 ≤ vaughanPrimitiveMeanCoefficient A :=
    vaughanPrimitiveMeanCoefficient_nonneg A
  have hscale : 0 ≤ vaughanPrimitiveMeanLogScale U U x :=
    vaughanPrimitiveMeanLogScale_nonneg _ _ _
  have hpolynomial : 0 ≤
      vaughanPrimitiveMeanEquationOneOnePolynomial x (Q : ℝ) :=
    vaughanPrimitiveMeanEquationOneOnePolynomial_nonneg x (by positivity)
  have halgebraic :=
    vaughanPrimitiveMeanAlgebraicScale_high_le_polynomial hx hQ hQsqrt
  have hlog := vaughanPrimitiveMeanLogScale_high_le hx hQ hQsqrt
  calc
    vaughanPrimitiveMeanMajorant A U U x Q ≤
        vaughanPrimitiveMeanCoefficient A *
          vaughanPrimitiveMeanAlgebraicScale U U x (Q : ℝ) *
          vaughanPrimitiveMeanLogScale U U x :=
      vaughanPrimitiveMeanMajorant_le_coefficient_mul_scales
        hA hx hU hU
    _ ≤ vaughanPrimitiveMeanCoefficient A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          vaughanPrimitiveMeanLogScale U U x := by
      apply mul_le_mul_of_nonneg_right _ hscale
      exact mul_le_mul_of_nonneg_left halgebraic hcoefficient
    _ ≤ vaughanPrimitiveMeanCoefficient A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          (vaughanPrimitiveMeanHighLogCoefficient *
            vaughanPrimitiveMeanEquationOneOneLogPower x) := by
      exact mul_le_mul_of_nonneg_left hlog
        (mul_nonneg hcoefficient hpolynomial)
    _ = vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
      unfold vaughanPrimitiveMeanEquationOneOneConstant
      ring

end

end BoundedGaps.Maynard
