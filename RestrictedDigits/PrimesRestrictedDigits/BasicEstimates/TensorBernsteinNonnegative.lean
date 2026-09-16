import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic.NormNum

/-!
# Nonnegative tensor Bernstein polynomials

This file proves nonnegativity on the real unit square for tensor Bernstein
polynomials with nonnegative rational coefficients.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private noncomputable def bernsteinEval (n i : Nat) (x : Real) : Real :=
  (bernsteinPolynomial Real n i).eval x

private theorem bernsteinEval_nonneg {n i : Nat} {x : Real}
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    0 <= bernsteinEval n i x := by
  rw [bernsteinEval, bernsteinPolynomial]
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

private noncomputable def tensorBernsteinEval
    (n m : Nat) (coefficient : Nat -> Nat -> Rat) (x y : Real) : Real :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
    (coefficient i j : Real) * bernsteinEval n i x * bernsteinEval m j y

private theorem tensorBernsteinEval_nonneg
    {n m : Nat} {coefficient : Nat -> Nat -> Rat} {x y : Real}
    (hcoefficient : ∀ i ≤ n, ∀ j ≤ m, 0 <= coefficient i j)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1) :
    0 <= tensorBernsteinEval n m coefficient x y := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  have hcoefficientReal : (0 : Real) <= coefficient i j := by
    exact_mod_cast hcoefficient i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  exact mul_nonneg
    (mul_nonneg
      hcoefficientReal
      (bernsteinEval_nonneg (n := n) (i := i) hx0 hx1))
    (bernsteinEval_nonneg (n := m) (i := j) hy0 hy1)

/-- The tensor Bernstein sum as a polynomial in the second variable, with
polynomials in the first variable as coefficients. -/
noncomputable def tensorBernsteinPolynomial
    (n m : Nat) (coefficient : Nat -> Nat -> Rat) :
    Polynomial (Polynomial Rat) :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
    Polynomial.C
        (Polynomial.C (coefficient i j) *
          bernsteinPolynomial Rat n i) *
      bernsteinPolynomial (Polynomial Rat) m j

private theorem eval₂_tensorBernsteinPolynomial
    (n m : Nat) (coefficient : Nat -> Nat -> Rat) (x y : Real) :
    Polynomial.eval₂
        (Polynomial.eval₂RingHom (algebraMap Rat Real) x) y
        (tensorBernsteinPolynomial n m coefficient) =
      tensorBernsteinEval n m coefficient x y := by
  rw [tensorBernsteinPolynomial, tensorBernsteinEval]
  simp_rw [Polynomial.eval₂_finsetSum]
  simp [bernsteinEval, bernsteinPolynomial, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, mul_assoc]

/-- A tensor Bernstein polynomial with nonnegative rational coefficients is
nonnegative on the real unit square. -/
theorem tensorBernsteinPolynomial_eval₂_nonneg
    {n m : Nat} {coefficient : Nat -> Nat -> Rat} {x y : Real}
    (hcoefficient : ∀ i ≤ n, ∀ j ≤ m, 0 <= coefficient i j)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1) :
    0 <= Polynomial.eval₂
      (Polynomial.eval₂RingHom (algebraMap Rat Real) x) y
      (tensorBernsteinPolynomial n m coefficient) := by
  rw [eval₂_tensorBernsteinPolynomial]
  exact tensorBernsteinEval_nonneg hcoefficient hx0 hx1 hy0 hy1

end PrimesRestrictedDigits
