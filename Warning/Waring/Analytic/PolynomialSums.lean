import Waring.Analytic.ChenTwo

/-!
# Polynomial complete-sum interface

This file records the polynomial phase used in Chen's Lemma 4.  The general
Hua stationary-phase estimate remains a separate proof obligation; the
algebraic identities here are already kernel-checked.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Chen's degree-five polynomial with no constant term, evaluated in a
semiring. -/
def fifthPolynomial {R : Type*} [Semiring R] (a₀ a₁ a₂ a₃ a₄ x : R) : R :=
  a₀ * x ^ 5 + a₁ * x ^ 4 + a₂ * x ^ 3 + a₃ * x ^ 2 + a₄ * x

/-- Complete standard-character sum of Chen's degree-five polynomial. -/
noncomputable def polynomialCompleteSum {q : Nat} [NeZero q]
    (a₀ a₁ a₂ a₃ a₄ : ZMod q) : Complex :=
  ∑ x : ZMod q, ZMod.stdAddChar (fifthPolynomial a₀ a₁ a₂ a₃ a₄ x)

/-- Adding a constant to every phase multiplies the complete sum by one
character value. -/
theorem polynomialCompleteSum_add_constant {q : Nat} [NeZero q]
    (a₀ a₁ a₂ a₃ a₄ c : ZMod q) :
    (∑ x : ZMod q,
      ZMod.stdAddChar (fifthPolynomial a₀ a₁ a₂ a₃ a₄ x + c)) =
      ZMod.stdAddChar c *
        polynomialCompleteSum a₀ a₁ a₂ a₃ a₄ := by
  rw [polynomialCompleteSum]
  calc
    (∑ x : ZMod q,
        ZMod.stdAddChar (fifthPolynomial a₀ a₁ a₂ a₃ a₄ x + c)) =
        ∑ x : ZMod q,
          ZMod.stdAddChar (fifthPolynomial a₀ a₁ a₂ a₃ a₄ x) *
            ZMod.stdAddChar c := by
      apply Finset.sum_congr rfl
      intro x hx
      exact ZMod.stdAddChar.map_add_eq_mul _ _
    _ = ZMod.stdAddChar c *
        ∑ x : ZMod q,
          ZMod.stdAddChar (fifthPolynomial a₀ a₁ a₂ a₃ a₄ x) := by
      rw [← Finset.sum_mul]
      ring

/-- With all lower-degree coefficients zero, the polynomial phase is the
monomial phase used by the completed Lemma 2 estimate. -/
theorem polynomialCompleteSum_monomial {q : Nat} [NeZero q]
    (a : ZMod q) :
    polynomialCompleteSum a 0 0 0 0 = completePowerSum 5 a := by
  simp [polynomialCompleteSum, completePowerSum, powerSum, fifthPolynomial]

/-- The verified global Lemma 2 estimate applies to the monomial slice of
Chen's polynomial complete sum. -/
theorem chen_four_monomial_bound {q : Nat} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    ‖polynomialCompleteSum a 0 0 0 0‖ ≤
      40 * (q : Real) ^ (4 / 5 : Real) := by
  rw [polynomialCompleteSum_monomial]
  exact chen_two_completePowerSum_bound a ha

end Waring.Analytic
