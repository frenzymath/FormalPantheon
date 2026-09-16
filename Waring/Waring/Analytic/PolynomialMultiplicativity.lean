import Waring.Analytic.PolynomialSums
import Waring.Analytic.CRTNormalization

/-!
# CRT factorization of polynomial complete sums

This file proves the exact normalized product formula underlying Chen's
Lemma 5 [CHEN1964-EN, pp. 1550-1551].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Complete sum of Chen's fifth-degree polynomial against an arbitrary
additive character. -/
noncomputable def polynomialSum {R : Type*} [Semiring R] [Fintype R]
    (character : AddChar R Complex) (a₀ a₁ a₂ a₃ a₄ : R) : Complex :=
  ∑ x : R, character (fifthPolynomial a₀ a₁ a₂ a₃ a₄ x)

/-- Polynomial complete sums on a product semiring factor through the two
restricted additive characters. -/
theorem polynomialSum_prod {R S : Type*} [Semiring R] [Semiring S]
    [Fintype R] [Fintype S] (character : AddChar (R × S) Complex)
    (a₀ a₁ a₂ a₃ a₄ : R) (b₀ b₁ b₂ b₃ b₄ : S) :
    polynomialSum character (a₀, b₀) (a₁, b₁) (a₂, b₂) (a₃, b₃) (a₄, b₄) =
      polynomialSum (AddChar.leftFactor character) a₀ a₁ a₂ a₃ a₄ *
        polynomialSum (AddChar.rightFactor character) b₀ b₁ b₂ b₃ b₄ := by
  rw [polynomialSum, Fintype.sum_prod_type, polynomialSum, polynomialSum,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simpa [fifthPolynomial, AddChar.leftFactor, AddChar.rightFactor] using
    character.map_add_eq_mul
      (fifthPolynomial a₀ a₁ a₂ a₃ a₄ x, 0)
      (0, fifthPolynomial b₀ b₁ b₂ b₃ b₄ y)

/-- Polynomial complete sums are invariant under transport across a ring
equivalence. -/
theorem polynomialSum_ringEquiv {R S : Type*} [Semiring R] [Semiring S]
    [Fintype R] [Fintype S] (equiv : R ≃+* S)
    (character : AddChar R Complex) (a₀ a₁ a₂ a₃ a₄ : R) :
    polynomialSum character a₀ a₁ a₂ a₃ a₄ =
      polynomialSum (AddChar.transport equiv.toAddEquiv character)
        (equiv a₀) (equiv a₁) (equiv a₂) (equiv a₃) (equiv a₄) := by
  rw [polynomialSum, polynomialSum, ← equiv.toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  simp [AddChar.transport, fifthPolynomial]

private lemma polynomialCompleteSum_eq_polynomialSum {q : Nat} [NeZero q]
    (a₀ a₁ a₂ a₃ a₄ : ZMod q) :
    polynomialCompleteSum a₀ a₁ a₂ a₃ a₄ =
      polynomialSum ZMod.stdAddChar a₀ a₁ a₂ a₃ a₄ := rfl

/-- Exact CRT factorization of the five-coefficient polynomial complete sum,
with the complementary modular inverses applied to every coefficient. -/
theorem polynomialCompleteSum_mul_standard {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (a₀ a₁ a₂ a₃ a₄ : ZMod (m * n)) :
    polynomialCompleteSum a₀ a₁ a₂ a₃ a₄ =
      polynomialCompleteSum
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a₀).1)
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a₁).1)
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a₂).1)
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a₃).1)
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a₄).1) *
        polynomialCompleteSum
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a₀).2)
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a₁).2)
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a₂).2)
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a₃).2)
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a₄).2) := by
  rw [polynomialCompleteSum_eq_polynomialSum]
  calc
    polynomialSum ZMod.stdAddChar a₀ a₁ a₂ a₃ a₄ =
        polynomialSum (chineseRemainderCharacter hcoprime)
          (ZMod.chineseRemainder hcoprime a₀)
          (ZMod.chineseRemainder hcoprime a₁)
          (ZMod.chineseRemainder hcoprime a₂)
          (ZMod.chineseRemainder hcoprime a₃)
          (ZMod.chineseRemainder hcoprime a₄) :=
      polynomialSum_ringEquiv (ZMod.chineseRemainder hcoprime)
        ZMod.stdAddChar a₀ a₁ a₂ a₃ a₄
    _ = polynomialSum (AddChar.leftFactor (chineseRemainderCharacter hcoprime))
          (ZMod.chineseRemainder hcoprime a₀).1
          (ZMod.chineseRemainder hcoprime a₁).1
          (ZMod.chineseRemainder hcoprime a₂).1
          (ZMod.chineseRemainder hcoprime a₃).1
          (ZMod.chineseRemainder hcoprime a₄).1 *
        polynomialSum (AddChar.rightFactor (chineseRemainderCharacter hcoprime))
          (ZMod.chineseRemainder hcoprime a₀).2
          (ZMod.chineseRemainder hcoprime a₁).2
          (ZMod.chineseRemainder hcoprime a₂).2
          (ZMod.chineseRemainder hcoprime a₃).2
          (ZMod.chineseRemainder hcoprime a₄).2 :=
      polynomialSum_prod (chineseRemainderCharacter hcoprime) _ _ _ _ _ _ _ _ _ _
    _ = _ := by
      apply congrArg₂ (fun x y : Complex ↦ x * y)
      · rw [polynomialSum, polynomialCompleteSum]
        apply Finset.sum_congr rfl
        intro x _
        rw [chineseRemainderCharacter_left_apply]
        apply congrArg ZMod.stdAddChar
        simp only [fifthPolynomial]
        ring
      · rw [polynomialSum, polynomialCompleteSum]
        apply Finset.sum_congr rfl
        intro x _
        rw [chineseRemainderCharacter_right_apply]
        apply congrArg ZMod.stdAddChar
        simp only [fifthPolynomial]
        ring

/-- The normalized CRT identity turns the norm of the composite-modulus sum
into the product of the two factor norms. -/
theorem norm_polynomialCompleteSum_mul_standard {m n : Nat}
    [NeZero m] [NeZero n] (hcoprime : m.Coprime n)
    (a₀ a₁ a₂ a₃ a₄ : ZMod (m * n)) :
    ‖polynomialCompleteSum a₀ a₁ a₂ a₃ a₄‖ =
      ‖polynomialCompleteSum
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a₀).1)
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a₁).1)
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a₂).1)
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a₃).1)
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a₄).1)‖ *
        ‖polynomialCompleteSum
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a₀).2)
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a₁).2)
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a₂).2)
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a₃).2)
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a₄).2)‖ := by
  rw [polynomialCompleteSum_mul_standard hcoprime, norm_mul]

end Waring.Analytic
