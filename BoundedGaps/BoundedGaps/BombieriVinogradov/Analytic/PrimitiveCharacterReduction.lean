import BoundedGaps.BombieriVinogradov.Analytic.CharacterOrthogonality
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Primitive-character restriction of finite twists

This file implements the finite conductor bridge reviewed in SEM-414. It
proves the original character vanishes on the non-coprime remainder and
identifies the primitive character's exact correction. It proves no bound for
that correction and no primitive-character mean-value estimate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

/-- A twisted von Mangoldt sum with support coprime to a specified modulus. -/
noncomputable def coprimeTwistedChebyshevSum
    (x q r : ℕ) (χ : DirichletCharacter ℂ r) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x with Nat.Coprime n q,
    χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

theorem dirichletCharacter_eq_primitiveCharacter_of_coprime
    {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hn : Nat.Coprime n q) :
    χ n = χ.primitiveCharacter n := by
  have hi : IsCoprime (n : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hn
  have h := χ.primitiveCharacter_apply_of_isCoprime hi
  simpa using h.symm

theorem twistedChebyshevSum_eq_coprime_add_nonCoprime
    (x q r : ℕ) (χ : DirichletCharacter ℂ r) :
    twistedChebyshevSum x r χ =
      coprimeTwistedChebyshevSum x q r χ +
        ∑ n ∈ Finset.Icc 1 x with ¬Nat.Coprime n q,
          χ n * (ArithmeticFunction.vonMangoldt n : ℂ) := by
  rw [twistedChebyshevSum, coprimeTwistedChebyshevSum]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem nonCoprimeTwistedChebyshevSum_eq_zero
    (x q : ℕ) (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc 1 x with ¬Nat.Coprime n q,
      χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hn_not_coprime : ¬Nat.Coprime n q := (Finset.mem_filter.mp hn).2
  have hn_nonunit : ¬IsUnit (n : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hn_not_coprime
  rw [MulChar.map_nonunit χ hn_nonunit, zero_mul]

theorem twistedChebyshevSum_eq_coprime
    (x q : ℕ) (χ : DirichletCharacter ℂ q) :
    twistedChebyshevSum x q χ = coprimeTwistedChebyshevSum x q q χ := by
  rw [twistedChebyshevSum_eq_coprime_add_nonCoprime,
    nonCoprimeTwistedChebyshevSum_eq_zero, add_zero]

theorem coprimeTwistedChebyshevSum_eq_primitive
    {x q : ℕ} (χ : DirichletCharacter ℂ q) :
    coprimeTwistedChebyshevSum x q q χ =
      coprimeTwistedChebyshevSum x q χ.conductor χ.primitiveCharacter := by
  unfold coprimeTwistedChebyshevSum
  apply Finset.sum_congr rfl
  intro n hn
  have hn_coprime : Nat.Coprime n q := (Finset.mem_filter.mp hn).2
  rw [dirichletCharacter_eq_primitiveCharacter_of_coprime χ hn_coprime]

theorem primitiveTwistedChebyshevSum_eq_add_correction
    (x q : ℕ) (χ : DirichletCharacter ℂ q) :
    twistedChebyshevSum x χ.conductor χ.primitiveCharacter =
      twistedChebyshevSum x q χ +
        ∑ n ∈ Finset.Icc 1 x with ¬Nat.Coprime n q,
          χ.primitiveCharacter n *
            (ArithmeticFunction.vonMangoldt n : ℂ) := by
  rw [twistedChebyshevSum_eq_coprime_add_nonCoprime]
  rw [← coprimeTwistedChebyshevSum_eq_primitive χ]
  rw [← twistedChebyshevSum_eq_coprime]

end BoundedGaps.Maynard
