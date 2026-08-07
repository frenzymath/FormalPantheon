import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Quadratic zeta-convolution coefficients at squares

For a square-principal Dirichlet character, every even prime-power
coefficient of `1 * chi` is at least one. Multiplicativity then gives the same
lower bound at every positive square.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 124, proof of
Theorem 12.8. Semantic review: `SEM-539`.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedGaps.Maynard

open ArithmeticFunction

/-- Even prime-power coefficients of `1 * chi` are at least one for a
square-principal character. -/
theorem one_le_zetaMul_prime_pow_two_mul
    {q p k : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hp : p.Prime) :
    (1 : ℂ) ≤ chi.zetaMul (p ^ (2 * k)) := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction,
    coe_zeta_mul_apply, coe_mk, Nat.sum_divisors_prime_pow hp,
    pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare p with h | h | h
  · simp [h]
  · simp [h]
    positivity
  · simp [h, neg_one_geom_sum]

/-- The coefficient of `1 * chi` at every positive square is at least one. -/
theorem one_le_zetaMul_sq
    {q n : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hn : n ≠ 0) :
    (1 : ℂ) ≤ chi.zetaMul (n ^ 2) := by
  rw [chi.isMultiplicative_zetaMul.multiplicative_factorization _
    (pow_ne_zero 2 hn)]
  refine Finset.one_le_prod fun p hp => ?_
  have hp' : p.Prime := by
    exact Nat.prime_of_mem_primeFactors (by simpa using hp)
  simpa [Nat.factorization_pow] using
    one_le_zetaMul_prime_pow_two_mul (chi := chi) hsquare hp'

end BoundedGaps.Maynard
