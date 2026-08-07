import BoundedGaps.BombieriVinogradov.Analytic.WeightedStatement
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Character orthogonality for weighted progression sums

This file implements the finite algebraic bridge reviewed in SEM-413. It
expresses a von Mangoldt progression sum as an average of complex character
twists. It contains no character-sum estimate or asymptotic theorem.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

/-- The positive natural-endpoint von Mangoldt sum twisted by `chi`. -/
noncomputable def twistedChebyshevSum
    (x q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The complete character kernel comparing the residues of `a` and `n`. -/
noncomputable def characterOrthogonalityKernel (q a n : ℕ) : ℂ :=
  ∑ χ : DirichletCharacter ℂ q,
    χ (a : ZMod q)⁻¹ * χ (n : ZMod q)

theorem characterOrthogonalityKernel_eq_of_coprime
    {q a n : ℕ} [NeZero q] (ha : Nat.Coprime a q) :
    characterOrthogonalityKernel q a n =
      if (a : ZMod q) = (n : ZMod q) then (q.totient : ℂ) else 0 := by
  unfold characterOrthogonalityKernel
  have hunit : IsUnit (a : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ha
  simpa using
    (DirichletCharacter.sum_char_inv_mul_char_eq ℂ hunit (n : ZMod q))

theorem characterOrthogonalityKernel_eq_mod_of_coprime
    {q a n : ℕ} [NeZero q] (ha : Nat.Coprime a q) :
    characterOrthogonalityKernel q a n =
      if a % q = n % q then (q.totient : ℂ) else 0 := by
  rw [characterOrthogonalityKernel_eq_of_coprime ha]
  congr 1
  simpa using (ZMod.natCast_eq_natCast_iff' a n q)

theorem inv_totient_mul_characterOrthogonalityKernel
    {q a n : ℕ} [NeZero q] (ha : Nat.Coprime a q) :
    (q.totient : ℂ)⁻¹ * characterOrthogonalityKernel q a n =
      if a % q = n % q then 1 else 0 := by
  rw [characterOrthogonalityKernel_eq_mod_of_coprime ha]
  split_ifs
  · rw [inv_mul_cancel₀]
    norm_num [Nat.totient_pos.mpr q.pos_of_neZero, NeZero.ne q]
  · simp

theorem chebyshevProgressionSum_complex_eq_character_average
    {x q a : ℕ} [NeZero q] (ha : Nat.Coprime a q) :
    (chebyshevProgressionSum x q a : ℂ) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * twistedChebyshevSum x q χ := by
  simp only [chebyshevProgressionSum, twistedChebyshevSum, Complex.ofReal_sum]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  change (if n % q = a % q then (ArithmeticFunction.vonMangoldt n : ℂ) else 0) =
    ((q.totient : ℂ)⁻¹ * characterOrthogonalityKernel q a n) *
      (ArithmeticFunction.vonMangoldt n : ℂ)
  rw [inv_totient_mul_characterOrthogonalityKernel ha]
  by_cases h : n % q = a % q
  · have h' : a % q = n % q := h.symm
    rw [if_pos h, if_pos h']
    simp
  · have h' : ¬a % q = n % q := fun h'' => h h''.symm
    rw [if_neg h, if_neg h']
    simp

end BoundedGaps.Maynard
