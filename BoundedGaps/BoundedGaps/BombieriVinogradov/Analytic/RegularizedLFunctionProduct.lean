import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Regularized product of Dirichlet L-functions

The pointwise product over all Dirichlet characters has a principal factor
whose analytic continuation has a pole at one. Replacing that factor by
Mathlib's pole-removed entire function gives an entire finite product. Away
from one, the regularized product is exactly `(s - 1)` times the pointwise
product; at one, it is nonzero.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110,
equation (11.2), and printed p. 119, Theorem 12.3. Nonvanishing at one uses
the stronger pinned-Mathlib theorem for every nonprincipal character.
Semantic review: `SEM-493`.
-/

noncomputable section

open scoped Classical

namespace BoundedGaps.Maynard

/-- Koukoulopoulos's pointwise product over all characters modulo `q`. -/
noncomputable def dirichletLFunctionProduct
    (q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  ∏ chi : DirichletCharacter ℂ q,
    DirichletCharacter.LFunction chi s

/-- The all-character product with its principal pole removed. -/
noncomputable def regularizedDirichletLFunctionProduct
    (q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ q s *
    ∏ chi ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      DirichletCharacter.LFunction chi s

/-- The regularized all-character product is entire. -/
theorem differentiable_regularizedDirichletLFunctionProduct
    (q : ℕ) [NeZero q] :
    Differentiable ℂ (regularizedDirichletLFunctionProduct q) := by
  apply (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).mul
  apply Differentiable.fun_finsetProd
  intro chi hchi
  exact DirichletCharacter.differentiable_LFunction
    (Finset.ne_of_mem_erase hchi)

/-- Away from the pole, regularization is multiplication by `s - 1`. -/
theorem regularizedDirichletLFunctionProduct_eq_sub_one_mul_of_ne_one
    (q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    regularizedDirichletLFunctionProduct q s =
      (s - 1) * dirichletLFunctionProduct q s := by
  rw [regularizedDirichletLFunctionProduct,
    DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
    dirichletLFunctionProduct]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun chi : DirichletCharacter ℂ q =>
      DirichletCharacter.LFunction chi s)
    (Finset.mem_univ (1 : DirichletCharacter ℂ q))]
  ring

/-- The regularized product is nonzero at one. -/
theorem regularizedDirichletLFunctionProduct_apply_one_ne_zero
    (q : ℕ) [NeZero q] :
    regularizedDirichletLFunctionProduct q 1 ≠ 0 := by
  rw [regularizedDirichletLFunctionProduct, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff]
  refine ⟨DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q, ?_⟩
  intro chi hchi
  exact DirichletCharacter.LFunction_apply_one_ne_zero
    (Finset.ne_of_mem_erase hchi)

/-- Zeros of the regularized product are exactly constituent zeros away from
the principal pole. -/
theorem regularizedDirichletLFunctionProduct_eq_zero_iff
    (q : ℕ) [NeZero q] (rho : ℂ) :
    regularizedDirichletLFunctionProduct q rho = 0 ↔
      rho ≠ 1 ∧
        ∃ chi : DirichletCharacter ℂ q,
          DirichletCharacter.LFunction chi rho = 0 := by
  constructor
  · intro hzero
    have hrho : rho ≠ 1 := by
      intro h
      subst rho
      exact regularizedDirichletLFunctionProduct_apply_one_ne_zero q hzero
    have hproduct : dirichletLFunctionProduct q rho = 0 := by
      rw [regularizedDirichletLFunctionProduct_eq_sub_one_mul_of_ne_one q hrho,
        mul_eq_zero] at hzero
      exact hzero.resolve_left (sub_ne_zero.mpr hrho)
    unfold dirichletLFunctionProduct at hproduct
    rw [Finset.prod_eq_zero_iff] at hproduct
    obtain ⟨chi, _, hchi⟩ := hproduct
    exact ⟨hrho, chi, hchi⟩
  · rintro ⟨hrho, chi, hchi⟩
    rw [regularizedDirichletLFunctionProduct_eq_sub_one_mul_of_ne_one q hrho]
    have hproduct : dirichletLFunctionProduct q rho = 0 := by
      unfold dirichletLFunctionProduct
      exact Finset.prod_eq_zero (Finset.mem_univ chi) hchi
    rw [hproduct, mul_zero]

end BoundedGaps.Maynard
