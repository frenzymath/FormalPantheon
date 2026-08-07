import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.MulChar.Lemmas
import BoundedGaps.BombieriVinogradov.Analytic.ImprimitiveLFunctionTransport

/-!
# Conjugation symmetry of Dirichlet L-functions

Complex conjugation exchanges the L-functions of a nonprincipal character
and its inverse. For a character whose square is principal, this gives the
conjugate-pair symmetry used in the real-character branch of the classical
zero-free region.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 110 and
119--121, especially the conjugate-zero step on p. 121. Independent
comparison: `ElkiesM229NearlyZeroFree2018`, p. 3. Semantic review: `SEM-485`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Filter
open scoped ComplexConjugate Topology

private lemma conj_LSeries_conj_eq_inv
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    conj (LSeries (chi ·) (conj s)) = LSeries (chi⁻¹ ·) s := by
  rw [LSeries, conj_tsum, LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      map_div₀]
    have hcoeff : (starRingEnd ℂ) (chi n) = chi⁻¹ n := by
      change star (chi n) = chi⁻¹ n
      exact MulChar.star_apply' chi n
    rw [hcoeff]
    congr 1
    rw [← Complex.conj_cpow (n : ℂ) s (by
      rw [Complex.natCast_arg]
      exact ne_of_eq_of_ne rfl Real.pi_ne_zero.symm),
      Complex.conj_natCast]

/-- Analytic continuation preserves the conjugation identity between a
character and its inverse. -/
theorem LFunction_inv_conj
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction chi⁻¹ (conj s) =
      conj (DirichletCharacter.LFunction chi s) := by
  have hinvAnalytic : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunction chi⁻¹) Set.univ :=
    DifferentiableOn.analyticOnNhd
      (DirichletCharacter.differentiable_LFunction
        (inv_ne_one.mpr hchi)).differentiableOn isOpen_univ
  have hconjAnalytic : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        conj (DirichletCharacter.LFunction chi (conj z))) Set.univ :=
    DifferentiableOn.analyticOnNhd (fun z _ =>
      (differentiableAt_conj_conj_iff.mpr
        (DirichletCharacter.differentiable_LFunction hchi (conj z))).differentiableWithinAt)
      isOpen_univ
  have heq (z : ℂ) (hz : 1 < z.re) :
      DirichletCharacter.LFunction chi⁻¹ z =
        conj (DirichletCharacter.LFunction chi (conj z)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries chi⁻¹ hz,
      DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hz)]
    exact (conj_LSeries_conj_eq_inv chi z).symm
  have hfun : DirichletCharacter.LFunction chi⁻¹ =
      fun z : ℂ => conj (DirichletCharacter.LFunction chi (conj z)) :=
    hinvAnalytic.eq_of_eventuallyEq hconjAnalytic <|
      eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (by norm_num : (1 : ℝ) < ((2 : ℂ).re))) heq
  simpa using congrFun hfun (conj s)

/-- A square-principal nonprincipal character has a real-coefficient
L-function on the whole continued plane. -/
theorem LFunction_conj_of_sq_eq_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (hsquare : chi ^ 2 = 1) (s : ℂ) :
    DirichletCharacter.LFunction chi (conj s) =
      conj (DirichletCharacter.LFunction chi s) := by
  have hinv : chi⁻¹ = chi :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsquare)
  simpa [hinv] using LFunction_inv_conj chi hchi s

/-- Nonprincipal nontrivial zeros of a square-principal character are closed
under complex conjugation. -/
theorem IsNonprincipalNontrivialLFunctionZero.conj_of_sq_eq_one
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q} {rho : ℂ}
    (hrho : IsNonprincipalNontrivialLFunctionZero chi rho)
    (hsquare : chi ^ 2 = 1) :
    IsNonprincipalNontrivialLFunctionZero chi (conj rho) := by
  rw [isNonprincipalNontrivialLFunctionZero_iff chi rho] at hrho
  rw [isNonprincipalNontrivialLFunctionZero_iff chi (conj rho)]
  rcases hrho with ⟨hchi, hzero, hrePos, hreLt⟩
  refine ⟨hchi, ?_, ?_, ?_⟩
  · rw [LFunction_conj_of_sq_eq_one chi hchi hsquare rho, hzero,
      map_zero]
  · simpa using hrePos
  · simpa using hreLt

end BoundedGaps.Maynard
