import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# The inducing Dirichlet Euler product

The L-function of a character is the L-function of its inducing primitive
character times an exact finite product over the prime divisors of the
original modulus. Inactive conductor-prime factors are retained as factors
equal to one.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110,
equation (11.2), and printed pp. 112--113. Semantic review: `SEM-506`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

private local instance conductorNeZero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor :=
  ⟨chi.conductor_ne_zero⟩

/-- The exact finite Euler product relating a character to its inducing
primitive character. Inactive factors are retained as factors equal to one. -/
noncomputable def inducingEulerProduct
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors,
    (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s))

private lemma primitiveCharacter_ne_one_of_ne_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hpsi
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter]
  exact (DirichletCharacter.changeLevel_eq_one_iff
    chi.conductor_dvd_level).2 hpsi

/-- The guarded change-of-level identity for an arbitrary character. -/
theorem LFunction_eq_inducingPrimitive_mul_inducingEulerProduct
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hguard : chi ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction chi s =
      DirichletCharacter.LFunction chi.primitiveCharacter s *
        inducingEulerProduct chi s := by
  have hprimitiveGuard : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1 :=
    hguard.imp (primitiveCharacter_ne_one_of_ne_one chi) id
  calc
    DirichletCharacter.LFunction chi s =
        DirichletCharacter.LFunction
          (DirichletCharacter.changeLevel chi.conductor_dvd_level
            chi.primitiveCharacter) s := by
      rw [chi.changeLevel_primitiveCharacter]
    _ = DirichletCharacter.LFunction chi.primitiveCharacter s *
        ∏ p ∈ q.primeFactors,
          (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)) :=
      DirichletCharacter.LFunction_changeLevel chi.conductor_dvd_level
        chi.primitiveCharacter hprimitiveGuard
    _ = _ := rfl

private lemma norm_character_mul_cpow_lt_one
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    ‖psi p * (p : ℂ) ^ (-s)‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, neg_re]
  calc
    ‖psi p‖ * (p : ℝ) ^ (-s.re) ≤
        1 * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (psi.norm_le_one p)
        (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ < 1 := by
      simpa using
        Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos hs)

private lemma inducingEulerFactor_ne_zero_of_re_pos
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    (1 : ℂ) - psi p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro hzero
  have hw : psi p * (p : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm := norm_character_mul_cpow_lt_one psi p hp s hs
  rw [hw, norm_one] at hnorm
  exact (lt_irrefl 1) hnorm

/-- The inducing product has no zero in the open right half-plane. -/
theorem inducingEulerProduct_ne_zero_of_re_pos
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    inducingEulerProduct chi s ≠ 0 := by
  rw [inducingEulerProduct, Finset.prod_ne_zero_iff]
  intro p hp
  exact inducingEulerFactor_ne_zero_of_re_pos chi.primitiveCharacter p
    (Nat.prime_of_mem_primeFactors hp) s hs

private lemma differentiableAt_inducingEulerFactor
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) :
    DifferentiableAt ℂ
      (fun z : ℂ => 1 - psi p * (p : ℂ) ^ (-z)) s :=
  ((hasDerivAt_const s (1 : ℂ)).sub
    (((hasDerivAt_neg' s).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero))).const_mul
        (psi p))).differentiableAt

/-- The inducing finite Euler product is entire. -/
theorem differentiable_inducingEulerProduct
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    Differentiable ℂ (inducingEulerProduct chi) := by
  intro s
  unfold inducingEulerProduct
  exact .fun_finsetProd fun p hp =>
    differentiableAt_inducingEulerFactor chi.primitiveCharacter p
      (Nat.prime_of_mem_primeFactors hp) s

end BoundedGaps.Maynard
