import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaZeroFree

/-!
# Principal-character zero transport

Away from the pole, Mathlib factors the principal Dirichlet L-function as
Riemann zeta times the finite Euler product over primes dividing the modulus.
Every factor is nonzero in the open right half-plane, so principal-character
zeros there are exactly zeta zeros. The quantitative zeta zero-free region
therefore transfers with no modulus-dependent loss.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110,
equation (11.2), and printed p. 119, the start of the proof of Theorem 12.3.
Semantic review: `SEM-492`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

private lemma norm_natCast_cpow_neg_lt_one
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos hs)

private lemma principalEulerFactor_ne_zero_of_re_pos
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  intro hzero
  have hpow : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := norm_natCast_cpow_neg_lt_one p hp s hs
  rw [hpow, norm_one] at hnorm
  exact (lt_irrefl 1) hnorm

private lemma principalEulerProduct_ne_zero_of_re_pos
    (q : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact principalEulerFactor_ne_zero_of_re_pos p
    (Nat.prime_of_mem_primeFactors hp) s hs

/-- Away from the pole, principal-character and zeta zeros agree throughout
the open right half-plane. -/
theorem principal_LFunction_eq_zero_iff_riemannZeta_eq_zero_of_re_pos_of_ne_one
    {q : ℕ} [NeZero q] {rho : ℂ}
    (hrho : 0 < rho.re) (hrho_one : rho ≠ 1) :
    DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ q) rho = 0 ↔
      riemannZeta rho = 0 := by
  have hproduct :
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-rho))) ≠ 0 :=
    principalEulerProduct_ne_zero_of_re_pos q rho hrho
  change DirichletCharacter.LFunctionTrivChar q rho = 0 ↔ _
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hrho_one,
    mul_eq_zero]
  simp only [hproduct, false_or]

/-- Principal-character open-strip zeros inherit the modulus-free zeta
zero-free region. -/
theorem exists_nat_principal_LFunction_openStrip_zero_re_lt :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q] (rho : ℂ),
        0 < rho.re → rho.re < 1 →
          DirichletCharacter.LFunction
              (1 : DirichletCharacter ℂ q) rho = 0 →
            rho.re <
              1 - 1 / ((M : ℝ) ^ 2 *
                Real.log (|rho.im| + 2)) := by
  obtain ⟨M, hM, hzeta⟩ := exists_nat_riemannZeta_zero_re_lt
  refine ⟨M, hM, ?_⟩
  intro q _ rho hrho0 hrho1 hzero
  have hrho_one : rho ≠ 1 := by
    intro hrho
    have hre := congrArg Complex.re hrho
    norm_num at hre
    linarith
  exact hzeta rho
    ((principal_LFunction_eq_zero_iff_riemannZeta_eq_zero_of_re_pos_of_ne_one
      hrho0 hrho_one).mp hzero)

end BoundedGaps.Maynard
