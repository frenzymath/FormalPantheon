import BoundedGaps.Maynard.MaynardS2OuterPrimeSquareTail

noncomputable section

/-!
# Composite squarefree factorization of the S2 outer weight

Maynard2013v3, source lines 540--552, uses the product of the prime-local
weights `phi(r)^2/(g(r)r^2)` on squarefree composite variables.  This file
identifies that product with the corresponding composite expression.
-/

namespace BoundedGaps.Maynard

theorem maynardS2OuterScalarWeight_prod_eq
    {n : ℕ} (hn : Squarefree n) :
    (∏ p ∈ n.primeFactors, maynardS2OuterScalarWeight p) =
      (Nat.totient n : ℝ) ^ 2 /
        ((maynardS2G n : ℝ) * (n : ℝ) ^ 2) := by
  have hphiNat := totient_eq_prod_primeFactors_of_squarefree hn
  have hgNat := maynardS2G_apply hn.ne_zero
  have hnNat := Nat.prod_primeFactors_of_squarefree hn
  have hphi : (Nat.totient n : ℝ) =
      ∏ p ∈ n.primeFactors, (Nat.totient p : ℝ) := by
    exact_mod_cast hphiNat
  have hg : (maynardS2G n : ℝ) =
      ∏ p ∈ n.primeFactors, (maynardS2G p : ℝ) := by
    rw [hgNat]
    push_cast
    apply Finset.prod_congr rfl
    intro p hp
    rw [maynardS2G_prime (Nat.prime_of_mem_primeFactors hp)]
  have hnR : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hnNat.symm
  calc
    (∏ p ∈ n.primeFactors, maynardS2OuterScalarWeight p) =
        ∏ p ∈ n.primeFactors,
          ((Nat.totient p : ℝ) ^ 2 /
            ((maynardS2G p : ℝ) * (p : ℝ) ^ 2)) := by
      apply Finset.prod_congr rfl
      intro p hp
      rfl
    _ = (∏ p ∈ n.primeFactors, (Nat.totient p : ℝ)) ^ 2 /
        ((∏ p ∈ n.primeFactors, (maynardS2G p : ℝ)) *
          (∏ p ∈ n.primeFactors, (p : ℝ)) ^ 2) := by
      rw [Finset.prod_div_distrib, ← Finset.prod_pow]
      congr 1
      rw [Finset.prod_mul_distrib, ← Finset.prod_pow]
    _ = (Nat.totient n : ℝ) ^ 2 /
        ((maynardS2G n : ℝ) * (n : ℝ) ^ 2) := by
      rw [← hphi, ← hg, ← hnR]

end BoundedGaps.Maynard
