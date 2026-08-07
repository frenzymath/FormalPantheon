import BoundedGaps.Maynard.MaynardS2OuterWeightFactorization

noncomputable section

/-!
# Multiplicative arithmetic function for the S2 outer weight

Maynard2013v3, source lines 540--552, uses a prime-local weight which vanishes
on primes dividing the pre-sieving modulus.  The prime-factor extension below
packages that local data without assuming the missing cumulative estimate.
-/

namespace BoundedGaps.Maynard

open ArithmeticFunction

noncomputable def maynardS2OuterWeightAF (W : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p =>
    if p ∣ W then 0 else maynardS2OuterScalarWeight p)

theorem maynardS2OuterWeightAF_isMultiplicative (W : ℕ) :
    (maynardS2OuterWeightAF W).IsMultiplicative := by
  unfold maynardS2OuterWeightAF
  exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem maynardS2OuterWeightAF_apply_prime
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    maynardS2OuterWeightAF W p =
      if p ∣ W then 0 else maynardS2OuterScalarWeight p := by
  rw [maynardS2OuterWeightAF, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,
    hp.primeFactors]
  simp

theorem maynardS2OuterWeightAF_apply_squarefree_of_coprime
    {W n : ℕ} (hn : Squarefree n) (hcop : Nat.Coprime n W) :
    maynardS2OuterWeightAF W n =
      (Nat.totient n : ℝ) ^ 2 /
        ((maynardS2G n : ℝ) * (n : ℝ) ^ 2) := by
  calc
    maynardS2OuterWeightAF W n =
        ∏ p ∈ n.primeFactors,
          (if p ∣ W then 0 else maynardS2OuterScalarWeight p) := by
      rw [maynardS2OuterWeightAF,
        ArithmeticFunction.prodPrimeFactors_apply hn.ne_zero]
    _ = ∏ p ∈ n.primeFactors, maynardS2OuterScalarWeight p := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpW : ¬p ∣ W := by
        exact hpPrime.coprime_iff_not_dvd.mp
          (Nat.Coprime.of_dvd_left hpdvd hcop)
      rw [if_neg hpW]
    _ = (Nat.totient n : ℝ) ^ 2 /
        ((maynardS2G n : ℝ) * (n : ℝ) ^ 2) :=
      maynardS2OuterScalarWeight_prod_eq hn

end BoundedGaps.Maynard
