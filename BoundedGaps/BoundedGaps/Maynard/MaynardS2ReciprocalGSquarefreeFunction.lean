import BoundedGaps.Maynard.MaynardS2GDivisorExpansion

noncomputable section

/-!
# Squarefree reciprocal-g function for S2

Maynard2013v3, Section 6, Lemma `lmm:S2Expression1`, uses the scalar
squarefree weight `mu(n)^2 / g(n)` with `(n,W)=1`. This module packages that
weight as a multiplicative arithmetic function. See `SEM-350`.
-/

namespace BoundedGaps.Maynard

open ArithmeticFunction

noncomputable def maynardS2ReciprocalGWeightAF
    (W : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p =>
    if p ∣ W then 0 else (1 : ℝ) / ((p - 2 : ℕ) : ℝ)

theorem maynardS2ReciprocalGWeightAF_isMultiplicative (W : ℕ) :
    (maynardS2ReciprocalGWeightAF W).IsMultiplicative := by
  unfold maynardS2ReciprocalGWeightAF
  exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem maynardS2ReciprocalGWeightAF_apply_prime
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    maynardS2ReciprocalGWeightAF W p =
      if p ∣ W then 0 else (1 : ℝ) / ((p - 2 : ℕ) : ℝ) := by
  rw [maynardS2ReciprocalGWeightAF,
    ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]
  simp

theorem maynardS2ReciprocalGWeightAF_apply_squarefree_of_coprime
    {W n : ℕ} (hn : Squarefree n) (hcop : Nat.Coprime n W) :
    maynardS2ReciprocalGWeightAF W n =
      (1 : ℝ) / (maynardS2G n : ℝ) := by
  have hg : (maynardS2G n : ℝ) =
      ∏ p ∈ n.primeFactors, ((p - 2 : ℕ) : ℝ) := by
    rw [maynardS2G_apply hn.ne_zero]
    push_cast
    rfl
  calc
    maynardS2ReciprocalGWeightAF W n =
        ∏ p ∈ n.primeFactors,
          (if p ∣ W then 0 else (1 : ℝ) / ((p - 2 : ℕ) : ℝ)) := by
      rw [maynardS2ReciprocalGWeightAF,
        ArithmeticFunction.prodPrimeFactors_apply hn.ne_zero]
    _ = ∏ p ∈ n.primeFactors,
        (1 : ℝ) / ((p - 2 : ℕ) : ℝ) := by
      apply Finset.prod_congr rfl
      intro p hpMem
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
      have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpMem
      have hpW : ¬p ∣ W := hpPrime.coprime_iff_not_dvd.mp
        (Nat.Coprime.of_dvd_left hpDvd hcop)
      rw [if_neg hpW]
    _ = (1 : ℝ) / ∏ p ∈ n.primeFactors,
        ((p - 2 : ℕ) : ℝ) := by
      rw [Finset.prod_div_distrib]
      simp
    _ = (1 : ℝ) / (maynardS2G n : ℝ) := by rw [hg]

noncomputable def maynardS2ReciprocalGSquarefreeAF
    (W : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul
    (ArithmeticFunction.pmul
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ))
    (maynardS2ReciprocalGWeightAF W)

theorem maynardS2ReciprocalGSquarefreeAF_isMultiplicative (W : ℕ) :
    (maynardS2ReciprocalGSquarefreeAF W).IsMultiplicative := by
  unfold maynardS2ReciprocalGSquarefreeAF
  exact (ArithmeticFunction.isMultiplicative_moebius.intCast.pmul
    ArithmeticFunction.isMultiplicative_moebius.intCast).pmul
      (maynardS2ReciprocalGWeightAF_isMultiplicative W)

theorem maynardS2ReciprocalGSquarefreeAF_apply_squarefree_of_coprime
    {W n : ℕ} (hn : Squarefree n) (hcop : Nat.Coprime n W) :
    maynardS2ReciprocalGSquarefreeAF W n =
      (1 : ℝ) / (maynardS2G n : ℝ) := by
  unfold maynardS2ReciprocalGSquarefreeAF
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  have hmu : (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
    exact_mod_cast (squarefree_iff_moebius_sq_eq_one n).mp hn
  calc
    (ArithmeticFunction.moebius n : ℝ) * ArithmeticFunction.moebius n *
        maynardS2ReciprocalGWeightAF W n =
        (ArithmeticFunction.moebius n : ℝ) ^ 2 *
          maynardS2ReciprocalGWeightAF W n := by ring
    _ = maynardS2ReciprocalGWeightAF W n := by rw [hmu, one_mul]
    _ = (1 : ℝ) / (maynardS2G n : ℝ) :=
      maynardS2ReciprocalGWeightAF_apply_squarefree_of_coprime hn hcop

theorem maynardS2ReciprocalGSquarefreeAF_apply_prime
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    maynardS2ReciprocalGSquarefreeAF W p =
      if p ∣ W then 0 else (1 : ℝ) / ((p - 2 : ℕ) : ℝ) := by
  unfold maynardS2ReciprocalGSquarefreeAF
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  have hmu : (ArithmeticFunction.moebius p : ℝ) ^ 2 = 1 := by
    exact_mod_cast (squarefree_iff_moebius_sq_eq_one p).mp hp.squarefree
  calc
    (ArithmeticFunction.moebius p : ℝ) * ArithmeticFunction.moebius p *
        maynardS2ReciprocalGWeightAF W p =
        (ArithmeticFunction.moebius p : ℝ) ^ 2 *
          maynardS2ReciprocalGWeightAF W p := by ring
    _ = maynardS2ReciprocalGWeightAF W p := by rw [hmu, one_mul]
    _ = if p ∣ W then 0 else (1 : ℝ) / ((p - 2 : ℕ) : ℝ) :=
      maynardS2ReciprocalGWeightAF_apply_prime W hp

end BoundedGaps.Maynard
