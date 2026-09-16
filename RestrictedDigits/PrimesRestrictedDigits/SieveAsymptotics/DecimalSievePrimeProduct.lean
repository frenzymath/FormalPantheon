import PrimesRestrictedDigits.SieveDecomposition.RoughSmoothFactorization
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.PrimeCounting

/-!
# Decimal sieve prime product

This realizes Maynard's weak source cutoff `p <= z` as a squarefree natural product while
excluding the prime divisors of ten.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The source primes weakly at most `z` that do not divide the decimal base. -/
def decimalSievePrimeCarrier (z : Real) : Finset Nat :=
  (Nat.primesLE (Nat.floor z)).filter fun p => ¬p ∣ 10

@[simp] theorem mem_decimalSievePrimeCarrier_iff
    {z : Real} {p : Nat} :
    p ∈ decimalSievePrimeCarrier z ↔
      p.Prime ∧ ¬p ∣ 10 ∧ (p : Real) <= z := by
  simp only [decimalSievePrimeCarrier, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpFloor, hp⟩, hpTen⟩
    exact ⟨hp, hpTen, (Nat.le_floor_iff' hp.ne_zero).mp hpFloor⟩
  · rintro ⟨hp, hpTen, hpz⟩
    exact ⟨⟨(Nat.le_floor_iff' hp.ne_zero).mpr hpz, hp⟩, hpTen⟩

/-- The squarefree source sieving integer at the weak cutoff `z`. -/
def decimalSievePrimeProduct (z : Real) : Nat :=
  ∏ p ∈ decimalSievePrimeCarrier z, p

theorem primeFactors_decimalSievePrimeProduct (z : Real) :
    (decimalSievePrimeProduct z).primeFactors =
      decimalSievePrimeCarrier z := by
  rw [decimalSievePrimeProduct]
  exact Nat.primeFactors_prod fun p hp =>
    (mem_decimalSievePrimeCarrier_iff.mp hp).1

theorem squarefree_decimalSievePrimeProduct (z : Real) :
    Squarefree (decimalSievePrimeProduct z) := by
  rw [decimalSievePrimeProduct]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hpPrime := (mem_decimalSievePrimeCarrier_iff.mp hp).1
    have hqPrime := (mem_decimalSievePrimeCarrier_iff.mp hq).1
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes hpPrime hqPrime).mpr hpq)
  · intro p hp
    exact (mem_decimalSievePrimeCarrier_iff.mp hp).1.prime.squarefree

theorem decimalSievePrimeProduct_ne_zero (z : Real) :
    decimalSievePrimeProduct z ≠ 0 :=
  (squarefree_decimalSievePrimeProduct z).ne_zero

@[simp] theorem mem_decimalSievePrimeProductFactors_iff
    {z : Real} {p : Nat} :
    p ∈ (decimalSievePrimeProduct z).primeFactors ↔
      p.Prime ∧ ¬p ∣ 10 ∧ (p : Real) <= z := by
  rw [primeFactors_decimalSievePrimeProduct]
  exact mem_decimalSievePrimeCarrier_iff

/-- Source factors lie strictly below the successor-floor analytic cutoff. -/
theorem decimalSievePrimeProduct_factor_lt_floor_add_one
    {z : Real} {p : Nat}
    (hp : p ∈ (decimalSievePrimeProduct z).primeFactors) :
    (p : Real) < (Nat.floor z : Real) + 1 := by
  exact (mem_decimalSievePrimeProductFactors_iff.mp hp).2.2.trans_lt
    (Nat.lt_floor_add_one z)

/-- Coprimality to the source product is strict roughness on decimal-coprime
integers. -/
theorem coprime_decimalSievePrimeProduct_iff_strictRoughPredicate
    {z : Real} {n : Nat} (hnTen : n.Coprime 10) :
    (decimalSievePrimeProduct z).Coprime n ↔
      strictRoughPredicate z n := by
  constructor
  · intro hnProduct p hp hpn
    by_contra hpz
    have hple : (p : Real) <= z := le_of_not_gt hpz
    have hpTen : ¬p ∣ 10 := by
      exact (hp.coprime_iff_not_dvd.mp (hnTen.of_dvd_left hpn))
    have hpFactor : p ∈ (decimalSievePrimeProduct z).primeFactors :=
      mem_decimalSievePrimeProductFactors_iff.mpr ⟨hp, hpTen, hple⟩
    have hpProduct : p ∣ decimalSievePrimeProduct z :=
      Nat.dvd_of_mem_primeFactors hpFactor
    exact (hp.coprime_iff_not_dvd.mp
      (hnProduct.of_dvd_left hpProduct)) hpn
  · intro hnRough
    apply Nat.coprime_of_dvd
    intro p hp hpProduct hpn
    have hpFactor : p ∈ (decimalSievePrimeProduct z).primeFactors :=
      hp.mem_primeFactors hpProduct (decimalSievePrimeProduct_ne_zero z)
    have hple := (mem_decimalSievePrimeProductFactors_iff.mp hpFactor).2.2
    exact (not_lt_of_ge hple) (hnRough p hp hpn)

@[simp] theorem mem_divisors_decimalSievePrimeProduct_iff
    {z : Real} {m : Nat} :
    m ∈ Nat.divisors (decimalSievePrimeProduct z) ↔
      m ≠ 0 ∧ Squarefree m ∧ m.Coprime 10 ∧
        weakSmoothPredicate z m := by
  rw [Nat.mem_divisors]
  have hProductZero := decimalSievePrimeProduct_ne_zero z
  constructor
  · rintro ⟨hmProduct, _⟩
    have hmZero : m ≠ 0 := ne_zero_of_dvd_ne_zero hProductZero hmProduct
    have hmSquarefree : Squarefree m :=
      Squarefree.squarefree_of_dvd hmProduct
        (squarefree_decimalSievePrimeProduct z)
    have hmTen : m.Coprime 10 := by
      apply Nat.coprime_of_dvd
      intro p hp hpm
      have hpProduct : p ∣ decimalSievePrimeProduct z := hpm.trans hmProduct
      have hpFactor : p ∈ (decimalSievePrimeProduct z).primeFactors :=
        hp.mem_primeFactors hpProduct hProductZero
      exact (mem_decimalSievePrimeProductFactors_iff.mp hpFactor).2.1
    have hmSmooth : weakSmoothPredicate z m := by
      intro p hp hpm
      have hpProduct : p ∣ decimalSievePrimeProduct z := hpm.trans hmProduct
      have hpFactor : p ∈ (decimalSievePrimeProduct z).primeFactors :=
        hp.mem_primeFactors hpProduct hProductZero
      exact (mem_decimalSievePrimeProductFactors_iff.mp hpFactor).2.2
    exact ⟨hmZero, hmSquarefree, hmTen, hmSmooth⟩
  · rintro ⟨hmZero, hmSquarefree, hmTen, hmSmooth⟩
    refine ⟨?_, hProductZero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hmSquarefree,
      decimalSievePrimeProduct]
    apply Finset.prod_dvd_prod_of_subset
    intro p hpFactor
    have hp := Nat.prime_of_mem_primeFactors hpFactor
    have hpDvd : p ∣ m := Nat.dvd_of_mem_primeFactors hpFactor
    have hpTen : ¬p ∣ 10 :=
      hp.coprime_iff_not_dvd.mp (hmTen.of_dvd_left hpDvd)
    exact mem_decimalSievePrimeCarrier_iff.mpr
      ⟨hp, hpTen, hmSmooth p hp hpDvd⟩

end

end PrimesRestrictedDigits
