import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Decimal-smooth Dirichlet character conductors

Factorization and conductor relations for decimal-smooth moduli.

Source: `MONTGOMERY-VAUGHAN-MNT-I`, Theorem 9.2 and Lemma 9.3, pp. 282--284,
and Chapter 11, p. 370, for quadratic primitive inheritance.
-/

namespace PrimesRestrictedDigits

/-- A positive natural whose prime factors are all two or five. -/
def IsDecimalSmooth (q : Nat) : Prop :=
  q ∈ Nat.factoredNumbers {2, 5}

/-- Decimal-smooth naturals are exactly products of a power of two and a power
of five. -/
theorem isDecimalSmooth_iff_exists_two_pow_mul_five_pow (q : Nat) :
    IsDecimalSmooth q ↔ ∃ a b : Nat, q = 2 ^ a * 5 ^ b := by
  constructor
  · intro hq
    let e2 := Nat.equivProdNatFactoredNumbers Nat.prime_two
      (by simp : 2 ∉ ({5} : Finset Nat))
    let x := e2.symm ⟨q, hq⟩
    let e5 := Nat.equivProdNatFactoredNumbers Nat.prime_five
      (by simp : 5 ∉ (∅ : Finset Nat))
    let y := e5.symm x.2
    have hqeq : q = 2 ^ x.1 * (x.2 : Nat) := by
      have h := congrArg Subtype.val (e2.apply_symm_apply ⟨q, hq⟩)
      simpa only [e2, x, Nat.equivProdNatFactoredNumbers_apply'] using h.symm
    have hxeq : (x.2 : Nat) = 5 ^ y.1 * (y.2 : Nat) := by
      have h := congrArg Subtype.val (e5.apply_symm_apply x.2)
      simpa only [e5, y, Nat.equivProdNatFactoredNumbers_apply'] using h.symm
    have hy : (y.2 : Nat) = 1 := by
      simpa only [Nat.factoredNumbers_empty, Set.mem_singleton_iff] using y.2.property
    refine ⟨x.1, y.1, ?_⟩
    rw [hqeq, hxeq, hy, mul_one]
  · rintro ⟨a, b, rfl⟩
    change 2 ^ a * 5 ^ b ∈ Nat.factoredNumbers {2, 5}
    have h1 : (1 : Nat) ∈ Nat.factoredNumbers ∅ := by
      rw [Nat.factoredNumbers_empty]
      rfl
    have h5 := Nat.pow_mul_mem_factoredNumbers Nat.prime_five b h1
    have h2 := Nat.pow_mul_mem_factoredNumbers Nat.prime_two a h5
    simpa using h2

/-- Decimal-smooth naturals are exactly the divisors of powers of ten. -/
theorem isDecimalSmooth_iff_exists_dvd_pow_ten (q : Nat) :
    IsDecimalSmooth q ↔ ∃ K : Nat, q ∣ 10 ^ K := by
  constructor
  · rw [isDecimalSmooth_iff_exists_two_pow_mul_five_pow]
    rintro ⟨a, b, rfl⟩
    refine ⟨max a b, ?_⟩
    change 2 ^ a * 5 ^ b ∣ (2 * 5) ^ max a b
    rw [mul_pow]
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 (Nat.le_max_left a b))
      (Nat.pow_dvd_pow 5 (Nat.le_max_right a b))
  · rintro ⟨K, hq⟩
    apply Nat.mem_factoredNumbers_of_dvd _ hq
    apply (isDecimalSmooth_iff_exists_two_pow_mul_five_pow (10 ^ K)).2
    refine ⟨K, K, ?_⟩
    calc
      10 ^ K = (2 * 5) ^ K := by norm_num
      _ = 2 ^ K * 5 ^ K := mul_pow 2 5 K

/-- Divisors of decimal-smooth naturals remain decimal-smooth. -/
theorem IsDecimalSmooth.of_dvd {m q : Nat}
    (hq : IsDecimalSmooth q) (hm : m ∣ q) : IsDecimalSmooth m :=
  Nat.mem_factoredNumbers_of_dvd hq hm

/-- The conductor of a character at a decimal-smooth level is decimal-smooth. -/
theorem IsDecimalSmooth.conductor {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : IsDecimalSmooth q) :
    IsDecimalSmooth chi.conductor :=
  hq.of_dvd chi.conductor_dvd_level

/-- Passing to the primitive inducing character preserves quadraticity. -/
theorem primitiveCharacter_isQuadratic {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi.IsQuadratic) :
    chi.primitiveCharacter.IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one]
  apply DirichletCharacter.changeLevel_injective chi.conductor_dvd_level
  simpa only [map_pow, DirichletCharacter.changeLevel_primitiveCharacter,
    map_one] using hchi.sq_eq_one

end PrimesRestrictedDigits
