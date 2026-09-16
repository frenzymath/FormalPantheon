import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Finite Dirichlet character decomposition of progression sums

This connects the project's `Nat.ModEq` convention with Mathlib's
`ArithmeticFunction.vonMangoldt.residueClass` and its character
orthogonality formula. No prime-distribution estimate is asserted here.

Source architecture: `MONTGOMERY-VAUGHAN-MNT-I`, Eq. (11.22), p. 377.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

open ArithmeticFunction DirichletCharacter

/-- A finite von Mangoldt sum filtered by `Nat.ModEq` is the same sum written
using Mathlib's residue-class indicator. -/
theorem sum_vonMangoldt_modEq_eq_sum_residueClass
    (s : Finset Nat) {q a : Nat} :
    (∑ n ∈ s with n ≡ a [MOD q], vonMangoldt n) =
      ∑ n ∈ s, vonMangoldt.residueClass (a : ZMod q) n := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [vonMangoldt.residueClass, Set.indicator_apply,
    Set.mem_setOf_eq, ZMod.natCast_eq_natCast_iff]

/-- Character orthogonality gives the exact finite average of twisted von
Mangoldt sums in a coprime residue class. -/
theorem sum_vonMangoldt_modEq_eq_character_average
    (s : Finset Nat) {q a : Nat} [NeZero q]
    (ha : Nat.Coprime a q) :
    ((∑ n ∈ s with n ≡ a [MOD q], vonMangoldt n : Real) : Complex) =
      (q.totient : Complex)⁻¹ *
        ∑ chi : DirichletCharacter Complex q,
          chi ((a : ZMod q)⁻¹) *
            ∑ n ∈ s, chi n * (vonMangoldt n : Complex) := by
  classical
  have haUnit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  calc
    ((∑ n ∈ s with n ≡ a [MOD q], vonMangoldt n : Real) : Complex) =
        ∑ n ∈ s,
          (vonMangoldt.residueClass (a : ZMod q) n : Complex) := by
      rw [sum_vonMangoldt_modEq_eq_sum_residueClass]
      push_cast
      rfl
    _ = ∑ n ∈ s, (q.totient : Complex)⁻¹ *
          ∑ chi : DirichletCharacter Complex q,
            chi ((a : ZMod q)⁻¹) * chi n *
              (vonMangoldt n : Complex) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact vonMangoldt.residueClass_apply haUnit n
    _ = (q.totient : Complex)⁻¹ *
          ∑ n ∈ s, ∑ chi : DirichletCharacter Complex q,
            chi ((a : ZMod q)⁻¹) * chi n *
              (vonMangoldt n : Complex) := by
      rw [Finset.mul_sum]
    _ = (q.totient : Complex)⁻¹ *
          ∑ chi : DirichletCharacter Complex q,
            ∑ n ∈ s, chi ((a : ZMod q)⁻¹) * chi n *
              (vonMangoldt n : Complex) := by
      rw [Finset.sum_comm]
    _ = (q.totient : Complex)⁻¹ *
          ∑ chi : DirichletCharacter Complex q,
            chi ((a : ZMod q)⁻¹) *
              ∑ n ∈ s, chi n * (vonMangoldt n : Complex) := by
      congr 1
      apply Finset.sum_congr rfl
      intro chi hchi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

end PrimesRestrictedDigits
