import Waring.Analytic.Basic

/-!
# Product factorization of complete power sums

This file proves the algebraic product decomposition underlying the
prime-power factorization cited in Chen's Lemma 2.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Transport an additive character across an additive equivalence. -/
noncomputable def AddChar.transport {R S : Type*} [AddMonoid R] [AddMonoid S]
    (equiv : R ≃+ S) (character : AddChar R Complex) : AddChar S Complex :=
  character.compAddMonoidHom equiv.symm.toAddMonoidHom

/-- The restriction of a character on a product to the left factor. -/
noncomputable def AddChar.leftFactor {R S : Type*} [AddMonoid R] [AddMonoid S]
    (character : AddChar (R × S) Complex) : AddChar R Complex :=
  character.compAddMonoidHom (AddMonoidHom.inl R S)

/-- The restriction of a character on a product to the right factor. -/
noncomputable def AddChar.rightFactor {R S : Type*} [AddMonoid R] [AddMonoid S]
    (character : AddChar (R × S) Complex) : AddChar S Complex :=
  character.compAddMonoidHom (AddMonoidHom.inr R S)

/-- A complete power sum on a product semiring is the product of the two sums
attached to the restricted characters. -/
theorem powerSum_prod {R S : Type*} [Semiring R] [Semiring S]
    [Fintype R] [Fintype S] (character : AddChar (R × S) Complex)
    (k : Nat) (a : R) (b : S) :
    powerSum character k (a, b) =
      powerSum (AddChar.leftFactor character) k a *
        powerSum (AddChar.rightFactor character) k b := by
  rw [powerSum, Fintype.sum_prod_type, powerSum, powerSum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simpa [AddChar.leftFactor, AddChar.rightFactor] using
    character.map_add_eq_mul (a * x ^ k, 0) (0, b * y ^ k)

/-- Complete power sums are invariant under transport across a ring
equivalence. -/
theorem powerSum_ringEquiv {R S : Type*} [Semiring R] [Semiring S]
    [Fintype R] [Fintype S] (equiv : R ≃+* S) (character : AddChar R Complex)
    (k : Nat) (a : R) :
    powerSum character k a =
      powerSum (AddChar.transport equiv.toAddEquiv character) k (equiv a) := by
  rw [powerSum, powerSum, ← equiv.toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  simp [AddChar.transport]

/-- The standard character modulo `m*n`, transported across the Chinese
remainder equivalence. -/
noncomputable def chineseRemainderCharacter {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) : AddChar (ZMod m × ZMod n) Complex :=
  AddChar.transport (ZMod.chineseRemainder hcoprime).toAddEquiv ZMod.stdAddChar

/-- Exact CRT factorization of a complete power sum. The two factor characters
remain explicit because their standard-character normalizations involve
modular inverses. -/
theorem completePowerSum_mul {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (k : Nat) (a : ZMod (m * n)) :
    completePowerSum k a =
      powerSum (AddChar.leftFactor (chineseRemainderCharacter hcoprime)) k
          ((ZMod.chineseRemainder hcoprime a).1) *
        powerSum (AddChar.rightFactor (chineseRemainderCharacter hcoprime)) k
          ((ZMod.chineseRemainder hcoprime a).2) := by
  calc
    completePowerSum k a = powerSum ZMod.stdAddChar k a := rfl
    _ = powerSum (chineseRemainderCharacter hcoprime) k
        (ZMod.chineseRemainder hcoprime a) :=
      powerSum_ringEquiv (ZMod.chineseRemainder hcoprime) ZMod.stdAddChar k a
    _ = _ := powerSum_prod (chineseRemainderCharacter hcoprime) k _ _

end Waring.Analytic
