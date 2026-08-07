import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Cross-level characters in Goldfeld's argument

Two primitive real characters in Theorem 12.9 can have different moduli.
Mathlib's cross-level product lifts them to the least common multiple of those
moduli.  This file records the exact distinctness, quadraticity,
nonprincipality, and conductor facts used before the four-factor Dirichlet
series is formed.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.9, printed
pp. 125--126.  Semantic review: `SEM-549`.
-/

noncomputable section

namespace BoundedGaps.Maynard

/-- Two characters at possibly different levels are distinct when their
canonical lifts to the common least-common-multiple level are unequal. -/
def goldfeldCharactersDistinct {q1 q : ℕ}
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q) : Prop :=
  chi1.changeLevel (Nat.dvd_lcm_left q1 q) ≠
    chi.changeLevel (Nat.dvd_lcm_right q1 q)

/-- At one level, Goldfeld distinctness is ordinary character inequality. -/
theorem goldfeldCharactersDistinct_same_level_iff
    {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter Complex q) :
    goldfeldCharactersDistinct chi1 chi ↔ chi1 ≠ chi := by
  letI : NeZero (Nat.lcm q q) :=
    ⟨Nat.lcm_ne_zero (NeZero.ne q) (NeZero.ne q)⟩
  unfold goldfeldCharactersDistinct
  rw [show Nat.dvd_lcm_right q q = Nat.dvd_lcm_left q q from
    Subsingleton.elim _ _]
  exact (DirichletCharacter.changeLevel_injective
    (R := Complex) (Nat.dvd_lcm_left q q)).ne_iff

/-- Primitive characters at unequal moduli remain unequal after lifting to
their common level. -/
theorem goldfeldCharactersDistinct_of_modulus_ne
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q)
    (hprimitive1 : DirichletCharacter.IsPrimitive chi1)
    (hprimitive : DirichletCharacter.IsPrimitive chi)
    (hmodulus : q1 ≠ q) :
    goldfeldCharactersDistinct chi1 chi := by
  letI : NeZero (Nat.lcm q1 q) :=
    ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩
  rw [goldfeldCharactersDistinct]
  intro heq
  apply hmodulus
  have hconductor := congrArg DirichletCharacter.conductor heq
  rw [chi1.conductor_changeLevel, chi.conductor_changeLevel] at hconductor
  exact hprimitive1.symm.trans (hconductor.trans hprimitive)

private lemma changeLevel_sq_eq_one
    {q m : ℕ} (hqm : q ∣ m)
    (chi : DirichletCharacter Complex q) (hsquare : chi ^ 2 = 1) :
    (chi.changeLevel hqm) ^ 2 = 1 := by
  rw [← map_pow, hsquare, map_one]

/-- The cross-level product of two square-principal characters is again
square-principal. -/
theorem goldfeldCrossLevelMul_sq_eq_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1) :
    (DirichletCharacter.mul chi1 chi) ^ 2 = 1 := by
  change
    (chi1.changeLevel (Nat.dvd_lcm_left q1 q) *
      chi.changeLevel (Nat.dvd_lcm_right q1 q)) ^ 2 = 1
  rw [mul_pow,
    changeLevel_sq_eq_one (Nat.dvd_lcm_left q1 q) chi1 hsquare1,
    changeLevel_sq_eq_one (Nat.dvd_lcm_right q1 q) chi hsquare,
    one_mul]

/-- A square-principal character cannot have principal cross-level product
with a distinct character. -/
theorem goldfeldCrossLevelMul_ne_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q)
    (hsquare1 : chi1 ^ 2 = 1)
    (hdistinct : goldfeldCharactersDistinct chi1 chi) :
    DirichletCharacter.mul chi1 chi ≠ 1 := by
  intro hprincipal
  apply hdistinct
  have hsquareLift := changeLevel_sq_eq_one
    (Nat.dvd_lcm_left q1 q) chi1 hsquare1
  have hproduct :
      chi1.changeLevel (Nat.dvd_lcm_left q1 q) *
          chi.changeLevel (Nat.dvd_lcm_right q1 q) = 1 := by
    simpa [DirichletCharacter.mul] using hprincipal
  have hinv :
      (chi1.changeLevel (Nat.dvd_lcm_left q1 q))⁻¹ =
        chi1.changeLevel (Nat.dvd_lcm_left q1 q) := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hsquareLift
  exact ((eq_inv_of_mul_eq_one_right hproduct).trans hinv).symm

/-- The product character's conductor is bounded by the product of the two
original levels, as used in the fixed-strip estimate. -/
theorem conductor_goldfeldCrossLevelMul_le
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q) :
    (DirichletCharacter.mul chi1 chi).conductor ≤ q1 * q := by
  exact Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q1) (NeZero.pos q))
    ((DirichletCharacter.mul chi1 chi).conductor_dvd_level.trans
      (Nat.lcm_dvd_mul q1 q))

end BoundedGaps.Maynard
