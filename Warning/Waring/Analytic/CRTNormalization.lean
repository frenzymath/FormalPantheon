import Waring.Analytic.ChenThree
import Waring.Analytic.Multiplicativity

/-!
# Standard-character normalization under the Chinese remainder theorem

This file identifies the two restricted characters in the CRT factorization
with standard additive characters multiplied by complementary modular
inverses. This is the coefficient normalization used in
[CHEN1964-EN, p. 1548; CHEN1964-ZH, p. 715].
-/

namespace Waring.Analytic

/-- Scaling a residue modulo `m` by `n` gives the CRT pair `(n*x, 0)`. -/
theorem chineseRemainder_zmodScale_left {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (x : ZMod m) :
    ZMod.chineseRemainder hcoprime (zmodScale m n x) = ((n : ZMod m) * x, 0) := by
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective x
  rw [zmodScale_intCast]
  apply Prod.ext
  · simp [ZMod.chineseRemainder]
  · simp [ZMod.chineseRemainder]

/-- The complementary scaling from residues modulo `n` into a modulus written
in the order `m*n`. -/
def zmodScaleRight (m n : Nat) : ZMod n →+ ZMod (m * n) :=
  (ZMod.ringEquivCongr (Nat.mul_comm n m)).toAddMonoidHom.comp (zmodScale n m)

@[simp] theorem zmodScaleRight_intCast (m n : Nat) (x : Int) :
    zmodScaleRight m n (x : ZMod n) = (m : ZMod (m * n)) * x := by
  simp [zmodScaleRight, zmodScale_intCast]

/-- Scaling a residue modulo `n` by `m` gives the CRT pair `(0, m*x)`. -/
theorem chineseRemainder_zmodScale_right {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (x : ZMod n) :
    ZMod.chineseRemainder hcoprime (zmodScaleRight m n x) = (0, (m : ZMod n) * x) := by
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective x
  rw [zmodScaleRight_intCast]
  apply Prod.ext
  · simp [ZMod.chineseRemainder]
  · simp [ZMod.chineseRemainder]

/-- The right complementary scaling also preserves the standard additive
character. -/
theorem stdAddChar_zmodScaleRight (m n : Nat) [NeZero m] [NeZero n] (x : ZMod n) :
    ZMod.stdAddChar (zmodScaleRight m n x) = ZMod.stdAddChar x := by
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective x
  rw [zmodScaleRight_intCast]
  rw [← Int.cast_natCast, ← Int.cast_mul, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hm : (m : Complex) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : Complex) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp [hm, hn]

/-- The left CRT restriction is the standard character modulo `m` multiplied
by the inverse of `n` modulo `m`. -/
theorem chineseRemainderCharacter_left_apply {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (x : ZMod m) :
    AddChar.leftFactor (chineseRemainderCharacter hcoprime) x =
      ZMod.stdAddChar ((n : ZMod m)⁻¹ * x) := by
  have hnUnit : IsUnit (n : ZMod m) :=
    (ZMod.isUnit_iff_coprime n m).mpr hcoprime.symm
  have hinverse :
      (ZMod.chineseRemainder hcoprime).symm (x, 0) =
        zmodScale m n ((n : ZMod m)⁻¹ * x) := by
    apply (ZMod.chineseRemainder hcoprime).injective
    rw [RingEquiv.apply_symm_apply]
    rw [chineseRemainder_zmodScale_left]
    rw [← mul_assoc, ZMod.mul_inv_of_unit _ hnUnit, one_mul]
  change ZMod.stdAddChar ((ZMod.chineseRemainder hcoprime).symm (x, 0)) = _
  rw [hinverse, stdAddChar_zmodScale]

/-- The right CRT restriction is the standard character modulo `n` multiplied
by the inverse of `m` modulo `n`. -/
theorem chineseRemainderCharacter_right_apply {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (x : ZMod n) :
    AddChar.rightFactor (chineseRemainderCharacter hcoprime) x =
      ZMod.stdAddChar ((m : ZMod n)⁻¹ * x) := by
  have hmUnit : IsUnit (m : ZMod n) :=
    (ZMod.isUnit_iff_coprime m n).mpr hcoprime
  have hinverse :
      (ZMod.chineseRemainder hcoprime).symm (0, x) =
        zmodScaleRight m n ((m : ZMod n)⁻¹ * x) := by
    apply (ZMod.chineseRemainder hcoprime).injective
    rw [RingEquiv.apply_symm_apply]
    rw [chineseRemainder_zmodScale_right]
    rw [← mul_assoc, ZMod.mul_inv_of_unit _ hmUnit, one_mul]
  change ZMod.stdAddChar ((ZMod.chineseRemainder hcoprime).symm (0, x)) = _
  rw [hinverse, stdAddChar_zmodScaleRight]

/-- CRT factorization with both restricted characters written as standard
characters and their complementary modular-inverse coefficients exposed. -/
theorem completePowerSum_mul_standard {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (k : Nat) (a : ZMod (m * n)) :
    completePowerSum k a =
      completePowerSum k
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a).1) *
        completePowerSum k
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a).2) := by
  rw [completePowerSum_mul hcoprime]
  apply congrArg₂ (fun x y : Complex ↦ x * y)
  · rw [powerSum, completePowerSum, powerSum]
    apply Finset.sum_congr rfl
    intro x _
    rw [chineseRemainderCharacter_left_apply]
    apply congrArg ZMod.stdAddChar
    ring
  · rw [powerSum, completePowerSum, powerSum]
    apply Finset.sum_congr rfl
    intro x _
    rw [chineseRemainderCharacter_right_apply]
    apply congrArg ZMod.stdAddChar
    ring

/-- A unit coefficient remains a unit in both normalized CRT factors. -/
theorem normalizedCrtCoefficients_isUnit {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) {a : ZMod (m * n)} (ha : IsUnit a) :
    IsUnit ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a).1) ∧
      IsUnit ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a).2) := by
  have hcomponents :
      IsUnit (ZMod.chineseRemainder hcoprime a).1 ∧
        IsUnit (ZMod.chineseRemainder hcoprime a).2 :=
    Prod.isUnit_iff.mp (ha.map (ZMod.chineseRemainder hcoprime).toRingHom)
  have hnUnit : IsUnit (n : ZMod m) :=
    (ZMod.isUnit_iff_coprime n m).mpr hcoprime.symm
  have hmUnit : IsUnit (m : ZMod n) :=
    (ZMod.isUnit_iff_coprime m n).mpr hcoprime
  have hnInv : IsUnit ((n : ZMod m)⁻¹) := by
    rcases hnUnit with ⟨u, hu⟩
    rw [← hu, ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have hmInv : IsUnit ((m : ZMod n)⁻¹) := by
    rcases hmUnit with ⟨u, hu⟩
    rw [← hu, ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  exact ⟨hnInv.mul hcomponents.1, hmInv.mul hcomponents.2⟩

-- These nonzero instances are retained in the reviewed CRT interface.  Its
-- statements deliberately use one uniform modulus contract across the file.
attribute [nolint unusedArguments]
  chineseRemainder_zmodScale_left
  chineseRemainder_zmodScale_right
  normalizedCrtCoefficients_isUnit

end Waring.Analytic
