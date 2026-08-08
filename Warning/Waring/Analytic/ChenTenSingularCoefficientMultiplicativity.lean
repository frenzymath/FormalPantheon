import Waring.Analytic.ChenTenSingularCoefficient
import Waring.Analytic.CRTNormalization

/-!
# Multiplicativity of Chen's finite singular coefficient

This file proves the coprime product formula for the finite coefficients in
Chen's Lemma 10.  The reindexing uses CRT coordinates normalized by the
inverse of the complementary modulus [CHEN1964-EN, pp. 1560-1567;
CHEN1964-ZH, pp. 727-733].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- CRT followed by the complementary-inverse normalization used by the
complete-power-sum factorization. -/
noncomputable def normalizedCrtEquiv {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) : ZMod (m * n) ≃ ZMod m × ZMod n where
  toFun a :=
    ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a).1,
      (m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a).2)
  invFun bc :=
    (ZMod.chineseRemainder hcoprime).symm
      ((n : ZMod m) * bc.1, (m : ZMod n) * bc.2)
  left_inv a := by
    have hnUnit : IsUnit (n : ZMod m) :=
      (ZMod.isUnit_iff_coprime n m).mpr hcoprime.symm
    have hmUnit : IsUnit (m : ZMod n) :=
      (ZMod.isUnit_iff_coprime m n).mpr hcoprime
    apply (ZMod.chineseRemainder hcoprime).injective
    rw [RingEquiv.apply_symm_apply]
    apply Prod.ext
    · change (n : ZMod m) *
          ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a).1) = _
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ hnUnit, one_mul]
    · change (m : ZMod n) *
          ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a).2) = _
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ hmUnit, one_mul]
  right_inv bc := by
    have hnUnit : IsUnit (n : ZMod m) :=
      (ZMod.isUnit_iff_coprime n m).mpr hcoprime.symm
    have hmUnit : IsUnit (m : ZMod n) :=
      (ZMod.isUnit_iff_coprime m n).mpr hcoprime
    apply Prod.ext
    · change (n : ZMod m)⁻¹ *
          ((ZMod.chineseRemainder hcoprime
            ((ZMod.chineseRemainder hcoprime).symm
              ((n : ZMod m) * bc.1, (m : ZMod n) * bc.2))).1) = bc.1
      rw [RingEquiv.apply_symm_apply]
      rw [← mul_assoc, ZMod.inv_mul_of_unit _ hnUnit, one_mul]
    · change (m : ZMod n)⁻¹ *
          ((ZMod.chineseRemainder hcoprime
            ((ZMod.chineseRemainder hcoprime).symm
              ((n : ZMod m) * bc.1, (m : ZMod n) * bc.2))).2) = bc.2
      rw [RingEquiv.apply_symm_apply]
      rw [← mul_assoc, ZMod.inv_mul_of_unit _ hmUnit, one_mul]

/-- The standard character factors in the same normalized CRT coordinates as
the complete fifth-power sum. -/
theorem stdAddChar_eq_mul_normalizedCrt {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (a : ZMod (m * n)) :
    ZMod.stdAddChar a =
      ZMod.stdAddChar ((normalizedCrtEquiv hcoprime a).1) *
        ZMod.stdAddChar ((normalizedCrtEquiv hcoprime a).2) := by
  rw [← show chineseRemainderCharacter hcoprime
      (ZMod.chineseRemainder hcoprime a) = ZMod.stdAddChar a by
    simp [chineseRemainderCharacter, AddChar.transport]]
  change chineseRemainderCharacter hcoprime
      (ZMod.chineseRemainder hcoprime a) =
        ZMod.stdAddChar
            ((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a).1) *
          ZMod.stdAddChar
            ((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a).2)
  rw [show ZMod.chineseRemainder hcoprime a =
      ((ZMod.chineseRemainder hcoprime a).1, 0) +
        (0, (ZMod.chineseRemainder hcoprime a).2) by ext <;> simp]
  rw [AddChar.map_add_eq_mul]
  change AddChar.leftFactor (chineseRemainderCharacter hcoprime)
        (ZMod.chineseRemainder hcoprime a).1 *
      AddChar.rightFactor (chineseRemainderCharacter hcoprime)
        (ZMod.chineseRemainder hcoprime a).2 = _
  rw [chineseRemainderCharacter_left_apply,
    chineseRemainderCharacter_right_apply]
  simp

/-- Normalized CRT coordinates preserve and reflect the unit condition. -/
theorem isUnit_normalizedCrtEquiv_iff {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (a : ZMod (m * n)) :
    IsUnit (normalizedCrtEquiv hcoprime a).1 ∧
        IsUnit (normalizedCrtEquiv hcoprime a).2 ↔ IsUnit a := by
  constructor
  · intro h
    have hnUnit : IsUnit (n : ZMod m) :=
      (ZMod.isUnit_iff_coprime n m).mpr hcoprime.symm
    have hmUnit : IsUnit (m : ZMod n) :=
      (ZMod.isUnit_iff_coprime m n).mpr hcoprime
    have hpair : IsUnit
        ((n : ZMod m) * (normalizedCrtEquiv hcoprime a).1,
          (m : ZMod n) * (normalizedCrtEquiv hcoprime a).2) :=
      Prod.isUnit_iff.mpr ⟨hnUnit.mul h.1, hmUnit.mul h.2⟩
    have himage := hpair.map (ZMod.chineseRemainder hcoprime).symm.toRingHom
    change IsUnit
      ((normalizedCrtEquiv hcoprime).symm (normalizedCrtEquiv hcoprime a)) at himage
    simpa using himage
  · exact normalizedCrtCoefficients_isUnit hcoprime

/-- The target character in a singular-coefficient summand splits in
normalized CRT coordinates. -/
theorem stdAddChar_neg_mul_eq_mul_normalizedCrt
    {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (N : Nat) (a : ZMod (m * n)) :
    ZMod.stdAddChar (-a * (N : ZMod (m * n))) =
      ZMod.stdAddChar
          (-(normalizedCrtEquiv hcoprime a).1 * (N : ZMod m)) *
        ZMod.stdAddChar
          (-(normalizedCrtEquiv hcoprime a).2 * (N : ZMod n)) := by
  rw [stdAddChar_eq_mul_normalizedCrt hcoprime
    (-a * (N : ZMod (m * n)))]
  apply congrArg₂ (fun x y : Complex ↦ x * y)
  · apply congrArg ZMod.stdAddChar
    change (n : ZMod m)⁻¹ *
        (ZMod.chineseRemainder hcoprime
          (-a * (N : ZMod (m * n)))).1 =
      -((n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime a).1) *
        (N : ZMod m)
    simp
    ring
  · apply congrArg ZMod.stdAddChar
    change (m : ZMod n)⁻¹ *
        (ZMod.chineseRemainder hcoprime
          (-a * (N : ZMod (m * n)))).2 =
      -((m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime a).2) *
        (N : ZMod n)
    simp
    ring

/-- One singular-coefficient summand factors over normalized CRT
coordinates. -/
theorem chenTenSingularTerm_mul {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (N : Nat) (a : ZMod (m * n)) :
    chenTenSingularTerm (m * n) N a =
      chenTenSingularTerm m N (normalizedCrtEquiv hcoprime a).1 *
        chenTenSingularTerm n N (normalizedCrtEquiv hcoprime a).2 := by
  have hm : (m : Complex) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : Complex) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hdiv :
      (completePowerSum 5 (normalizedCrtEquiv hcoprime a).1 *
          completePowerSum 5 (normalizedCrtEquiv hcoprime a).2) /
          ((m * n : Nat) : Complex) =
        (completePowerSum 5 (normalizedCrtEquiv hcoprime a).1 /
            (m : Complex)) *
          (completePowerSum 5 (normalizedCrtEquiv hcoprime a).2 /
            (n : Complex)) := by
    rw [Nat.cast_mul]
    field_simp [hm, hn]
  unfold chenTenSingularTerm
  rw [completePowerSum_mul_standard hcoprime]
  change
    ((completePowerSum 5 (normalizedCrtEquiv hcoprime a).1 *
          completePowerSum 5 (normalizedCrtEquiv hcoprime a).2) /
        ((m * n : Nat) : Complex)) ^ 15 *
        ZMod.stdAddChar (-a * (N : ZMod (m * n))) = _
  rw [hdiv, mul_pow,
    stdAddChar_neg_mul_eq_mul_normalizedCrt hcoprime]
  ring

/-- Chen's finite singular coefficient is multiplicative in coprime positive
moduli. -/
theorem chenTenSingularCoefficient_mul {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (N : Nat) :
    chenTenSingularCoefficient (m * n) N =
      chenTenSingularCoefficient m N * chenTenSingularCoefficient n N := by
  unfold chenTenSingularCoefficient
  calc
    (∑ a : ZMod (m * n),
        if IsUnit a then chenTenSingularTerm (m * n) N a else 0) =
        ∑ bc : ZMod m × ZMod n,
          if IsUnit bc.1 ∧ IsUnit bc.2 then
            chenTenSingularTerm m N bc.1 * chenTenSingularTerm n N bc.2
          else 0 := by
      apply Fintype.sum_equiv (normalizedCrtEquiv hcoprime)
      intro a
      have hunit :
          IsUnit a ↔
            IsUnit (normalizedCrtEquiv hcoprime a).1 ∧
              IsUnit (normalizedCrtEquiv hcoprime a).2 :=
        (isUnit_normalizedCrtEquiv_iff hcoprime a).symm
      by_cases ha : IsUnit a
      · rw [if_pos ha, if_pos (hunit.mp ha),
          chenTenSingularTerm_mul hcoprime]
      · have hcoordinates :
            ¬(IsUnit (normalizedCrtEquiv hcoprime a).1 ∧
              IsUnit (normalizedCrtEquiv hcoprime a).2) := by
          exact fun h ↦ ha (hunit.mpr h)
        rw [if_neg ha, if_neg hcoordinates]
    _ = ∑ b : ZMod m, ∑ c : ZMod n,
        if IsUnit b ∧ IsUnit c then
          chenTenSingularTerm m N b * chenTenSingularTerm n N c
        else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ b : ZMod m, ∑ c : ZMod n,
        (if IsUnit b then chenTenSingularTerm m N b else 0) *
          (if IsUnit c then chenTenSingularTerm n N c else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      by_cases hb : IsUnit b <;> by_cases hc : IsUnit c <;> simp [hb, hc]
    _ = (∑ b : ZMod m,
          if IsUnit b then chenTenSingularTerm m N b else 0) *
        ∑ c : ZMod n,
          if IsUnit c then chenTenSingularTerm n N c else 0 := by
      rw [Finset.sum_mul_sum]

-- The equivalence retains both nonzero modulus instances to match the CRT
-- coefficient API whose inverse laws and consumers require the same contract.
attribute [nolint unusedArguments] normalizedCrtEquiv

end Waring.Analytic
