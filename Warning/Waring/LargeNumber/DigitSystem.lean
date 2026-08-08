import Waring.LargeNumber.DigitBounds
import Waring.LargeNumber.FiniteCode
import Waring.LargeNumber.FiniteTail
import Waring.LargeNumber.Scales

/-!
# Chen's eleven-coordinate digit system

This file instantiates the separated finite-code infrastructure with the digit
intervals in Chen's English Lemma 11 / Chinese Lemma 12
[CHEN1964-EN, pp. 1567-1568; CHEN1964-ZH, p. 733].
-/

namespace Waring.LargeNumber

open scoped BigOperators

/-- The scale attached to one of Chen's eleven digit coordinates. -/
def digitScale (p₁ : Nat) (i : Fin 11) : Nat := iterScale p₁ i

/-- Inclusive lower base endpoint at a digit coordinate.  The last endpoint is
zero, as explicitly printed in the English edition. -/
def digitBaseLower (p₁ : Nat) (i : Fin 11) : Nat :=
  if i = Fin.last 10 then 0 else digitLower (digitScale p₁ i)

/-- Inclusive upper base endpoint at a digit coordinate. -/
def digitBaseUpper (p₁ : Nat) (i : Fin 11) : Nat :=
  if i = Fin.last 10 then 17 * digitScale p₁ i / 10
  else 2 * digitScale p₁ i - 1

@[simp] theorem digitBaseLower_last (p₁ : Nat) :
    digitBaseLower p₁ (Fin.last 10) = 0 := by
  simp [digitBaseLower]

@[simp] theorem digitBaseUpper_last (p₁ : Nat) :
    digitBaseUpper p₁ (Fin.last 10) = 17 * iterScale p₁ 10 / 10 := by
  simp [digitBaseUpper, digitScale]

/-- Away from the special last coordinate, the ordinary lower endpoint is
used. -/
theorem digitBaseLower_of_ne_last (p₁ : Nat) {i : Fin 11}
    (hi : i ≠ Fin.last 10) :
    digitBaseLower p₁ i = digitLower (digitScale p₁ i) := by
  rw [digitBaseLower, if_neg hi]

/-- Away from the special last coordinate, the ordinary upper endpoint is
used. -/
theorem digitBaseUpper_of_ne_last (p₁ : Nat) {i : Fin 11}
    (hi : i ≠ Fin.last 10) :
    digitBaseUpper p₁ i = 2 * digitScale p₁ i - 1 := by
  rw [digitBaseUpper, if_neg hi]

@[simp] theorem digitBaseLower_castSucc (p₁ : Nat) (i : Fin 10) :
    digitBaseLower p₁ i.castSucc = digitLower (iterScale p₁ i) := by
  rw [digitBaseLower, if_neg (Fin.ne_of_lt i.castSucc_lt_last)]
  rfl

@[simp] theorem digitBaseUpper_castSucc (p₁ : Nat) (i : Fin 10) :
    digitBaseUpper p₁ i.castSucc = 2 * iterScale p₁ i - 1 := by
  rw [digitBaseUpper, if_neg (Fin.ne_of_lt i.castSucc_lt_last)]
  rfl

/-- Finite set of permitted bases at coordinate `i`. -/
def digitChoiceSet (p₁ : Nat) (i : Fin 11) : Finset Nat :=
  Finset.Icc (digitBaseLower p₁ i) (digitBaseUpper p₁ i)

/-- Type of permitted bases at coordinate `i`. -/
def DigitChoice (p₁ : Nat) (i : Fin 11) := ↥(digitChoiceSet p₁ i)

/-- Each finite digit-choice set supplies a finite choice type. -/
instance instFintypeDigitChoice (p₁ : Nat) (i : Fin 11) :
    Fintype (DigitChoice p₁ i) := by
  unfold DigitChoice
  infer_instance

/-- Fifth-power code attached to one permitted base. -/
def digitCode {p₁ : Nat} (i : Fin 11) (x : DigitChoice p₁ i) : Nat :=
  x.1 ^ 5

/-- Coordinatewise lower bound for the fifth-power code. -/
def digitCodeLower (p₁ : Nat) (i : Fin 11) : Nat :=
  digitBaseLower p₁ i ^ 5

/-- Coordinatewise upper bound for the fifth-power code. -/
def digitCodeUpper (p₁ : Nat) (i : Fin 11) : Nat :=
  digitBaseUpper p₁ i ^ 5

/-- Strict upper cap for a code beginning at coordinate `i`. -/
def digitCodeCap (p₁ : Nat) (i : Fin 11) : Nat :=
  (2 * digitScale p₁ i) ^ 5

/-- A digit choice is at least its coordinatewise lower base endpoint. -/
lemma digitChoice_lower {p₁ : Nat} {i : Fin 11} (x : DigitChoice p₁ i) :
    digitBaseLower p₁ i ≤ x.1 := by
  exact (Finset.mem_Icc.mp x.2).1

/-- A digit choice is at most its coordinatewise upper base endpoint. -/
lemma digitChoice_upper {p₁ : Nat} {i : Fin 11} (x : DigitChoice p₁ i) :
    x.1 ≤ digitBaseUpper p₁ i := by
  exact (Finset.mem_Icc.mp x.2).2

/-- Each coordinate fifth-power code is injective. -/
theorem digitCode_injective {p₁ : Nat} (i : Fin 11) :
    Function.Injective (digitCode (p₁ := p₁) i) := by
  intro x y h
  apply Subtype.ext
  exact fifthPower_injective h

/-- The fifth-power code is bounded below by the lower endpoint code. -/
lemma digitCode_lower {p₁ : Nat} (i : Fin 11) (x : DigitChoice p₁ i) :
    digitCodeLower p₁ i ≤ digitCode i x := by
  exact Nat.pow_le_pow_left (digitChoice_lower x) 5

/-- The fifth-power code is bounded above by the upper endpoint code. -/
lemma digitCode_upper {p₁ : Nat} (i : Fin 11) (x : DigitChoice p₁ i) :
    digitCode i x ≤ digitCodeUpper p₁ i := by
  exact Nat.pow_le_pow_left (digitChoice_upper x) 5

/-- The special last digit occupies less than `25 q^5`, despite having lower
endpoint zero. -/
theorem lastDigitUpper_pow_lt_twentyFive {q : Nat} (hq : 0 < q) :
    (17 * q / 10) ^ 5 < 25 * q ^ 5 := by
  have hscaled : 10 * (17 * q / 10) ≤ 17 * q := by omega
  have hpow := Nat.pow_le_pow_left hscaled 5
  have hqPow : 0 < q ^ 5 := pow_pos hq _
  norm_num [mul_pow] at hpow ⊢
  nlinarith

private theorem digitCodeUpper_last_lt_cap {p₁ : Nat}
    (hp₁ : 10 ^ 155 ≤ p₁) :
    digitCodeUpper p₁ (Fin.last 10) < digitCodeCap p₁ (Fin.last 10) := by
  have hs : 1000 ≤ iterScale p₁ 10 := by
    simpa using oneThousand_le_iterScale hp₁ (Fin.last 10)
  rw [digitCodeUpper, digitCodeCap, digitBaseUpper_last]
  change (17 * iterScale p₁ 10 / 10) ^ 5 < (2 * iterScale p₁ 10) ^ 5
  apply Nat.pow_lt_pow_left ?_ (by norm_num)
  apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)).2
  nlinarith

private theorem digitCodeUpper_add_cap_succ_lt {p₁ : Nat}
    (hp₁ : 10 ^ 155 ≤ p₁) (i : Fin 10) :
    digitCodeUpper p₁ i.castSucc + digitCodeCap p₁ i.succ <
      digitCodeCap p₁ i.castSucc := by
  have hpThousand : 1000 ≤ iterScale p₁ i := by
    simpa using oneThousand_le_iterScale hp₁ i.castSucc
  have hp : 10 ≤ iterScale p₁ i := by omega
  have h := digitUpper_add_next_lt hp (iterScale_succ_pow_five_le p₁ i)
  simpa [digitCodeUpper, digitCodeCap, digitScale] using h

/-- The sum of all coordinatewise upper codes from `i` onward stays strictly
below the cap `(2p_i)^5`. -/
theorem sum_digitCodeUpper_Ici_lt_cap {p₁ : Nat}
    (hp₁ : 10 ^ 155 ≤ p₁) (i : Fin 11) :
    (∑ j ∈ Finset.Ici i, digitCodeUpper p₁ j) < digitCodeCap p₁ i := by
  exact sum_Ici_lt_of_last_of_step _ _ (digitCodeUpper_last_lt_cap hp₁)
    (digitCodeUpper_add_cap_succ_lt hp₁) i

/-- The upper-code sum strictly after a nonfinal coordinate stays below the
next coordinate's cap. -/
theorem sum_digitCodeUpper_Ioi_lt_nextCap {p₁ : Nat}
    (hp₁ : 10 ^ 155 ≤ p₁) (i : Fin 10) :
    (∑ j ∈ Finset.Ioi i.castSucc, digitCodeUpper p₁ j) <
      digitCodeCap p₁ i.succ := by
  exact sum_Ioi_castSucc_lt_of_last_of_step _ _
    (digitCodeUpper_last_lt_cap hp₁)
    (digitCodeUpper_add_cap_succ_lt hp₁) i

private theorem digitCode_separates_closed_suffixes {p₁ : Nat}
    (hp₁ : 10 ^ 155 ≤ p₁) (i : Fin 11)
    (a b : DigitChoice p₁ i) (hab : digitCode i a < digitCode i b) :
    digitCode i a + (∑ j ∈ Finset.Ioi i, digitCodeUpper p₁ j) <
      digitCode i b + ∑ j ∈ Finset.Ioi i, digitCodeLower p₁ j := by
  by_cases hi : i = Fin.last 10
  · subst i
    rw [Ioi_last_eq_empty]
    simpa using hab
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    have hp : 1000 ≤ digitScale p₁ k.castSucc :=
      oneThousand_le_iterScale hp₁ k.castSucc
    have hq : 100 ≤ digitScale p₁ k.succ :=
      (by omega : 100 ≤ 1000) |>.trans
        (oneThousand_le_iterScale hp₁ k.succ)
    have hscale : digitScale p₁ k.succ ^ 5 ≤
        digitScale p₁ k.castSucc ^ 4 := by
      simpa [digitScale] using iterScale_succ_pow_five_le p₁ k
    have haLower : digitLower (digitScale p₁ k.castSucc) ≤ a.1 := by
      simpa [digitScale] using digitChoice_lower a
    have habBase : a.1 < b.1 := by
      apply (Nat.pow_lt_pow_iff_left (n := 5) (by norm_num)).mp
      exact hab
    by_cases hnext : k.succ = Fin.last 10
    · have hUpperEq :
          (∑ j ∈ Finset.Ioi k.castSucc, digitCodeUpper p₁ j) =
            digitCodeUpper p₁ k.succ := by
        rw [Ioi_castSucc_eq_Ici_succ, hnext, Ici_last_eq_singleton]
        simp
      have hLowerEq :
          (∑ j ∈ Finset.Ioi k.castSucc, digitCodeLower p₁ j) =
            digitCodeLower p₁ k.succ := by
        rw [Ioi_castSucc_eq_Ici_succ, hnext, Ici_last_eq_singleton]
        simp
      have hLastPos : 0 < iterScale p₁ 10 := by
        have ht : 1000 ≤ iterScale p₁ 10 := by
          simpa using oneThousand_le_iterScale hp₁ (Fin.last 10)
        omega
      have hUpper : digitCodeUpper p₁ k.succ <
          25 * digitScale p₁ k.succ ^ 5 := by
        calc
          digitCodeUpper p₁ k.succ = (17 * iterScale p₁ 10 / 10) ^ 5 := by
            rw [hnext, digitCodeUpper, digitBaseUpper_last]
          _ < 25 * iterScale p₁ 10 ^ 5 :=
            lastDigitUpper_pow_lt_twentyFive hLastPos
          _ = 25 * digitScale p₁ k.succ ^ 5 := by
            rw [hnext]
            rfl
      have hLower : digitCodeLower p₁ k.succ = 0 := by
        rw [hnext, digitCodeLower, digitBaseLower_last]
        norm_num
      have hgap := fifthPower_step_gap hp haLower
      have hmono : (a.1 + 1) ^ 5 ≤ b.1 ^ 5 :=
        Nat.pow_le_pow_left (by omega) 5
      have hscale' : 25 * digitScale p₁ k.succ ^ 5 ≤
          25 * digitScale p₁ k.castSucc ^ 4 :=
        Nat.mul_le_mul_left 25 hscale
      rw [hUpperEq, hLowerEq, hLower]
      calc
        digitCode k.castSucc a + digitCodeUpper p₁ k.succ <
            digitCode k.castSucc a + 25 * digitScale p₁ k.succ ^ 5 :=
          Nat.add_lt_add_left hUpper _
        _ ≤ digitCode k.castSucc a + 25 * digitScale p₁ k.castSucc ^ 4 :=
          Nat.add_le_add_left hscale' _
        _ ≤ (a.1 + 1) ^ 5 := by simpa [digitCode] using hgap
        _ ≤ digitCode k.castSucc b := by simpa [digitCode] using hmono
        _ = digitCode k.castSucc b + 0 := by omega
    · have hUpper := sum_digitCodeUpper_Ioi_lt_nextCap hp₁ k
      have hLower := le_sum_Ioi_castSucc (digitCodeLower p₁) k
      have hLocal := fifthPower_digit_separation hp hq hscale
        haLower habBase
      have hUpper' :
          (∑ j ∈ Finset.Ioi k.castSucc, digitCodeUpper p₁ j) <
            (2 * digitScale p₁ k.succ) ^ 5 := by
        simpa [digitCodeCap] using hUpper
      have hLower' : digitLower (digitScale p₁ k.succ) ^ 5 ≤
          ∑ j ∈ Finset.Ioi k.castSucc, digitCodeLower p₁ j := by
        have hEq : digitCodeLower p₁ k.succ =
            digitLower (digitScale p₁ k.succ) ^ 5 := by
          rw [digitCodeLower, digitBaseLower_of_ne_last p₁ hnext]
        rw [← hEq]
        exact hLower
      calc
        digitCode k.castSucc a +
            (∑ j ∈ Finset.Ioi k.castSucc, digitCodeUpper p₁ j) <
          digitCode k.castSucc a + (2 * digitScale p₁ k.succ) ^ 5 :=
            Nat.add_lt_add_left hUpper' _
        _ ≤ digitCode k.castSucc b +
            digitLower (digitScale p₁ k.succ) ^ 5 := by
          simpa [digitCode] using hLocal
        _ ≤ digitCode k.castSucc b +
            ∑ j ∈ Finset.Ioi k.castSucc, digitCodeLower p₁ j :=
          Nat.add_le_add_left hLower' _

/-- Distinct permitted eleven-tuples give distinct sums of fifth powers. -/
theorem chenDigitCode_injective {p₁ : Nat} (hp₁ : 10 ^ 155 ≤ p₁) :
    Function.Injective (finCode (digitCode (p₁ := p₁))) := by
  apply finCode_injective_of_closed_bounds
    (lower := digitCodeLower p₁) (upper := digitCodeUpper p₁)
  · exact digitCode_injective
  · exact digitCode_lower
  · exact digitCode_upper
  · exact digitCode_separates_closed_suffixes hp₁

/-- Every permitted eleven-coordinate sum is strictly below `(2p₁)^5`. -/
theorem chenDigitCode_lt {p₁ : Nat} (hp₁ : 10 ^ 155 ≤ p₁)
    (x : ∀ i, DigitChoice p₁ i) :
    finCode (digitCode (p₁ := p₁)) x < (2 * p₁) ^ 5 := by
  have hCode : finCode (digitCode (p₁ := p₁)) x ≤
      ∑ i, digitCodeUpper p₁ i :=
    Finset.sum_le_sum fun i _ ↦ digitCode_upper i (x i)
  have hCap := sum_digitCodeUpper_Ici_lt_cap hp₁ (0 : Fin 11)
  have hCap' : (∑ i, digitCodeUpper p₁ i) < (2 * p₁) ^ 5 := by
    simpa [digitCodeCap, digitScale, iterScale] using hCap
  exact hCode.trans_lt hCap'

end Waring.LargeNumber
