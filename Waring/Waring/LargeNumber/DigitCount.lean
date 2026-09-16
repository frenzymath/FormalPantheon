import Waring.LargeNumber.DigitSystem
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Cardinality of Chen's digit family

This file counts the distinct sums constructed in Chen's English Lemma 11 /
Chinese Lemma 12 [CHEN1964-EN, pp. 1567-1568;
CHEN1964-ZH, p. 733].
-/

namespace Waring.LargeNumber

open scoped BigOperators

/-- Number of permitted bases at one coordinate. -/
def digitCount (p₁ : Nat) (i : Fin 11) : Nat := (digitChoiceSet p₁ i).card

/-- Exact cardinality of one inclusive digit interval. -/
theorem card_DigitChoice (p₁ : Nat) (i : Fin 11) :
    Fintype.card (DigitChoice p₁ i) = digitCount p₁ i := by
  change Fintype.card ↥(digitChoiceSet p₁ i) = _
  rw [Fintype.card_coe, digitCount]

/-- Closed formula for one digit count. -/
theorem digitCount_eq (p₁ : Nat) (i : Fin 11) :
    digitCount p₁ i = digitBaseUpper p₁ i + 1 - digitBaseLower p₁ i := by
  rw [digitCount, digitChoiceSet, Nat.card_Icc]

@[simp] theorem digitCount_last (p₁ : Nat) :
    digitCount p₁ (Fin.last 10) = 17 * iterScale p₁ 10 / 10 + 1 := by
  rw [digitCount_eq, digitBaseLower_last, digitBaseUpper_last]
  omega

/-- Each ordinary digit interval contains at least half its scale. -/
theorem digitScale_le_two_mul_card_DigitChoice {p₁ : Nat}
    (hp₁ : 10 ^ 155 ≤ p₁) (i : Fin 10) :
    digitScale p₁ i.castSucc ≤ 2 * digitCount p₁ i.castSucc := by
  have hs : 1000 ≤ digitScale p₁ i.castSucc :=
    oneThousand_le_iterScale hp₁ i.castSucc
  rw [digitCount_eq, digitBaseLower_castSucc, digitBaseUpper_castSucc]
  change iterScale p₁ i ≤
    2 * ((2 * iterScale p₁ i - 1 + 1) - digitLower (iterScale p₁ i))
  have hs' : 1000 ≤ iterScale p₁ i := by simpa [digitScale] using hs
  simp only [digitLower]
  omega

/-- Real form of the ordinary digit count. -/
theorem half_digitScale_le_card_DigitChoice {p₁ : Nat}
    (hp₁ : 10 ^ 155 ≤ p₁) (i : Fin 10) :
    (digitScale p₁ i.castSucc : Real) / 2 ≤
      digitCount p₁ i.castSucc := by
  have h := digitScale_le_two_mul_card_DigitChoice hp₁ i
  have hReal : (digitScale p₁ i.castSucc : Real) ≤
      2 * digitCount p₁ i.castSucc := by
    exact_mod_cast h
  linarith

/-- The inclusive last interval contains at least `17/10` times its scale. -/
theorem seventeen_mul_digitScale_le_ten_mul_card_last {p₁ : Nat}
    (hp₁ : 10 ^ 155 ≤ p₁) :
    17 * digitScale p₁ (Fin.last 10) ≤
      10 * digitCount p₁ (Fin.last 10) := by
  have hs : 1000 ≤ digitScale p₁ (Fin.last 10) :=
    oneThousand_le_iterScale hp₁ (Fin.last 10)
  rw [digitCount_last]
  change 17 * iterScale p₁ 10 ≤ 10 * (17 * iterScale p₁ 10 / 10 + 1)
  omega

/-- Generic real lower bound for the inclusive `floor (17n/10)` interval. -/
theorem seventeen_tenths_mul_le_div_add_one (n : Nat) :
    (17 / 10 : Real) * n ≤ ((17 * n / 10 + 1 : Nat) : Real) := by
  have hNat : 17 * n ≤ 10 * (17 * n / 10 + 1) := by omega
  have hReal : 17 * (n : Real) ≤
      10 * ((17 * n / 10 + 1 : Nat) : Real) := by
    exact_mod_cast hNat
  nlinarith

/-- Real form of the last digit count. -/
theorem seventeen_tenths_mul_lastScale_le_card (p₁ : Nat) :
    (17 / 10 : Real) * digitScale p₁ (Fin.last 10) ≤
      digitCount p₁ (Fin.last 10) := by
  rw [digitCount_last]
  change (17 / 10 : Real) * iterScale p₁ 10 ≤
    ((17 * iterScale p₁ 10 / 10 + 1 : Nat) : Real)
  exact seventeen_tenths_mul_le_div_add_one _

private theorem prod_half_digitScale_eq {p₁ : Nat} :
    (∏ i : Fin 10, (digitScale p₁ i.castSucc : Real) / 2) =
      (∏ i : Fin 10, (digitScale p₁ i.castSucc : Real)) / 2 ^ 10 := by
  simp_rw [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num [div_eq_mul_inv, inv_pow]

/-- Product of the eleven interval cardinalities has the source's elementary
`(17/10)/2^10` lower factor. -/
theorem digitScale_product_count_lower {p₁ : Nat}
    (hp₁ : 10 ^ 155 ≤ p₁) :
    (17 / 10 : Real) / 2 ^ 10 *
        (∏ i : Fin 11, (digitScale p₁ i : Real)) ≤
      ∏ i : Fin 11, (digitCount p₁ i : Real) := by
  have hOrdinary :
      (∏ i : Fin 10, (digitScale p₁ i.castSucc : Real) / 2) ≤
        ∏ i : Fin 10,
          (digitCount p₁ i.castSucc : Real) := by
    exact Finset.prod_le_prod
      (fun i _ ↦ div_nonneg (Nat.cast_nonneg _) (by norm_num))
      (fun i _ ↦ half_digitScale_le_card_DigitChoice hp₁ i)
  have hLast := seventeen_tenths_mul_lastScale_le_card p₁
  have hLastNonneg : 0 ≤
      (17 / 10 : Real) * digitScale p₁ (Fin.last 10) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hOrdinaryUpperNonneg : 0 ≤
      ∏ i : Fin 10, (digitCount p₁ i.castSucc : Real) :=
    Finset.prod_nonneg fun i _ ↦ Nat.cast_nonneg _
  have hMul := mul_le_mul hOrdinary hLast hLastNonneg
    hOrdinaryUpperNonneg
  rw [Fin.prod_univ_castSucc
    (fun i : Fin 11 ↦ (digitScale p₁ i : Real))]
  rw [Fin.prod_univ_castSucc
    (fun i : Fin 11 ↦ (digitCount p₁ i : Real))]
  calc
    (17 / 10 : Real) / 2 ^ 10 *
        ((∏ i : Fin 10, (digitScale p₁ i.castSucc : Real)) *
          digitScale p₁ (Fin.last 10)) =
      (∏ i : Fin 10, (digitScale p₁ i.castSucc : Real) / 2) *
        ((17 / 10 : Real) * digitScale p₁ (Fin.last 10)) := by
          rw [prod_half_digitScale_eq]
          ring
    _ ≤ (∏ i : Fin 10,
          (digitCount p₁ i.castSucc : Real)) *
        digitCount p₁ (Fin.last 10) := hMul

/-- Finite set of all fifth-power sums produced by Chen's permitted tuples. -/
def chenDigitSums (p₁ : Nat) : Finset Nat :=
  Finset.univ.image (finCode (digitCode (p₁ := p₁)))

/-- Injectivity turns the tuple-product count into the exact number of distinct
sums. -/
theorem card_chenDigitSums {p₁ : Nat} (hp₁ : 10 ^ 155 ≤ p₁) :
    (chenDigitSums p₁).card = ∏ i, digitCount p₁ i := by
  calc
    (chenDigitSums p₁).card = ∏ i, Fintype.card (DigitChoice p₁ i) :=
      card_finCode_image _ (chenDigitCode_injective hp₁)
    _ = ∏ i, digitCount p₁ i := by simp_rw [card_DigitChoice]

/-- Count lower bound transferred to the finite set of distinct sums. -/
theorem digitScale_product_le_card_chenDigitSums {p₁ : Nat}
    (hp₁ : 10 ^ 155 ≤ p₁) :
    (17 / 10 : Real) / 2 ^ 10 *
        (∏ i : Fin 11, (digitScale p₁ i : Real)) ≤
      ((chenDigitSums p₁).card : Real) := by
  rw [card_chenDigitSums hp₁, Nat.cast_prod]
  exact digitScale_product_count_lower hp₁

end Waring.LargeNumber
