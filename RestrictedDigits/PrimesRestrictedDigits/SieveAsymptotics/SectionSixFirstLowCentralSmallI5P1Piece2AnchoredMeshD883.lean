import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0AnalyticD816
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece2AnchoredMeshD883 -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

private abbrev L : Real → Real := sectionSixFirstLowCentralSmallI5P1D807L
private abbrev Q4 : Real → Real → Real := sectionSixFirstLowCentralSmallI5P1D816Row0Q4
private abbrev Prim : Real → Real → Real := sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive

private def qCoeff (a : Real) (i : Nat) : Real := (-1 : Real) ^ i / a ^ (i + 1)

private def upperIntegrand (a d r : Real) : Real :=
  Q4 a r * Prim a (L d - r)

private def upperExpanded (a d r : Real) : Real :=
  let l := L d
  ∑ i ∈ Finset.range 5,
    (∑ j ∈ Finset.range 5,
      (∑ k ∈ Finset.range (j + 2),
          (qCoeff a i * qCoeff a j * (j + 1 : Nat).choose k * (-1 : Real) ^ k /
              (j + 1 : Real)) *
            l ^ (j + 1 - k) * r ^ (i + k)))

private theorem upper_pointwise (a d r : Real) :
    upperIntegrand a d r = upperExpanded a d r := by
  simp [upperIntegrand, upperExpanded, qCoeff,
    sectionSixFirstLowCentralSmallI5P1D814Q4,
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive,
    sectionSixFirstLowCentralSmallI5P1D807L,
    Finset.sum_range_succ, Nat.choose]
  ring

private theorem intervalIntegrable_sum
    {ι : Type} (s : Finset ι) (f : ι → Real → Real)
    {u v : Real}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume u v) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume u v := by
  exact (IntervalIntegrable.sum s hf).congr (by
    intro x hx
    simp [Finset.sum_apply])

private theorem monomial_integral
    (C l m h : Real) (i j k : Nat) :
    (∫ r in m..h, (C / (j + 1 : Real)) * l ^ (j + 1 - k) * r ^ (i + k)) =
      (C / ((j + 1 : Real) * (i + k + 1 : Real))) * l ^ (j + 1 - k) *
        (h ^ (i + k + 1) - m ^ (i + k + 1)) := by
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have hj : (0 : Real) < (j + 1 : Nat) := by positivity
  have hik : (0 : Real) < (i + k + 1 : Nat) := by positivity
  field_simp [ne_of_gt hj, ne_of_gt hik]
  norm_num [Nat.cast_add]

private theorem upper_integral_eq_sum (a d : Real) :
    (∫ r in L d / 2..L d, upperIntegrand a d r) =
      ∑ i ∈ Finset.range 5,
        (∑ j ∈ Finset.range 5,
          (∑ k ∈ Finset.range (j + 2),
            (qCoeff a i * qCoeff a j * (j + 1 : Nat).choose k * (-1 : Real) ^ k /
              ((j + 1 : Real) * (i + k + 1 : Real))) *
              L d ^ (j + 1 - k) *
                (L d ^ (i + k + 1) - (L d / 2) ^ (i + k + 1)))) := by
  rw [intervalIntegral.integral_congr (fun r hr => upper_pointwise a d r)]
  simp only [upperExpanded]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k hk
        simpa [mul_assoc] using
          monomial_integral
            (qCoeff a i * qCoeff a j * (j + 1 : Nat).choose k * (-1 : Real) ^ k)
            (L d) (L d / 2) (L d) i j k
      · intro k hk
        have hc : Continuous (fun r : Real =>
            (qCoeff a i * qCoeff a j * (j + 1 : Nat).choose k * (-1 : Real) ^ k /
              (j + 1 : Real)) * L d ^ (j + 1 - k) * r ^ (i + k)) := by
          fun_prop
        exact hc.intervalIntegrable (μ := volume) (L d / 2) (L d)
    · intro j hj
      apply intervalIntegrable_sum
      intro k hk
      have hc : Continuous (fun r : Real =>
          (qCoeff a i * qCoeff a j * (j + 1 : Nat).choose k * (-1 : Real) ^ k /
            (j + 1 : Real)) * L d ^ (j + 1 - k) * r ^ (i + k)) := by
        fun_prop
      exact hc.intervalIntegrable (μ := volume) (L d / 2) (L d)
  · intro i hi
    apply intervalIntegrable_sum
    intro j hj
    apply intervalIntegrable_sum
    intro k hk
    have hc : Continuous (fun r : Real =>
        (qCoeff a i * qCoeff a j * (j + 1 : Nat).choose k * (-1 : Real) ^ k /
          (j + 1 : Real)) * L d ^ (j + 1 - k) * r ^ (i + k)) := by
      fun_prop
    exact hc.intervalIntegrable (μ := volume) (L d / 2) (L d)

private def ratA : Rat := 180001 / 500000
private def ratDr : Rat := 84167 / 500000
private def ratD1 : Rat := 180001 / 1000000
private def ratBeta : Rat := 212499 / 500000
private def ratGap : Rat := 16249 / 250000
private def ratM : Rat := 70893 / 125000

private def ratF2 : Rat := 1 / 4
private def ratF3 : Rat := -1 / 6
private def ratF4 : Rat := 5 / 48
private def ratF5 : Rat := -1 / 15
private def ratF6 : Rat := 2 / 45
private def ratF7 : Rat := -1 / 140
private def ratF8 : Rat := 11 / 6720
private def ratF9 : Rat := -1 / 2520
private def ratF10 : Rat := 1 / 12600

private def ratLower (i : Nat) : Rat :=
  ratDr + (i : Rat) * (ratD1 - ratDr) / 128

private def ratUpper (i : Nat) : Rat :=
  ratDr + ((i + 1 : Nat) : Rat) * (ratD1 - ratDr) / 128

private def ratFactor (i : Nat) : Rat :=
  ratM / (ratBeta - ratUpper i) * (1 / ratGap - 1 / (ratUpper i - ratGap))

private def ratAreaCoeff (a : Rat) : Fin 11 → Rat := ![
  ratF2 * ratA ^ 2 / a ^ 2 +
    ratF3 * ratA ^ 3 / a ^ 3 +
    ratF4 * ratA ^ 4 / a ^ 4 +
    ratF5 * ratA ^ 5 / a ^ 5 +
    ratF6 * ratA ^ 6 / a ^ 6 +
    ratF7 * ratA ^ 7 / a ^ 7 +
    ratF8 * ratA ^ 8 / a ^ 8 +
    ratF9 * ratA ^ 9 / a ^ 9 +
    ratF10 * ratA ^ 10 / a ^ 10,
  (-2 : Rat) * (ratF2 * 2 * ratA / a ^ 2 + ratF3 * 3 * ratA ^ 2 / a ^ 3 +
    ratF4 * 4 * ratA ^ 3 / a ^ 4 + ratF5 * 5 * ratA ^ 4 / a ^ 5 +
    ratF6 * 6 * ratA ^ 5 / a ^ 6 + ratF7 * 7 * ratA ^ 6 / a ^ 7 +
    ratF8 * 8 * ratA ^ 7 / a ^ 8 + ratF9 * 9 * ratA ^ 8 / a ^ 9 +
    ratF10 * 10 * ratA ^ 9 / a ^ 10),
  (-2 : Rat)^2 * (ratF2 / a ^ 2 + ratF3 * 3 * ratA / a ^ 3 +
    ratF4 * 6 * ratA ^ 2 / a ^ 4 + ratF5 * 10 * ratA ^ 3 / a ^ 5 +
    ratF6 * 15 * ratA ^ 4 / a ^ 6 + ratF7 * 21 * ratA ^ 5 / a ^ 7 +
    ratF8 * 28 * ratA ^ 6 / a ^ 8 + ratF9 * 36 * ratA ^ 7 / a ^ 9 +
    ratF10 * 45 * ratA ^ 8 / a ^ 10),
  (-2 : Rat)^3 * (ratF3 / a ^ 3 + ratF4 * 4 * ratA / a ^ 4 +
    ratF5 * 10 * ratA ^ 2 / a ^ 5 + ratF6 * 20 * ratA ^ 3 / a ^ 6 +
    ratF7 * 35 * ratA ^ 4 / a ^ 7 + ratF8 * 56 * ratA ^ 5 / a ^ 8 +
    ratF9 * 84 * ratA ^ 6 / a ^ 9 + ratF10 * 120 * ratA ^ 7 / a ^ 10),
  (-2 : Rat)^4 * (ratF4 / a ^ 4 + ratF5 * 5 * ratA / a ^ 5 +
    ratF6 * 15 * ratA ^ 2 / a ^ 6 + ratF7 * 35 * ratA ^ 3 / a ^ 7 +
    ratF8 * 70 * ratA ^ 4 / a ^ 8 + ratF9 * 126 * ratA ^ 5 / a ^ 9 +
    ratF10 * 210 * ratA ^ 6 / a ^ 10),
  (-2 : Rat)^5 * (ratF5 / a ^ 5 + ratF6 * 6 * ratA / a ^ 6 +
    ratF7 * 21 * ratA ^ 2 / a ^ 7 + ratF8 * 56 * ratA ^ 3 / a ^ 8 +
    ratF9 * 126 * ratA ^ 4 / a ^ 9 + ratF10 * 252 * ratA ^ 5 / a ^ 10),
  (-2 : Rat)^6 * (ratF6 / a ^ 6 + ratF7 * 7 * ratA / a ^ 7 +
    ratF8 * 28 * ratA ^ 2 / a ^ 8 + ratF9 * 84 * ratA ^ 3 / a ^ 9 +
    ratF10 * 210 * ratA ^ 4 / a ^ 10),
  (-2 : Rat)^7 * (ratF7 / a ^ 7 + ratF8 * 8 * ratA / a ^ 8 +
    ratF9 * 36 * ratA ^ 2 / a ^ 9 + ratF10 * 120 * ratA ^ 3 / a ^ 10),
  (-2 : Rat)^8 * (ratF8 / a ^ 8 + ratF9 * 9 * ratA / a ^ 9 +
    ratF10 * 45 * ratA ^ 2 / a ^ 10),
  (-2 : Rat)^9 * (ratF9 / a ^ 9 + ratF10 * 10 * ratA / a ^ 10),
  (-2 : Rat)^10 * (ratF10 / a ^ 10)
]

private def ratAreaIntegral (i : Nat) : Rat :=
  ∑ n : Fin 11,
    ratAreaCoeff (ratLower i) n *
      (ratUpper i ^ ((n : Nat) + 1) - ratLower i ^ ((n : Nat) + 1)) /
        ((n : Nat) + 1 : Nat)

private def ratRowTerm (i : Nat) : Rat := ratFactor i * ratAreaIntegral i

private def realAreaPoly (a : Rat) (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D814FinPoly
    (fun n : Fin 11 => (ratAreaCoeff a n : Real)) d

private theorem h_eq_cast_sub (d : Real) :
    sectionSixFirstLowCentralSmallI5P1D807L d = (ratA : Real) - 2 * d := by
  have hA := sectionSixFirstLowCentralSmallI5P1D807_constants.1
  unfold sectionSixFirstLowCentralSmallI5P1D807L
  rw [hA]
  norm_num [ratA]

private theorem case2_eq_realAreaPoly (a : Rat) (ha : a ≠ 0) (d : Real) :
    (Prim (a : Real) (L d / 2)) ^ 2 / 2 +
      ∫ r in L d / 2..L d, Q4 (a : Real) r * Prim (a : Real) (L d - r) =
      realAreaPoly a d := by
  have haR : (a : Real) ≠ 0 := by exact_mod_cast ha
  change Prim (a : Real) (L d / 2) ^ 2 / 2 +
      (∫ r in L d / 2..L d, upperIntegrand (a : Real) d r) =
      realAreaPoly a d
  rw [upper_integral_eq_sum]
  unfold realAreaPoly
  unfold Prim
  unfold sectionSixFirstLowCentralSmallI5P1D814FinPoly
  simp only [sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
  unfold L
  rw [h_eq_cast_sub]
  simp [ratAreaCoeff, ratF2, ratF3, ratF4, ratF5, ratF6, ratF7, ratF8,
    ratF9, ratF10, qCoeff, Fin.sum_univ_succ, Finset.sum_range_succ, Nat.choose]
  field_simp [haR]
  ring

private theorem realAreaPoly_integral_eq_cast (a lo hi : Rat) :
    (∫ d in (lo : Real)..(hi : Real), realAreaPoly a d) =
      ((∑ n : Fin 11,
        ratAreaCoeff a n *
          (hi ^ ((n : Nat) + 1) - lo ^ ((n : Nat) + 1)) /
            ((n : Nat) + 1 : Nat) : Rat) : Real) := by
  unfold realAreaPoly
  rw [sectionSixFirstLowCentralSmallI5P1D814_intervalIntegral_finPoly]
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  norm_num

private abbrev RowLower (i : Fin 128) : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Dr +
    (i : Real) * (sectionSixFirstLowCentralSmallI5P1D807D1 -
      sectionSixFirstLowCentralSmallI5P1D807Dr) / 128

private abbrev RowUpper (i : Fin 128) : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Dr +
    (((i : Nat) + 1 : Nat) : Real) *
      (sectionSixFirstLowCentralSmallI5P1D807D1 -
        sectionSixFirstLowCentralSmallI5P1D807Dr) / 128

private theorem row_first : RowLower (0 : Fin 128) =
    sectionSixFirstLowCentralSmallI5P1D807Dr := by
  simp [RowLower]

private theorem row_last : RowUpper (⟨127, by norm_num⟩ : Fin 128) =
    sectionSixFirstLowCentralSmallI5P1D807D1 := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, _, hDr, hD1⟩
  simp [RowUpper, hDr, hD1]

private theorem row_adjacent {i : Fin 128} (h : i.1 + 1 < 128) :
    RowUpper i = RowLower ⟨i.1 + 1, h⟩ := by
  simp only [RowUpper, RowLower]

private theorem row_endpoint_order (i : Fin 128) : RowLower i ≤ RowUpper i := by
  have hi : (i : Real) ≤ (((i : Nat) + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ i.1
  have hw : 0 ≤ sectionSixFirstLowCentralSmallI5P1D807D1 -
      sectionSixFirstLowCentralSmallI5P1D807Dr := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, _, _, _, hDr, hD1⟩
    rw [hDr, hD1]
    norm_num
  dsimp [RowLower, RowUpper]
  have h := mul_le_mul_of_nonneg_right hi
    (div_nonneg hw (by norm_num : (0 : Real) ≤ 128))
  linarith

private theorem row_signs (i : Fin 128) :
    0 < RowLower i ∧
      RowUpper i < sectionSixFirstLowCentralSmallI5P1D807Beta ∧
      0 < sectionSixFirstLowCentralSmallI5P1D807Gap ∧
      0 < RowUpper i - sectionSixFirstLowCentralSmallI5P1D807Gap := by
  have hi0 : (0 : Real) ≤ (i : Real) := by positivity
  have hi128 : (((i : Nat) + 1 : Nat) : Real) ≤ 128 := by
    exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hw : 0 ≤ sectionSixFirstLowCentralSmallI5P1D807D1 -
      sectionSixFirstLowCentralSmallI5P1D807Dr := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, _, _, _, hDr, hD1⟩
    rw [hDr, hD1]
    norm_num
  have hlow : sectionSixFirstLowCentralSmallI5P1D807Dr ≤ RowLower i := by
    dsimp [RowLower]
    nlinarith [mul_nonneg hi0 hw]
  have hupp : RowUpper i ≤ sectionSixFirstLowCentralSmallI5P1D807D1 := by
    dsimp [RowUpper]
    have hm := mul_le_mul_of_nonneg_right hi128
      (div_nonneg hw (by norm_num : (0 : Real) ≤ 128))
    nlinarith
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, hBeta, hGap, _, _, hDr, hD1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hDr] at hlow
    norm_num at hlow ⊢
    linarith
  · rw [hD1] at hupp
    rw [hBeta]
    norm_num at hupp ⊢
    linarith
  · rw [hGap]
    norm_num
  · have hUG : sectionSixFirstLowCentralSmallI5P1D807Dr ≤ RowUpper i :=
      hlow.trans (row_endpoint_order i)
    rw [sub_pos, hGap]
    rw [hDr] at hUG
    norm_num at hUG ⊢
    linarith

private abbrev RowFactor (i : Fin 128) : Real :=
  (70893 / 125000 : Real) /
      (sectionSixFirstLowCentralSmallI5P1D807Beta - RowUpper i) *
    (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
      1 / (RowUpper i - sectionSixFirstLowCentralSmallI5P1D807Gap))

def sectionSixFirstLowCentralSmallI5P1D883P2AnchoredRowMajorant
    (i : Fin 128) (d : Real) : Real :=
  let a := sectionSixFirstLowCentralSmallI5P1D807Dr +
    (i : Real) *
      (sectionSixFirstLowCentralSmallI5P1D807D1 -
        sectionSixFirstLowCentralSmallI5P1D807Dr) / 128
  let b := sectionSixFirstLowCentralSmallI5P1D807Dr +
    (((i : Nat) + 1 : Nat) : Real) *
      (sectionSixFirstLowCentralSmallI5P1D807D1 -
        sectionSixFirstLowCentralSmallI5P1D807Dr) / 128
  ((70893 / 125000 : Real) /
      (sectionSixFirstLowCentralSmallI5P1D807Beta - b) *
      (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
        1 / (b - sectionSixFirstLowCentralSmallI5P1D807Gap))) *
    ((sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a
        (sectionSixFirstLowCentralSmallI5P1D807L d / 2)) ^ 2 / 2 +
      ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
          sectionSixFirstLowCentralSmallI5P1D807L d,
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a
            (sectionSixFirstLowCentralSmallI5P1D807L d - r))

private theorem rowLower_eq_cast (i : Fin 128) :
    RowLower i = (ratLower i.1 : Real) := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, _, hDr, hD1⟩
  simp only [RowLower, ratLower]
  rw [hDr, hD1]
  norm_num [ratDr, ratD1]

private theorem rowUpper_eq_cast (i : Fin 128) :
    RowUpper i = (ratUpper i.1 : Real) := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, _, hDr, hD1⟩
  simp only [RowUpper, ratUpper]
  rw [hDr, hD1]
  norm_num [ratDr, ratD1]

private theorem ratLower_ne_zero (i : Fin 128) : ratLower i.1 ≠ 0 := by
  have hi : (0 : Rat) ≤ i.1 := by positivity
  unfold ratLower ratDr ratD1
  norm_num
  positivity

private theorem rowFactor_eq_cast (i : Fin 128) :
    RowFactor i = (ratFactor i.1 : Real) := by
  rcases row_signs i with ⟨_, hβpos, hGpos, hUGpos⟩
  have hβne := ne_of_gt hβpos
  have hGne := ne_of_gt hGpos
  have hUGne := ne_of_gt hUGpos
  change (70893 / 125000 : Real) /
      (sectionSixFirstLowCentralSmallI5P1D807Beta - RowUpper i) *
      (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
        1 / (RowUpper i - sectionSixFirstLowCentralSmallI5P1D807Gap)) = _
  rw [rowUpper_eq_cast]
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, hBeta, hGap, _, _, _, _⟩
  rw [hBeta, hGap]
  norm_num [ratFactor, ratM, ratBeta, ratGap, hβne, hGne, hUGne]

private abbrev RowCase2 (i : Fin 128) (d : Real) : Real :=
  (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
      (RowLower i) (sectionSixFirstLowCentralSmallI5P1D807L d / 2)) ^ 2 / 2 +
    ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
        sectionSixFirstLowCentralSmallI5P1D807L d,
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (RowLower i) r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
          (RowLower i) (sectionSixFirstLowCentralSmallI5P1D807L d - r)

private theorem rowIntegral_eq_cast (i : Fin 128) :
    (∫ d in RowLower i..RowUpper i, RowFactor i * RowCase2 i d) =
      (ratRowTerm i.1 : Real) := by
  simp only [rowLower_eq_cast i, rowUpper_eq_cast i]
  unfold RowCase2
  simp_rw [rowLower_eq_cast i]
  rw [intervalIntegral.integral_const_mul, rowFactor_eq_cast]
  rw [intervalIntegral.integral_congr (fun d hd =>
    case2_eq_realAreaPoly (ratLower i.1) (ratLower_ne_zero i) d)]
  rw [realAreaPoly_integral_eq_cast]
  unfold ratRowTerm ratAreaIntegral
  norm_num

private theorem ratRowSum_lt :
    (Finset.sum (Finset.range 128) ratRowTerm) <
      (14111 / 62500000 : Rat) := by
  norm_num [ratRowTerm, ratAreaIntegral, ratAreaCoeff, ratFactor,
    ratLower, ratUpper, ratA, ratDr, ratD1, ratBeta, ratGap, ratM,
    ratF2, ratF3, ratF4, ratF5, ratF6, ratF7, ratF8, ratF9, ratF10,
    Fin.sum_univ_succ, Finset.sum_range_succ]

private theorem realRowSum_eq_cast :
    (∑ i : Fin 128,
      ∫ d in RowLower i..RowUpper i,
        RowFactor i *
          ((sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
            (RowLower i) (sectionSixFirstLowCentralSmallI5P1D807L d / 2)) ^ 2 / 2 +
            ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
                sectionSixFirstLowCentralSmallI5P1D807L d,
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (RowLower i) r *
                sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
                  (RowLower i) (sectionSixFirstLowCentralSmallI5P1D807L d - r))) =
      ((Finset.sum (Finset.range 128) ratRowTerm : Rat) : Real) := by
  calc
    (∑ i : Fin 128,
      ∫ d in RowLower i..RowUpper i,
        RowFactor i *
          ((sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
            (RowLower i) (sectionSixFirstLowCentralSmallI5P1D807L d / 2)) ^ 2 / 2 +
            ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
                sectionSixFirstLowCentralSmallI5P1D807L d,
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (RowLower i) r *
                sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
                  (RowLower i) (sectionSixFirstLowCentralSmallI5P1D807L d - r))) =
        ∑ i : Fin 128, (ratRowTerm i.1 : Real) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact rowIntegral_eq_cast i
    _ = ((∑ i : Fin 128, ratRowTerm i.1 : Rat) : Real) := by
      symm
      exact Rat.cast_sum (Finset.univ : Finset (Fin 128))
        (fun i : Fin 128 => ratRowTerm i.1)
    _ = ((Finset.sum (Finset.range 128) ratRowTerm : Rat) : Real) := by
      congr 1

theorem sectionSixFirstLowCentralSmallI5P1D883_p2AnchoredRowMajorant_sum_lt :
    (∑ i : Fin 128,
      (∫ d in
          (sectionSixFirstLowCentralSmallI5P1D807Dr +
            (i : Real) *
              (sectionSixFirstLowCentralSmallI5P1D807D1 -
                sectionSixFirstLowCentralSmallI5P1D807Dr) / 128)..
          (sectionSixFirstLowCentralSmallI5P1D807Dr +
            (((i : Nat) + 1 : Nat) : Real) *
              (sectionSixFirstLowCentralSmallI5P1D807D1 -
                sectionSixFirstLowCentralSmallI5P1D807Dr) / 128),
        sectionSixFirstLowCentralSmallI5P1D883P2AnchoredRowMajorant i d)) <
      (113 / 500000 : Real) := by
  change (∑ i : Fin 128,
      ∫ d in RowLower i..RowUpper i,
        RowFactor i *
          ((sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
            (RowLower i) (sectionSixFirstLowCentralSmallI5P1D807L d / 2)) ^ 2 / 2 +
            ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
                sectionSixFirstLowCentralSmallI5P1D807L d,
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (RowLower i) r *
                sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
                  (RowLower i) (sectionSixFirstLowCentralSmallI5P1D807L d - r))) < _
  rw [realRowSum_eq_cast]
  calc
    ((Finset.sum (Finset.range 128) ratRowTerm : Rat) : Real) <
        ((14111 / 62500000 : Rat) : Real) :=
      (Rat.cast_lt (K := Real)).mpr ratRowSum_lt
    _ < (113 / 500000 : Real) := by norm_num

end
end PrimesRestrictedDigits
