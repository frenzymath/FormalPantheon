import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0RowCompositionD875
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1D814P0RowPolynomial
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece0RowMajorantSumD876 -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
# exact Piece0 row-majorant sum

This module evaluates the 256 row-majorant interval integrals through an exact rational
degree-ten certificate. It exports only the relaxed arithmetic cap and makes no row-union,
set-integral, or full-I5 claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6.
-/

private def ratD0 : Rat := 16249 / 125000
private def ratDs : Rat := 29 / 200
private def ratBeta : Rat := 212499 / 500000
private def ratGap : Rat := 16249 / 250000
private def ratTailC : Rat := 564383 / 1000000
private def ratH0 : Rat := 107501 / 1000000

private def ratLower (i : Nat) : Rat :=
  ratD0 + (i : Rat) * (ratDs - ratD0) / 256

private def ratUpper (i : Nat) : Rat :=
  ratD0 + ((i + 1 : Nat) : Rat) * (ratDs - ratD0) / 256

private def ratFactor (i : Nat) : Rat :=
  ratTailC / (ratBeta - ratUpper i) *
    (1 / ratGap - 1 / (ratUpper i - ratGap))

private def ratAreaCoeff (a : Rat) : Fin 11 -> Rat := ![
  (-1 / 2 : Rat) ^ 0 * (
    (1 / 2 : Rat) * ratH0 ^ 2 / a ^ 2 +
    (-1 / 2 : Rat) * ratH0 ^ 3 / a ^ 3 +
    (11 / 24 : Rat) * ratH0 ^ 4 / a ^ 4 +
    (-5 / 12 : Rat) * ratH0 ^ 5 / a ^ 5 +
    (137 / 360 : Rat) * ratH0 ^ 6 / a ^ 6 +
    (-11 / 60 : Rat) * ratH0 ^ 7 / a ^ 7 +
    (47 / 480 : Rat) * ratH0 ^ 8 / a ^ 8 +
    (-1 / 20 : Rat) * ratH0 ^ 9 / a ^ 9 +
    (1 / 50 : Rat) * ratH0 ^ 10 / a ^ 10),
  (-1 / 2 : Rat) ^ 1 * (
    (1 / 2 : Rat) * 2 * ratH0 / a ^ 2 +
    (-1 / 2 : Rat) * 3 * ratH0 ^ 2 / a ^ 3 +
    (11 / 24 : Rat) * 4 * ratH0 ^ 3 / a ^ 4 +
    (-5 / 12 : Rat) * 5 * ratH0 ^ 4 / a ^ 5 +
    (137 / 360 : Rat) * 6 * ratH0 ^ 5 / a ^ 6 +
    (-11 / 60 : Rat) * 7 * ratH0 ^ 6 / a ^ 7 +
    (47 / 480 : Rat) * 8 * ratH0 ^ 7 / a ^ 8 +
    (-1 / 20 : Rat) * 9 * ratH0 ^ 8 / a ^ 9 +
    (1 / 50 : Rat) * 10 * ratH0 ^ 9 / a ^ 10),
  (-1 / 2 : Rat) ^ 2 * (
    (1 / 2 : Rat) / a ^ 2 +
    (-1 / 2 : Rat) * 3 * ratH0 / a ^ 3 +
    (11 / 24 : Rat) * 6 * ratH0 ^ 2 / a ^ 4 +
    (-5 / 12 : Rat) * 10 * ratH0 ^ 3 / a ^ 5 +
    (137 / 360 : Rat) * 15 * ratH0 ^ 4 / a ^ 6 +
    (-11 / 60 : Rat) * 21 * ratH0 ^ 5 / a ^ 7 +
    (47 / 480 : Rat) * 28 * ratH0 ^ 6 / a ^ 8 +
    (-1 / 20 : Rat) * 36 * ratH0 ^ 7 / a ^ 9 +
    (1 / 50 : Rat) * 45 * ratH0 ^ 8 / a ^ 10),
  (-1 / 2 : Rat) ^ 3 * (
    (-1 / 2 : Rat) / a ^ 3 +
    (11 / 24 : Rat) * 4 * ratH0 / a ^ 4 +
    (-5 / 12 : Rat) * 10 * ratH0 ^ 2 / a ^ 5 +
    (137 / 360 : Rat) * 20 * ratH0 ^ 3 / a ^ 6 +
    (-11 / 60 : Rat) * 35 * ratH0 ^ 4 / a ^ 7 +
    (47 / 480 : Rat) * 56 * ratH0 ^ 5 / a ^ 8 +
    (-1 / 20 : Rat) * 84 * ratH0 ^ 6 / a ^ 9 +
    (1 / 50 : Rat) * 120 * ratH0 ^ 7 / a ^ 10),
  (-1 / 2 : Rat) ^ 4 * (
    (11 / 24 : Rat) / a ^ 4 +
    (-5 / 12 : Rat) * 5 * ratH0 / a ^ 5 +
    (137 / 360 : Rat) * 15 * ratH0 ^ 2 / a ^ 6 +
    (-11 / 60 : Rat) * 35 * ratH0 ^ 3 / a ^ 7 +
    (47 / 480 : Rat) * 70 * ratH0 ^ 4 / a ^ 8 +
    (-1 / 20 : Rat) * 126 * ratH0 ^ 5 / a ^ 9 +
    (1 / 50 : Rat) * 210 * ratH0 ^ 6 / a ^ 10),
  (-1 / 2 : Rat) ^ 5 * (
    (-5 / 12 : Rat) / a ^ 5 +
    (137 / 360 : Rat) * 6 * ratH0 / a ^ 6 +
    (-11 / 60 : Rat) * 21 * ratH0 ^ 2 / a ^ 7 +
    (47 / 480 : Rat) * 56 * ratH0 ^ 3 / a ^ 8 +
    (-1 / 20 : Rat) * 126 * ratH0 ^ 4 / a ^ 9 +
    (1 / 50 : Rat) * 252 * ratH0 ^ 5 / a ^ 10),
  (-1 / 2 : Rat) ^ 6 * (
    (137 / 360 : Rat) / a ^ 6 +
    (-11 / 60 : Rat) * 7 * ratH0 / a ^ 7 +
    (47 / 480 : Rat) * 28 * ratH0 ^ 2 / a ^ 8 +
    (-1 / 20 : Rat) * 84 * ratH0 ^ 3 / a ^ 9 +
    (1 / 50 : Rat) * 210 * ratH0 ^ 4 / a ^ 10),
  (-1 / 2 : Rat) ^ 7 * (
    (-11 / 60 : Rat) / a ^ 7 +
    (47 / 480 : Rat) * 8 * ratH0 / a ^ 8 +
    (-1 / 20 : Rat) * 36 * ratH0 ^ 2 / a ^ 9 +
    (1 / 50 : Rat) * 120 * ratH0 ^ 3 / a ^ 10),
  (-1 / 2 : Rat) ^ 8 * (
    (47 / 480 : Rat) / a ^ 8 +
    (-1 / 20 : Rat) * 9 * ratH0 / a ^ 9 +
    (1 / 50 : Rat) * 45 * ratH0 ^ 2 / a ^ 10),
  (-1 / 2 : Rat) ^ 9 * (
    (-1 / 20 : Rat) / a ^ 9 +
    (1 / 50 : Rat) * 10 * ratH0 / a ^ 10),
  (-1 / 2 : Rat) ^ 10 * ((1 / 50 : Rat) / a ^ 10)
]

private def ratAreaIntegral (i : Nat) : Rat :=
  ∑ n : Fin 11,
    ratAreaCoeff (ratLower i) n *
      (ratUpper i ^ ((n : Nat) + 1) - ratLower i ^ ((n : Nat) + 1)) /
        ((n : Nat) + 1 : Nat)

private def ratRowTerm (i : Nat) : Rat :=
  ratFactor i * ratAreaIntegral i

private def realAreaPoly (a : Rat) (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D814FinPoly
    (fun n : Fin 11 => (ratAreaCoeff a n : Real)) d

private theorem h_eq_cast_sub (d : Real) :
    sectionSixFirstLowCentralSmallI5P1D807H d = (ratH0 : Real) - d / 2 := by
  have hBeta := sectionSixFirstLowCentralSmallI5P1D807_constants.2.1
  unfold sectionSixFirstLowCentralSmallI5P1D807H
  rw [hBeta]
  norm_num [sectionSixFirstLowCentralSmallI5P1D807Square, ratH0]
  ring

private theorem area_eq_realAreaPoly (a : Rat) (ha : a ≠ 0) (d : Real) :
    sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
          (a : Real) (sectionSixFirstLowCentralSmallI5P1D807H d) ^ 2 / 2 =
      realAreaPoly a d := by
  have haR : (a : Real) ≠ 0 := by exact_mod_cast ha
  rw [h_eq_cast_sub]
  unfold sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
    realAreaPoly sectionSixFirstLowCentralSmallI5P1D814FinPoly
  simp [ratAreaCoeff, Fin.sum_univ_succ]
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

private abbrev RowLower (i : Fin 256) : Real :=
  sectionSixFirstLowCentralSmallI5P1D871P0RowLower i

private abbrev RowUpper (i : Fin 256) : Real :=
  sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i

private abbrev RowFactor (i : Fin 256) : Real :=
  sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i

private abbrev RowMajorant (i : Fin 256) (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D875P0RowMajorant i d

private theorem rowLower_eq_cast (i : Fin 256) :
    RowLower i = (ratLower i.1 : Real) := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, hD0, hDs, _, _⟩
  simp only [RowLower, ratLower, ratD0, ratDs,
    sectionSixFirstLowCentralSmallI5P1D871P0RowLower]
  rw [hD0, hDs]
  norm_num

private theorem rowUpper_eq_cast (i : Fin 256) :
    RowUpper i = (ratUpper i.1 : Real) := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, hD0, hDs, _, _⟩
  simp only [RowUpper, ratUpper, ratD0, ratDs,
    sectionSixFirstLowCentralSmallI5P1D871P0RowUpper]
  rw [hD0, hDs]
  norm_num

private theorem ratLower_ne_zero (i : Fin 256) : ratLower i.1 ≠ 0 := by
  have hi : (0 : Rat) <= i.1 := by positivity
  unfold ratLower ratD0 ratDs
  norm_num
  positivity

private theorem rowFactor_denominators_pos (i : Fin 256) :
    0 < sectionSixFirstLowCentralSmallI5P1D807Beta - RowUpper i ∧
      0 < sectionSixFirstLowCentralSmallI5P1D807Gap ∧
      0 < RowUpper i - sectionSixFirstLowCentralSmallI5P1D807Gap := by
  have ho := sectionSixFirstLowCentralSmallI5P1D871_p0Row_endpoint_order i
  have hD0Upper : sectionSixFirstLowCentralSmallI5P1D807D0 <= RowUpper i :=
    ho.1.trans ho.2.1
  have hUpperDs : RowUpper i <= sectionSixFirstLowCentralSmallI5P1D807Ds :=
    ho.2.2
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, hBeta, hGap, hD0, hDs, _, _⟩
  rw [hD0] at hD0Upper
  rw [hDs] at hUpperDs
  constructor
  · rw [hBeta]
    norm_num at hUpperDs ⊢
    linarith
  · constructor
    · rw [hGap]
      norm_num
    · rw [hGap]
      norm_num at hD0Upper ⊢
      linarith

private theorem rowFactor_eq_cast (i : Fin 256) :
    RowFactor i = (ratFactor i.1 : Real) := by
  rcases rowFactor_denominators_pos i with
    ⟨hBetaPos, hGapPos, hUpperGapPos⟩
  have hProductNe :
      (sectionSixFirstLowCentralSmallI5P1D807Beta - RowUpper i) *
          sectionSixFirstLowCentralSmallI5P1D807Gap *
          (RowUpper i - sectionSixFirstLowCentralSmallI5P1D807Gap) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt hBetaPos) (ne_of_gt hGapPos))
      (ne_of_gt hUpperGapPos)
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, hBeta, hGap, _, _, _, _⟩
  change sectionSixFirstLowCentralSmallI5P1D816Row0TailC /
      (sectionSixFirstLowCentralSmallI5P1D807Beta -
        sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i) *
      (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
        1 / (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i -
          sectionSixFirstLowCentralSmallI5P1D807Gap)) =
    (ratFactor i.1 : Real)
  apply mul_left_cancel₀ hProductNe
  rw [show sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i =
    (ratUpper i.1 : Real) by exact rowUpper_eq_cast i]
  rw [hBeta, hGap]
  norm_num [ratFactor, ratTailC, ratBeta, ratGap,
    sectionSixFirstLowCentralSmallI5P1D816Row0TailC]

private theorem rowMajorantIntegral_eq_cast (i : Fin 256) :
    (∫ d in RowLower i..RowUpper i, RowMajorant i d) =
      (ratRowTerm i.1 : Real) := by
  rw [rowLower_eq_cast, rowUpper_eq_cast]
  change (∫ d in (ratLower i.1 : Real)..(ratUpper i.1 : Real),
      RowFactor i *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
          (sectionSixFirstLowCentralSmallI5P1D807H d) ^ 2 / 2) =
    (ratRowTerm i.1 : Real)
  rw [show sectionSixFirstLowCentralSmallI5P1D871P0RowLower i =
    (ratLower i.1 : Real) by exact rowLower_eq_cast i]
  rw [show (fun d : Real => RowFactor i *
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
        (ratLower i.1 : Real) (sectionSixFirstLowCentralSmallI5P1D807H d) ^ 2 / 2) =
      (fun d : Real => RowFactor i *
        (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
          (ratLower i.1 : Real) (sectionSixFirstLowCentralSmallI5P1D807H d) ^ 2 / 2)) by
        funext d
        ring]
  rw [intervalIntegral.integral_const_mul, rowFactor_eq_cast]
  rw [intervalIntegral.integral_congr (fun d hd =>
    area_eq_realAreaPoly (ratLower i.1) (ratLower_ne_zero i) d)]
  rw [realAreaPoly_integral_eq_cast]
  unfold ratRowTerm ratAreaIntegral
  norm_num

private theorem ratRowSum_lt :
    (Finset.sum (Finset.range 256) ratRowTerm) <
      (1313 / 1000000 : Rat) := by
  norm_num [ratRowTerm, ratAreaIntegral, ratAreaCoeff, ratFactor,
    ratLower, ratUpper, ratD0, ratDs, ratBeta, ratGap, ratTailC, ratH0,
    Fin.sum_univ_succ, Finset.sum_range_succ]

private theorem realRowSum_eq_cast :
    (∑ i : Fin 256,
      ∫ d in RowLower i..RowUpper i, RowMajorant i d) =
      ((Finset.sum (Finset.range 256) ratRowTerm : Rat) : Real) := by
  calc
    (∑ i : Fin 256,
      ∫ d in RowLower i..RowUpper i, RowMajorant i d) =
        ∑ i : Fin 256, (ratRowTerm i.1 : Real) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact rowMajorantIntegral_eq_cast i
    _ = ((∑ i : Fin 256, ratRowTerm i.1 : Rat) : Real) := by
      symm
      exact Rat.cast_sum (Finset.univ : Finset (Fin 256))
        (fun i : Fin 256 => ratRowTerm i.1)
    _ = ((Finset.sum (Finset.range 256) ratRowTerm : Rat) : Real) := by
      congr 1

theorem sectionSixFirstLowCentralSmallI5P1D876_p0RowMajorant_sum_lt :
    (∑ i : Fin 256,
      ∫ d in
        sectionSixFirstLowCentralSmallI5P1D871P0RowLower i..
        sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i,
        sectionSixFirstLowCentralSmallI5P1D875P0RowMajorant i d) <
      (1313 / 1000000 : Real) := by
  rw [realRowSum_eq_cast]
  calc
    ((Finset.sum (Finset.range 256) ratRowTerm : Rat) : Real) <
        ((1313 / 1000000 : Rat) : Real) :=
      (Rat.cast_lt (K := Real)).mpr ratRowSum_lt
    _ = (1313 / 1000000 : Real) := by norm_num

end

end PrimesRestrictedDigits
