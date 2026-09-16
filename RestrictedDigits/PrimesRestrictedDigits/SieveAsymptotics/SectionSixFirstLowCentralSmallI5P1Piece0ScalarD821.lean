import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0AnalyticD816
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1D814P0RowPolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece0ScalarD821 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-! Scalar inequalities for the transformed P1 Piece0 region. -/

abbrev sectionSixFirstLowCentralSmallI5P1D821A : Real := 16249 / 125000
abbrev sectionSixFirstLowCentralSmallI5P1D821B : Real := 29 / 200
abbrev sectionSixFirstLowCentralSmallI5P1D821Beta : Real := 212499 / 500000
abbrev sectionSixFirstLowCentralSmallI5P1D821Gap : Real := 16249 / 250000
abbrev sectionSixFirstLowCentralSmallI5P1D821C : Real := 16 / 25
abbrev sectionSixFirstLowCentralSmallI5P1D821TailC : Real := 564383 / 1000000

def sectionSixFirstLowCentralSmallI5P1D821H (d : Real) : Real :=
  (sectionSixFirstLowCentralSmallI5P1D821C -
      sectionSixFirstLowCentralSmallI5P1D821Beta - d) / 2

def sectionSixFirstLowCentralSmallI5P1D821Majorant
    (_d r s : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D821TailC *
      ((1 / (sectionSixFirstLowCentralSmallI5P1D821Beta -
        sectionSixFirstLowCentralSmallI5P1D821B)) *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4
          sectionSixFirstLowCentralSmallI5P1D821A r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4
          sectionSixFirstLowCentralSmallI5P1D821A s) *
      (1 / sectionSixFirstLowCentralSmallI5P1D821Gap -
        1 / (sectionSixFirstLowCentralSmallI5P1D821B -
          sectionSixFirstLowCentralSmallI5P1D821Gap))

def sectionSixFirstLowCentralSmallI5P1D821RMajorant (d : Real) : Real :=
  ∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D821H d,
    ∫ s in (0 : Real)..r,
      sectionSixFirstLowCentralSmallI5P1D821Majorant d r s

def sectionSixFirstLowCentralSmallI5P1D821CrossPoly (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D814P0Row0CrossPoly d

theorem sectionSixFirstLowCentralSmallI5P1D821_crossPoly_integral :
    (∫ d in sectionSixFirstLowCentralSmallI5P1D821A..
        sectionSixFirstLowCentralSmallI5P1D821B,
      sectionSixFirstLowCentralSmallI5P1D821CrossPoly d) =
      (327447056022046909775566217058747222137490434815982912909 /
        639355980702064931048382255296227661982235859563315200000000 : Real) := by
  change (∫ d in sectionSixFirstLowCentralSmallI5P1D821A..
    sectionSixFirstLowCentralSmallI5P1D821B,
    sectionSixFirstLowCentralSmallI5P1D814FinPoly
      sectionSixFirstLowCentralSmallI5P1D814P0Row0Coeff d) = _
  rw [sectionSixFirstLowCentralSmallI5P1D814_intervalIntegral_finPoly]
  norm_num [sectionSixFirstLowCentralSmallI5P1D821A,
    sectionSixFirstLowCentralSmallI5P1D821B,
    sectionSixFirstLowCentralSmallI5P1D814P0Row0Coeff,
    Fin.sum_univ_succ]

theorem sectionSixFirstLowCentralSmallI5P1D821_scalar_lt_three_thousandths :
    sectionSixFirstLowCentralSmallI5P1D821TailC /
        (sectionSixFirstLowCentralSmallI5P1D821Beta -
          sectionSixFirstLowCentralSmallI5P1D821B) *
        (1 / sectionSixFirstLowCentralSmallI5P1D821Gap -
          1 / (sectionSixFirstLowCentralSmallI5P1D821B -
            sectionSixFirstLowCentralSmallI5P1D821Gap)) *
        (∫ d in sectionSixFirstLowCentralSmallI5P1D821A..
          sectionSixFirstLowCentralSmallI5P1D821B,
          sectionSixFirstLowCentralSmallI5P1D821CrossPoly d) <
      (3 / 1000 : Real) := by
  rw [sectionSixFirstLowCentralSmallI5P1D821_crossPoly_integral]
  norm_num [sectionSixFirstLowCentralSmallI5P1D821A,
    sectionSixFirstLowCentralSmallI5P1D821B,
    sectionSixFirstLowCentralSmallI5P1D821Beta,
    sectionSixFirstLowCentralSmallI5P1D821Gap,
    sectionSixFirstLowCentralSmallI5P1D821TailC]

theorem sectionSixFirstLowCentralSmallI5P1D821_triangle (d : Real) :
    sectionSixFirstLowCentralSmallI5P1D821RMajorant d =
      sectionSixFirstLowCentralSmallI5P1D821TailC /
          (sectionSixFirstLowCentralSmallI5P1D821Beta -
            sectionSixFirstLowCentralSmallI5P1D821B) *
          (1 / sectionSixFirstLowCentralSmallI5P1D821Gap -
            1 / (sectionSixFirstLowCentralSmallI5P1D821B -
              sectionSixFirstLowCentralSmallI5P1D821Gap)) *
          sectionSixFirstLowCentralSmallI5P1D821CrossPoly d := by
  have ha : sectionSixFirstLowCentralSmallI5P1D821A ≠ 0 := by
    norm_num [sectionSixFirstLowCentralSmallI5P1D821A]
  have htri := sectionSixFirstLowCentralSmallI5P1D816_triangular_q4
    (a := sectionSixFirstLowCentralSmallI5P1D821A)
    (H := sectionSixFirstLowCentralSmallI5P1D821H d) ha
  have hH : sectionSixFirstLowCentralSmallI5P1D821H d =
      sectionSixFirstLowCentralSmallI5P1D814P0Row0R d := by
    unfold sectionSixFirstLowCentralSmallI5P1D821H
      sectionSixFirstLowCentralSmallI5P1D814P0Row0R
    norm_num [sectionSixFirstLowCentralSmallI5P1D821C,
      sectionSixFirstLowCentralSmallI5P1D821Beta]
  have hcross := sectionSixFirstLowCentralSmallI5P1D814_p0CrossPoly_eq d
  simp only [sectionSixFirstLowCentralSmallI5P1D821RMajorant]
  change
    (∫ r in 0..sectionSixFirstLowCentralSmallI5P1D821H d,
      ∫ s in 0..r,
        sectionSixFirstLowCentralSmallI5P1D821TailC *
          ((1 / (sectionSixFirstLowCentralSmallI5P1D821Beta -
            sectionSixFirstLowCentralSmallI5P1D821B)) *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4
              sectionSixFirstLowCentralSmallI5P1D821A r *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4
              sectionSixFirstLowCentralSmallI5P1D821A s) *
          (1 / sectionSixFirstLowCentralSmallI5P1D821Gap -
            1 / (sectionSixFirstLowCentralSmallI5P1D821B -
              sectionSixFirstLowCentralSmallI5P1D821Gap))) = _
  have hinner (r : Real) :
      (∫ s in 0..r,
        sectionSixFirstLowCentralSmallI5P1D821TailC *
          ((1 / (sectionSixFirstLowCentralSmallI5P1D821Beta -
            sectionSixFirstLowCentralSmallI5P1D821B)) *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4
              sectionSixFirstLowCentralSmallI5P1D821A r *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4
              sectionSixFirstLowCentralSmallI5P1D821A s) *
          (1 / sectionSixFirstLowCentralSmallI5P1D821Gap -
            1 / (sectionSixFirstLowCentralSmallI5P1D821B -
              sectionSixFirstLowCentralSmallI5P1D821Gap))) =
        (sectionSixFirstLowCentralSmallI5P1D821TailC *
          (1 / (sectionSixFirstLowCentralSmallI5P1D821Beta -
            sectionSixFirstLowCentralSmallI5P1D821B)) *
          (1 / sectionSixFirstLowCentralSmallI5P1D821Gap -
            1 / (sectionSixFirstLowCentralSmallI5P1D821B -
              sectionSixFirstLowCentralSmallI5P1D821Gap)) *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4
            sectionSixFirstLowCentralSmallI5P1D821A r) *
          (∫ s in 0..r,
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4
              sectionSixFirstLowCentralSmallI5P1D821A s) := by
    calc
      (∫ s in 0..r,
          sectionSixFirstLowCentralSmallI5P1D821TailC *
            ((1 / (sectionSixFirstLowCentralSmallI5P1D821Beta -
              sectionSixFirstLowCentralSmallI5P1D821B)) *
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4
                sectionSixFirstLowCentralSmallI5P1D821A r *
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4
                sectionSixFirstLowCentralSmallI5P1D821A s) *
            (1 / sectionSixFirstLowCentralSmallI5P1D821Gap -
              1 / (sectionSixFirstLowCentralSmallI5P1D821B -
                sectionSixFirstLowCentralSmallI5P1D821Gap))) =
          ∫ s in 0..r,
            (sectionSixFirstLowCentralSmallI5P1D821TailC *
              (1 / (sectionSixFirstLowCentralSmallI5P1D821Beta -
                sectionSixFirstLowCentralSmallI5P1D821B)) *
              (1 / sectionSixFirstLowCentralSmallI5P1D821Gap -
                1 / (sectionSixFirstLowCentralSmallI5P1D821B -
                  sectionSixFirstLowCentralSmallI5P1D821Gap)) *
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4
                sectionSixFirstLowCentralSmallI5P1D821A r) *
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4
                sectionSixFirstLowCentralSmallI5P1D821A s := by
        apply intervalIntegral.integral_congr
        intro s hs
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr (fun r hr => hinner r)]
  ring_nf
  rw [intervalIntegral.integral_mul_const]
  rw [htri]
  rw [hH]
  have hprim :
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
          sectionSixFirstLowCentralSmallI5P1D821A
          (sectionSixFirstLowCentralSmallI5P1D814P0Row0R d) ^ 2 / 2 =
        sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
          sectionSixFirstLowCentralSmallI5P1D814P0Row0A
          (sectionSixFirstLowCentralSmallI5P1D814P0Row0R d) ^ 2 / 2 := by
    simp only [sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
      sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
    norm_num [sectionSixFirstLowCentralSmallI5P1D821A,
      sectionSixFirstLowCentralSmallI5P1D814P0Row0A]
  rw [hprim, ← hcross]
  rfl


end
end PrimesRestrictedDigits
