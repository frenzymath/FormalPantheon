import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatterns
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5BranchPartition
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabInverseFiberIntegral
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# P0 fibers for the low-central-small I5 carrier

This file records the fixed-delta all-low pair fiber and its three weak Buchstab branch cells.
The cells are closed overcovers; the only analytic claim is the symbolic inverse-cell identity
supplied by the generic weak-endpoint API.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P0Fiber (u v w : Real) : Set Real :=
  {t | (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real) ∧
    (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallI5PairPattern 0}

/-- The three raw lower endpoints are inverse, middle, and tail order. -/
def sectionSixFirstLowCentralSmallI5P0RawLower
    (u v w : Real) : Fin 3 → Real :=
  ![(1 - u - v - w) / 3,
    (1 - u - v - w) / 4,
    sectionSixThetaGap (1 / 1000000 : Real)]

/-- The three raw upper endpoints are inverse, middle, and tail order. -/
def sectionSixFirstLowCentralSmallI5P0RawUpper
    (u v w : Real) : Fin 3 → Real :=
  ![(1 - u - v - w) / 2,
    (1 - u - v - w) / 3,
    (1 - u - v - w) / 4]

def sectionSixFirstLowCentralSmallI5P0CellLower
    (u v w : Real) (b : Fin 3) : Real :=
  max (sectionSixThetaGap (1 / 1000000 : Real))
    (sectionSixFirstLowCentralSmallI5P0RawLower u v w b)

def sectionSixFirstLowCentralSmallI5P0CellUpper
    (u v w : Real) (b : Fin 3) : Real :=
  min (min w (sectionSixThetaOne (1 / 1000000 : Real) - u))
    (sectionSixFirstLowCentralSmallI5P0RawUpper u v w b)

def sectionSixFirstLowCentralSmallI5P0Cell
    (u v w : Real) (b : Fin 3) : Set Real :=
  Icc (sectionSixFirstLowCentralSmallI5P0CellLower u v w b)
    (sectionSixFirstLowCentralSmallI5P0CellUpper u v w b)

private theorem sectionSixFirstLowCentralSmallI5P0_gap_pos :
    0 < sectionSixThetaGap (1 / 1000000 : Real) := by
  norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]

private theorem sectionSixFirstLowCentralSmallI5P0_pattern_low
    {u v w t : Real}
    (hp : (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallI5PairPattern 0) :
    u + w < sectionSixThetaOne (1 / 1000000 : Real) := by
  change u + w < sectionSixThetaOne (1 / 1000000 : Real) ∧
      u + t < sectionSixThetaOne (1 / 1000000 : Real) ∧
      v + w < sectionSixThetaOne (1 / 1000000 : Real) ∧
      v + t < sectionSixThetaOne (1 / 1000000 : Real) ∧
      w + t < sectionSixThetaOne (1 / 1000000 : Real) at hp
  exact hp.1

theorem sectionSixFirstLowCentralSmallI5P0Fiber_mem_branchCell
    {u v w t : Real}
    (ht : t ∈ sectionSixFirstLowCentralSmallI5P0Fiber u v w) :
    ∃ b : Fin 3,
      t ∈ sectionSixFirstLowCentralSmallI5P0Cell u v w b := by
  change (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real) ∧
    (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallI5PairPattern 0 at ht
  rcases ht with ⟨houter, hpattern⟩
  have hgap := sectionSixFirstLowCentralSmallI5P0_gap_pos
  have hpart := sectionSixFirstLowCentralSmallUniformOuter_branch_partition
    hgap houter
  have hyOne := sectionSixFirstLowCentralSmallUniformOuter_argument_ge_one
    hgap houter
  have htu : t <= sectionSixThetaOne (1 / 1000000 : Real) - u := by
    have hlow := sectionSixFirstLowCentralSmallI5P0_pattern_low hpattern
    linarith [houter.2.1]
  have hlowGap : sectionSixThetaGap (1 / 1000000 : Real) <= t :=
    (houter.1).le
  have hupperBase : t <= w := houter.2.1
  let B : Real := 1 - u - v - w
  have hlowBase : sectionSixFirstLowCentralSmallI5P0RawLower u v w =
      ![B / 3, B / 4, sectionSixThetaGap (1 / 1000000 : Real)] := by
    funext i
    fin_cases i <;> simp [sectionSixFirstLowCentralSmallI5P0RawLower, B]
  have hupperBaseVec : sectionSixFirstLowCentralSmallI5P0RawUpper u v w =
      ![B / 2, B / 3, B / 4] := by
    funext i
    fin_cases i <;> simp [sectionSixFirstLowCentralSmallI5P0RawUpper, B]
  have hy :
      (1 - u - v - w - t) / t = (B - t) / t := by
    rfl
  by_cases hyTwo : (1 - u - v - w - t) / t <= 2
  · have hinv := (hpart.2.2).mp ⟨hyOne, hyTwo⟩
    refine ⟨0, ?_⟩
    apply mem_Icc.mpr
    constructor
    · unfold sectionSixFirstLowCentralSmallI5P0CellLower
      apply max_le hlowGap
      change B / 3 <= t
      linarith [hinv.1]
    · unfold sectionSixFirstLowCentralSmallI5P0CellUpper
      apply le_min
      · exact le_min hupperBase htu
      · change t <= B / 2
        linarith [hinv.2]
  · have hyTwo' : 2 <=
        (1 - u - v - w - t) / t := le_of_not_ge hyTwo
    by_cases hyThree : (1 - u - v - w - t) / t <= 3
    · have hmiddle := (hpart.2.1).mp ⟨hyTwo', hyThree⟩
      refine ⟨1, ?_⟩
      apply mem_Icc.mpr
      constructor
      · unfold sectionSixFirstLowCentralSmallI5P0CellLower
        apply max_le hlowGap
        change B / 4 <= t
        linarith [hmiddle.2]
      · unfold sectionSixFirstLowCentralSmallI5P0CellUpper
        apply le_min
        · exact le_min hupperBase htu
        · change t <= B / 3
          linarith [hmiddle.1]
    · have hyThree' : 3 <=
          (1 - u - v - w - t) / t := le_of_not_ge hyThree
      have htail := hpart.1.mp hyThree'
      refine ⟨2, ?_⟩
      apply mem_Icc.mpr
      constructor
      · unfold sectionSixFirstLowCentralSmallI5P0CellLower
        apply max_le hlowGap
        change sectionSixThetaGap (1 / 1000000 : Real) <= t
        exact hlowGap
      · unfold sectionSixFirstLowCentralSmallI5P0CellUpper
        apply le_min
        · exact le_min hupperBase htu
        · change t <= B / 4
          linarith [htail]

theorem sectionSixFirstLowCentralSmallI5P0InverseCell_integral_eq
    {u v w : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hLU :
      sectionSixFirstLowCentralSmallI5P0CellLower u v w 0 <=
        sectionSixFirstLowCentralSmallI5P0CellUpper u v w 0) :
    (∫ t in
        sectionSixFirstLowCentralSmallI5P0CellLower u v w 0..
        sectionSixFirstLowCentralSmallI5P0CellUpper u v w 0,
      buchstabFunction ((1 - u - v - w - t) / t) /
        (u * v * w * t ^ 2)) =
      1 / (u * v * w * (1 - u - v - w)) *
        Real.log
          (sectionSixFirstLowCentralSmallI5P0CellUpper u v w 0 *
              (1 - u - v - w -
                sectionSixFirstLowCentralSmallI5P0CellLower u v w 0) /
            (sectionSixFirstLowCentralSmallI5P0CellLower u v w 0 *
              (1 - u - v - w -
                sectionSixFirstLowCentralSmallI5P0CellUpper u v w 0))) := by
  have hgap := sectionSixFirstLowCentralSmallI5P0_gap_pos
  have hl : 0 <
      sectionSixFirstLowCentralSmallI5P0CellLower u v w 0 := by
    unfold sectionSixFirstLowCentralSmallI5P0CellLower
    exact lt_of_lt_of_le hgap (le_max_left _ _)
  have hAOne : 2 *
      sectionSixFirstLowCentralSmallI5P0CellUpper u v w 0 <=
        1 - u - v - w := by
    have hraw :
        sectionSixFirstLowCentralSmallI5P0CellUpper u v w 0 <=
          sectionSixFirstLowCentralSmallI5P0RawUpper u v w 0 := by
      unfold sectionSixFirstLowCentralSmallI5P0CellUpper
      exact min_le_right _ _
    have hraw' : sectionSixFirstLowCentralSmallI5P0RawUpper u v w 0 <=
        (1 - u - v - w) / 2 := by
      change (1 - u - v - w) / 2 <=
        (1 - u - v - w) / 2
      exact le_rfl
    have hupper := hraw.trans hraw'
    linarith [hupper]
  have hATwo : 1 - u - v - w <= 3 *
      sectionSixFirstLowCentralSmallI5P0CellLower u v w 0 := by
    have hraw := le_max_right
      (sectionSixThetaGap (1 / 1000000 : Real))
      (sectionSixFirstLowCentralSmallI5P0RawLower u v w 0)
    have hraw' : (1 - u - v - w) / 3 <=
        sectionSixFirstLowCentralSmallI5P0CellLower u v w 0 := by
      have hraw0 : (1 - u - v - w) / 3 <=
          sectionSixFirstLowCentralSmallI5P0RawLower u v w 0 := by
        change (1 - u - v - w) / 3 <=
          (1 - u - v - w) / 3
        exact le_rfl
      exact hraw0.trans hraw
    linarith [hraw']
  exact integral_sectionSixBuchstabInverseBranch_eq
    hu hv hw hl hLU hAOne hATwo

end

end PrimesRestrictedDigits
