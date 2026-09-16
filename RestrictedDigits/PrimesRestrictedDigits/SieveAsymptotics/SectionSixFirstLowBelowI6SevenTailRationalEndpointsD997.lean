import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6SevenTailFiberGeometryD996
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0RationalNestedReplay
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact rational endpoint bounds for the seven I6 tail targets

The five selected affine bands retain zero/one sentinels and reflected last band. Rational
extrema bound the endpoints on an arbitrary leaf box; positivity of the upper ceiling requires
an actual ordered point.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace PrimesRestrictedDigits

def i6D997TailRootBox : RationalBox 3 where
  lower := fun _ => 16249 / 250000
  upper := fun _ => 180001 / 500000

def i6D997TailBandLowerAffine : Fin 5 -> RationalAffine 3 := ![
  ⟨180001 / 500000, ![-1, -1, 0]⟩,
  ⟨180001 / 500000, ![-1, 0, -1]⟩,
  ⟨180001 / 500000, ![0, -1, -1]⟩,
  ⟨180001 / 500000, ![-1, -1, -1]⟩,
  ⟨287501 / 500000, ![-1, -1, -1]⟩
]

def i6D997TailBandUpperAffine : Fin 5 -> RationalAffine 3 := ![
  ⟨212499 / 500000, ![-1, -1, 0]⟩,
  ⟨212499 / 500000, ![-1, 0, -1]⟩,
  ⟨212499 / 500000, ![0, -1, -1]⟩,
  ⟨212499 / 500000, ![-1, -1, -1]⟩,
  ⟨319999 / 500000, ![-1, -1, -1]⟩
]

def i6D997TailBranchUpperAffine : RationalAffine 3 :=
  ⟨1 / 4, ![-1 / 4, -1 / 4, -1 / 4]⟩

def i6D997TailLowerFloor (sigma : Fin 5 -> Bool) (box : RationalBox 3) : Rat :=
  let high : Fin 5 -> Rat := fun i =>
    if sigma i = true then (i6D997TailBandUpperAffine i).minOn box else 0
  max (16249 / 250000)
    (max 0 (max (high 0) (max (high 1) (max (high 2) (max (high 3) (high 4))))))

def i6D997TailUpperCeiling (sigma : Fin 5 -> Bool) (box : RationalBox 3) : Rat :=
  let low : Fin 5 -> Rat := fun i =>
    if sigma i = true then 1 else (i6D997TailBandLowerAffine i).maxOn box
  min (box.upper 2) (min (i6D997TailBranchUpperAffine.maxOn box)
    (min 1 (min (low 0) (min (low 1) (min (low 2) (min (low 3) (low 4)))))))

theorem i6D997TailRootBox_spec :
    i6D997TailRootBox.IsOrdered ∧
      sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3
        i6D997TailRootBox = i6D996TailRootBase := by
  constructor
  · intro i
    norm_num [i6D997TailRootBox]
  · ext z
    rcases z with ⟨⟨u, v⟩, w⟩
    norm_num [sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3,
      i6D997TailRootBox, i6D996TailRootBase, sectionSixThetaGap,
      sectionSixThetaOne, sectionSixThetaTwo]

theorem i6D997TailBandAffines_eval (i : Fin 5) (z : ((Real × Real) × Real)) :
    (i6D997TailBandLowerAffine i).evalReal
        (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z) =
      sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 i ∧
    (i6D997TailBandUpperAffine i).evalReal
        (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z) =
      sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 i := by
  fin_cases i <;> constructor <;>
    norm_num [i6D997TailBandLowerAffine, i6D997TailBandUpperAffine,
      RationalAffine.evalReal, Fin.sum_univ_succ,
      sectionSixFirstLowCentralSmallI5P0RationalCoordinates3,
      sectionSixFirstLowBelowI6BandLower, sectionSixFirstLowBelowI6BandUpper,
      sectionSixThetaOne, sectionSixThetaTwo, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

theorem i6D997TailBranchUpperAffine_eval (z : ((Real × Real) × Real)) :
    i6D997TailBranchUpperAffine.evalReal
        (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z) =
      (1 - z.1.1 - z.1.2 - z.2) / 4 := by
  norm_num [i6D997TailBranchUpperAffine, RationalAffine.evalReal,
    Fin.sum_univ_succ, sectionSixFirstLowCentralSmallI5P0RationalCoordinates3]
  ring

theorem i6D997TailLowerFloor_pos (sigma : Fin 5 -> Bool) (box : RationalBox 3) :
    0 < i6D997TailLowerFloor sigma box := by
  unfold i6D997TailLowerFloor
  exact (show (0 : Rat) < 16249 / 250000 by norm_num).trans_le (le_max_left _ _)

theorem i6D997TailEndpointBounds_on_box
    (label : i6D996TailLabel) (box : RationalBox 3)
    {z : ((Real × Real) × Real)}
    (hzOrdered : z ∈ i6D996TailOrderedBase label)
    (hzBox : sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z ∈ box.region) :
    (i6D997TailLowerFloor label.1.2.2 box : Real) <=
        i6D996TailLower label.1.2.2 z ∧
      i6D996TailUpper label.1.2.2 z <=
        (i6D997TailUpperCeiling label.1.2.2 box : Real) ∧
      0 < (i6D997TailUpperCeiling label.1.2.2 box : Real) := by
  let high : Fin 5 -> Rat := fun i => if label.1.2.2 i = true then
    (i6D997TailBandUpperAffine i).minOn box else 0
  let low : Fin 5 -> Rat := fun i => if label.1.2.2 i = true then
    1 else (i6D997TailBandLowerAffine i).maxOn box
  let highReal : Fin 5 -> Real := fun i => if label.1.2.2 i = true then
    sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 i else 0
  let lowReal : Fin 5 -> Real := fun i => if label.1.2.2 i = true then
    1 else sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 i
  have hhigh : ∀ i, (high i : Real) <= highReal i := by
    intro i
    by_cases hi : label.1.2.2 i = true
    · simpa only [high, highReal, hi, ite_true, (i6D997TailBandAffines_eval i z).2]
        using ((i6D997TailBandUpperAffine i).eval_mem_interval box hzBox).1
    · simp [high, highReal, hi]
  have hlow : ∀ i, lowReal i <= (low i : Real) := by
    intro i
    by_cases hi : label.1.2.2 i = true
    · simp [low, lowReal, hi]
    · simpa [low, lowReal, hi, (i6D997TailBandAffines_eval i z).1]
        using ((i6D997TailBandLowerAffine i).eval_mem_interval box hzBox).2
  have hLower : (i6D997TailLowerFloor label.1.2.2 box : Real) <=
      i6D996TailLower label.1.2.2 z := by
    calc
      (i6D997TailLowerFloor label.1.2.2 box : Real) =
          max ((16249 / 250000 : Rat) : Real)
            (max 0 (max (high 0 : Real) (max (high 1 : Real)
              (max (high 2 : Real) (max (high 3 : Real) (high 4 : Real)))))) := by
        simp [i6D997TailLowerFloor, high]
      _ <= max ((16249 / 250000 : Rat) : Real)
          (max 0 (max (highReal 0) (max (highReal 1)
            (max (highReal 2) (max (highReal 3) (highReal 4)))))) :=
        max_le_max le_rfl (max_le_max le_rfl (max_le_max (hhigh 0)
          (max_le_max (hhigh 1) (max_le_max (hhigh 2)
            (max_le_max (hhigh 3) (hhigh 4))))))
      _ = i6D996TailLower label.1.2.2 z := by
        norm_num [i6D996TailLower, highReal, sectionSixThetaGap,
          sectionSixThetaOne, sectionSixThetaTwo]
  have hw : z.2 <= (box.upper 2 : Real) := by
    simpa [sectionSixFirstLowCentralSmallI5P0RationalCoordinates3] using
      hzBox.2 (2 : Fin 3)
  have hbranch := (i6D997TailBranchUpperAffine.eval_mem_interval box hzBox).2
  rw [i6D997TailBranchUpperAffine_eval] at hbranch
  have hUpper : i6D996TailUpper label.1.2.2 z <=
      (i6D997TailUpperCeiling label.1.2.2 box : Real) := by
    calc
      i6D996TailUpper label.1.2.2 z =
          min z.2 (min ((1 - z.1.1 - z.1.2 - z.2) / 4)
            (min 1 (min (lowReal 0) (min (lowReal 1)
              (min (lowReal 2) (min (lowReal 3) (lowReal 4))))))) := rfl
      _ <= min (box.upper 2 : Real)
          (min (i6D997TailBranchUpperAffine.maxOn box : Real)
            (min 1 (min (low 0 : Real) (min (low 1 : Real)
              (min (low 2 : Real) (min (low 3 : Real) (low 4 : Real))))))) :=
        min_le_min hw (min_le_min hbranch (min_le_min le_rfl (min_le_min (hlow 0)
          (min_le_min (hlow 1) (min_le_min (hlow 2) (min_le_min (hlow 3) (hlow 4)))))))
      _ = (i6D997TailUpperCeiling label.1.2.2 box : Real) := by
        simp [i6D997TailUpperCeiling, low]
  have hFloorPos : (0 : Real) < (i6D997TailLowerFloor label.1.2.2 box : Real) :=
    (Rat.cast_pos (K := Real)).2 (i6D997TailLowerFloor_pos label.1.2.2 box)
  exact ⟨hLower, hUpper, (hFloorPos.trans_le hLower).trans_le (hzOrdered.2.trans hUpper)⟩

end PrimesRestrictedDigits
