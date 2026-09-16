import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelCandidateSubset
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6TightRootBox
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6FiberCover
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberOrderedOuter
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Closed fibers containing the seven I6 tail targets

The exact branch-two endpoints retain all selected affine walls. The base closes the native
strict faces only in the containing direction.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), pp. 143--144.
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace PrimesRestrictedDigits

noncomputable section

def i6D996SevenTailLabels : Finset i6D691Label :=
  i6D731CandidateLabels.filter fun label => label.2.1 = (2 : Fin 3)

abbrev i6D996TailLabel :=
  {label : i6D691Label // label ∈ i6D996SevenTailLabels}

def i6D996TailRootBase : Set ((Real × Real) × Real) :=
  (Icc (sectionSixThetaGap (1 / 1000000 : Real))
      (sectionSixThetaOne (1 / 1000000 : Real)) ×ˢ
    Icc (sectionSixThetaGap (1 / 1000000 : Real))
      (sectionSixThetaOne (1 / 1000000 : Real))) ×ˢ
  Icc (sectionSixThetaGap (1 / 1000000 : Real))
    (sectionSixThetaOne (1 / 1000000 : Real))

def i6D996TailBase (rho : Bool) : Set ((Real × Real) × Real) :=
  {z | z ∈ i6D996TailRootBase ∧ z.2 <= z.1.2 ∧ z.1.2 <= z.1.1 ∧
    z.1.1 + z.1.2 <= sectionSixThetaOne (1 / 1000000 : Real) ∧
    match rho with
    | false => z.1.1 + z.1.2 + z.2 <= sectionSixThetaOne (1 / 1000000 : Real)
    | true => sectionSixThetaTwo (1 / 1000000 : Real) <= z.1.1 + z.1.2 + z.2}

def i6D996TailLower
    (sigma : Fin 5 → Bool) (z : ((Real × Real) × Real)) : Real :=
  let high : Fin 5 → Real := fun i =>
    if sigma i = true then sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 i else 0
  max (sectionSixThetaGap (1 / 1000000 : Real))
    (max 0 (max (high 0) (max (high 1) (max (high 2) (max (high 3) (high 4))))))

def i6D996TailUpper
    (sigma : Fin 5 → Bool) (z : ((Real × Real) × Real)) : Real :=
  let low : Fin 5 → Real := fun i =>
    if sigma i = true then 1 else sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 i
  min z.2 (min ((1 - z.1.1 - z.1.2 - z.2) / 4)
    (min 1 (min (low 0) (min (low 1) (min (low 2) (min (low 3) (low 4)))))))

def i6D996TailOrderedBase (label : i6D996TailLabel) : Set ((Real × Real) × Real) :=
  orderedOuter (i6D996TailBase label.1.1)
    (i6D996TailLower label.1.2.2) (i6D996TailUpper label.1.2.2)

def i6D996TailFiberCell (label : i6D996TailLabel) :
    Set (((Real × Real) × Real) × Real) :=
  closedIccFiberCell (i6D996TailBase label.1.1)
    (i6D996TailLower label.1.2.2) (i6D996TailUpper label.1.2.2)

theorem i6D996_mem_sevenTailLabels_iff {label : i6D691Label} :
    label ∈ i6D996SevenTailLabels ↔
      label ∈ i6D731CandidateLabels ∧ label.2.1 = (2 : Fin 3) :=
  Finset.mem_filter

theorem i6D996SevenTailLabels_card : i6D996SevenTailLabels.card = 7 := by
  decide +kernel

theorem i6D996Tail_endpoints_eq_cellEndpoints
    (sigma : Fin 5 → Bool) (z : ((Real × Real) × Real)) :
    i6D996TailLower sigma z =
        sectionSixFirstLowBelowI6CellLower z.1.1 z.1.2 z.2 (2 : Fin 3) sigma ∧
      i6D996TailUpper sigma z =
        sectionSixFirstLowBelowI6CellUpper z.1.1 z.1.2 z.2 (2 : Fin 3) sigma := by
  constructor
  · let high : Fin 5 → Real := fun i => if sigma i = true then
      sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 i else 0
    let M := max 0 (max (high 0) (max (high 1) (max (high 2) (max (high 3) (high 4)))))
    change max (sectionSixThetaGap (1 / 1000000 : Real)) M =
      max (sectionSixThetaGap (1 / 1000000 : Real))
        (max (sectionSixThetaGap (1 / 1000000 : Real)) M)
    calc
      _ = max (max (sectionSixThetaGap (1 / 1000000 : Real))
          (sectionSixThetaGap (1 / 1000000 : Real))) M := by rw [max_self]
      _ = _ := max_assoc _ _ _
  · rfl

theorem i6D996TailTarget_subset_fiberCell (label : i6D996TailLabel) :
    i6D691NativeTarget label.1 ⊆ i6D996TailFiberCell label := by
  rintro ⟨⟨⟨u, v⟩, w⟩, t⟩ hx
  have hregion := hx.1
  change sectionSixThetaGap (1 / 1000000 : Real) < t ∧
    t <= w ∧ w <= v ∧ v <= u ∧
    u + v < sectionSixThetaOne (1 / 1000000 : Real) ∧ _ at hregion
  rcases hregion with ⟨htgap, htw, hwv, hvu, huv, _⟩
  have hroot := i6D692_nativeTarget_subset_nativeRootCell label.1 hx
  have hz : ((u, v), w) ∈ i6D996TailRootBase := by
    have hrootBase := hroot.1
    convert hrootBase using 1
    norm_num [i6D996TailRootBase, i6D692RootBox, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have htpos : 0 < t := hgap.trans htgap
  have htone : t <= 1 := by
    have hw := hz.2.2
    norm_num [sectionSixThetaOne] at hw
    linarith
  have hbase := hx.2.1
  have hbranch := hx.2.2.1
  have hb := (i6D996_mem_sevenTailLabels_iff.mp label.2).2
  have htbranch : t <= (1 - u - v - w) / 4 := by
    simp [hb, i6D690BranchHolds, i6D690Constraint, i6D690Affine,
      RationalAffineConstraint.holds, RationalAffine.evalReal,
      i6D686Coordinates, Fin.sum_univ_succ] at hbranch
    linarith
  have hlow : ∀ i, label.1.2.2 i = false ->
      t <= sectionSixFirstLowBelowI6BandLower u v w i := by
    intro i hi
    have h := hx.2.2.2 i
    simp only [i6D690SelectedBandConstraint, hi, ite_true] at h
    fin_cases i <;>
      simp [i6D690BandLowConstraint, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, Fin.sum_univ_succ, i6D690_thetaOne_cast,
        i6D690_reflectedLow_cast, i6D690Delta,
        sectionSixFirstLowBelowI6BandLower] at h ⊢ <;> linarith
  have hhigh : ∀ i, label.1.2.2 i = true ->
      sectionSixFirstLowBelowI6BandUpper u v w i <= t := by
    intro i hi
    have h := hx.2.2.2 i
    simp only [i6D690SelectedBandConstraint, hi, Bool.true_eq_false, if_false] at h
    fin_cases i <;>
      simp [i6D690BandHighConstraint, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, Fin.sum_univ_succ, i6D690_thetaTwo_cast,
        i6D690_reflectedHigh_cast, i6D690Delta,
        sectionSixFirstLowBelowI6BandUpper] at h ⊢ <;> linarith
  have hhighTerms : ∀ i, (if label.1.2.2 i = true then
      sectionSixFirstLowBelowI6BandUpper u v w i else 0) <= t := by
    intro i
    split_ifs with hi
    · exact hhigh i hi
    · exact htpos.le
  have hlowTerms : ∀ i, t <= (if label.1.2.2 i = true then 1 else
      sectionSixFirstLowBelowI6BandLower u v w i) := by
    intro i
    split_ifs with hi
    · exact htone
    · exact hlow i (by cases hs : label.1.2.2 i <;> simp_all)
  change ((u, v), w) ∈ i6D996TailBase label.1.1 ∧ _
  constructor
  · refine ⟨hz, hwv, hvu, huv.le, ?_⟩
    cases hrho : label.1.1 <;>
      norm_num [hrho, i6D690BaseConstraint, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, Fin.sum_univ_succ, i6D690_thetaOne_cast,
        i6D690_thetaTwo_cast, i6D690Delta] at hbase ⊢ <;> linarith
  · constructor
    · exact max_le htgap.le (max_le htpos.le (max_le (hhighTerms 0)
        (max_le (hhighTerms 1) (max_le (hhighTerms 2)
          (max_le (hhighTerms 3) (hhighTerms 4))))))
    · exact le_min htw (le_min htbranch (le_min htone (le_min (hlowTerms 0)
        (le_min (hlowTerms 1) (le_min (hlowTerms 2)
          (le_min (hlowTerms 3) (hlowTerms 4)))))))

end

end PrimesRestrictedDigits
