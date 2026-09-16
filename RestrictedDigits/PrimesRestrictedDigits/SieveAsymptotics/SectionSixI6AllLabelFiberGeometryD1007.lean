import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6SevenTailFiberGeometryD996
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6AffineEndpointSelectionD1004
import Mathlib.Tactic.FunProp

/-!
# Closed fibers for every I6 label

The exact endpoints retain the selected branch and every band wall. Source:
`MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace PrimesRestrictedDigits

noncomputable section

abbrev i6D1007Lower (label : i6D691Label) (z : (Real × Real) × Real) : Real :=
  sectionSixFirstLowBelowI6CellLower z.1.1 z.1.2 z.2 label.2.1 label.2.2

abbrev i6D1007Upper (label : i6D691Label) (z : (Real × Real) × Real) : Real :=
  sectionSixFirstLowBelowI6CellUpper z.1.1 z.1.2 z.2 label.2.1 label.2.2

def i6D1007OrderedBase (label : i6D691Label) : Set ((Real × Real) × Real) :=
  orderedOuter (i6D996TailBase label.1) (i6D1007Lower label) (i6D1007Upper label)

def i6D1007FiberCell (label : i6D691Label) : Set (((Real × Real) × Real) × Real) :=
  closedIccFiberCell (i6D996TailBase label.1) (i6D1007Lower label) (i6D1007Upper label)

theorem i6D1007_endpoints_continuous (label : i6D691Label) :
    Continuous (i6D1007Lower label) ∧ Continuous (i6D1007Upper label) := by
  have hhigh : ∀ i : Fin 5, Continuous (fun z : (Real × Real) × Real =>
      if label.2.2 i = true then sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 i
      else 0) := by
    intro i
    by_cases hi : label.2.2 i = true
    · simp only [hi, ite_true]
      fin_cases i <;> dsimp [sectionSixFirstLowBelowI6BandUpper] <;> fun_prop
    · simpa [hi] using
        (continuous_const : Continuous (fun _ : (Real × Real) × Real => (0 : Real)))
  have hlow : ∀ i : Fin 5, Continuous (fun z : (Real × Real) × Real =>
      if label.2.2 i = true then 1 else
        sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 i) := by
    intro i
    by_cases hi : label.2.2 i = true
    · simpa only [hi, ite_true] using
        (continuous_const : Continuous (fun _ : (Real × Real) × Real => (1 : Real)))
    · simp only [hi]
      fin_cases i <;> dsimp [sectionSixFirstLowBelowI6BandLower] <;> fun_prop
  have hbranch (b : Fin 3) :
      Continuous (fun z : (Real × Real) × Real =>
        sectionSixFirstLowBelowI6BranchLower z.1.1 z.1.2 z.2 b) ∧
      Continuous (fun z : (Real × Real) × Real =>
        sectionSixFirstLowBelowI6BranchUpper z.1.1 z.1.2 z.2 b) := by
    fin_cases b <;> constructor <;>
      dsimp [sectionSixFirstLowBelowI6BranchLower, sectionSixFirstLowBelowI6BranchUpper] <;>
      fun_prop
  exact ⟨continuous_const.max ((hbranch label.2.1).1.max (continuous_const.max
    ((hhigh 0).max ((hhigh 1).max ((hhigh 2).max ((hhigh 3).max (hhigh 4))))))),
    continuous_snd.min ((hbranch label.2.1).2.min (continuous_const.min
      ((hlow 0).min ((hlow 1).min ((hlow 2).min ((hlow 3).min (hlow 4)))))))⟩

theorem i6D1007_endpoint_bounds (label : i6D691Label) (z : (Real × Real) × Real) :
    sectionSixThetaGap (1 / 1000000 : Real) ≤ i6D1007Lower label z ∧
      sectionSixFirstLowBelowI6BranchLower z.1.1 z.1.2 z.2 label.2.1 ≤
        i6D1007Lower label z ∧
      i6D1007Upper label z ≤ z.2 ∧
      i6D1007Upper label z ≤
        sectionSixFirstLowBelowI6BranchUpper z.1.1 z.1.2 z.2 label.2.1 := by
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _)⟩

theorem i6D1007NativeTarget_subset_fiberCell (label : i6D691Label) :
    i6D691NativeTarget label ⊆ i6D1007FiberCell label := by
  rintro ⟨⟨⟨u, v⟩, w⟩, t⟩ hx
  have hregion := hx.1
  change sectionSixThetaGap (1 / 1000000 : Real) < t ∧
    t ≤ w ∧ w ≤ v ∧ v ≤ u ∧
    u + v < sectionSixThetaOne (1 / 1000000 : Real) ∧ _ at hregion
  rcases hregion with ⟨htgap, htw, hwv, hvu, huv, _⟩
  have hroot := i6D692_nativeTarget_subset_nativeRootCell label hx
  have hz : ((u, v), w) ∈ i6D996TailRootBase := by
    convert hroot.1 using 1
    norm_num [i6D996TailRootBase, i6D692RootBox, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hwone : w ≤ 1 := by
    have hw := hz.2.2
    norm_num [sectionSixThetaOne] at hw
    linarith
  have hbase := hx.2.1
  have hbranch := hx.2.2.1
  have hbranchBounds :
      sectionSixFirstLowBelowI6BranchLower u v w label.2.1 ≤ t ∧
      t ≤ sectionSixFirstLowBelowI6BranchUpper u v w label.2.1 := by
    generalize hb : label.2.1 = b at hbranch ⊢
    fin_cases b <;>
      simp [i6D690BranchHolds, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, Fin.sum_univ_succ,
        sectionSixFirstLowBelowI6BranchLower,
        sectionSixFirstLowBelowI6BranchUpper] at hbranch ⊢ <;> constructor <;> linarith
  have hlow : ∀ i, label.2.2 i = false ->
      t ≤ sectionSixFirstLowBelowI6BandLower u v w i := by
    intro i hi
    have h := hx.2.2.2 i
    simp only [i6D690SelectedBandConstraint, hi, ite_true] at h
    fin_cases i <;>
      simp [i6D690BandLowConstraint, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, Fin.sum_univ_succ, i6D690_thetaOne_cast,
        i6D690_reflectedLow_cast, i6D690Delta,
        sectionSixFirstLowBelowI6BandLower] at h ⊢ <;> linarith
  have hhigh : ∀ i, label.2.2 i = true ->
      sectionSixFirstLowBelowI6BandUpper u v w i ≤ t := by
    intro i hi
    have h := hx.2.2.2 i
    simp only [i6D690SelectedBandConstraint, hi, Bool.true_eq_false, if_false] at h
    fin_cases i <;>
      simp [i6D690BandHighConstraint, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, Fin.sum_univ_succ, i6D690_thetaTwo_cast,
        i6D690_reflectedHigh_cast, i6D690Delta,
        sectionSixFirstLowBelowI6BandUpper] at h ⊢ <;> linarith
  change ((u, v), w) ∈ i6D996TailBase label.1 ∧ _
  constructor
  · refine ⟨hz, hwv, hvu, huv.le, ?_⟩
    cases hrho : label.1 <;>
      norm_num [hrho, i6D690BaseConstraint, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, Fin.sum_univ_succ, i6D690_thetaOne_cast,
        i6D690_thetaTwo_cast, i6D690Delta] at hbase ⊢ <;> linarith
  · constructor
    · apply (i6D1004_cellLower_le_iff label ((u, v), w) t).mpr
      have heval (i : Fin 7) := congrFun (i6D1004LowerAffine_eval label.2.1 ((u, v), w)) i
      intro i hi
      rw [heval i]
      fin_cases i
      · exact htgap.le
      · exact hbranchBounds.1
      all_goals
        simp only [i6D1004LowerActive] at hi
        exact hhigh _ hi
    · apply (i6D1004_le_cellUpper_iff label ((u, v), w) t hwone).mpr
      have heval (i : Fin 7) := congrFun (i6D1004UpperAffine_eval label.2.1 ((u, v), w)) i
      intro i hi
      rw [heval i]
      fin_cases i
      · exact htw
      · exact hbranchBounds.2
      all_goals
        simp [i6D1004UpperActive, Matrix.cons_val] at hi
        exact hlow _ hi

end

end PrimesRestrictedDigits
