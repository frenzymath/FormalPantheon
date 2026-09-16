import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelActiveReduction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Necessary branch pruning for the fixed I6 native labels

Native-target membership forces branch-specific selector consequences. This module is a
pointwise necessary filter only; it contains no nonemptiness, subdivision, replay, or
numerical estimate.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowBelowI6_native_target_rhoFalse_forces_branchTwo
    (label : i6D691Label)
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D691NativeTarget label)
    (hrho : label.1 = false) :
    label.2.1 = (2 : Fin 3) := by
  have hregion := hx.1
  have hholds := hx.2
  have hbase := hholds.1
  simp [i6D690BaseConstraint, hrho, i6D690Constraint, i6D690Affine,
    RationalAffineConstraint.holds, RationalAffine.evalReal,
    i6D686Coordinates, Fin.sum_univ_succ, i6D690_thetaOne_cast] at hbase
  have hbase' : x.1.1.1 + x.1.1.2 + x.1.2 <
      sectionSixThetaOne (1 / 1000000 : Real) := by
    simpa [i6D690Delta, add_assoc] using hbase
  have hthreeT : 3 * x.2 <=
      x.1.1.1 + x.1.1.2 + x.1.2 := by
    have htw := hregion.2.1
    have hwv := hregion.2.2.1
    have hvu := hregion.2.2.2.1
    linarith
  have htheta : 2 * sectionSixThetaOne (1 / 1000000 : Real) <
      (1 : Real) := by
    norm_num [sectionSixThetaOne]
  have htheta7 : 7 * sectionSixThetaOne (1 / 1000000 : Real) <
      (3 : Real) := by
    norm_num [sectionSixThetaOne]
  have hne0 : label.2.1 ≠ (0 : Fin 3) := by
    intro hb
    have hbranch := hholds.2.1
    simp [i6D690BranchHolds, hb, i6D690Constraint, i6D690Affine,
      RationalAffineConstraint.holds, RationalAffine.evalReal,
      i6D686Coordinates, Fin.sum_univ_succ] at hbranch
    have hlower : (1 : Real) <=
        x.1.1.1 + x.1.1.2 + x.1.2 + 3 * x.2 := by
      linarith [hbranch.2]
    linarith
  have hne1 : label.2.1 ≠ (1 : Fin 3) := by
    intro hb
    have hbranch := hholds.2.1
    simp [i6D690BranchHolds, hb, i6D690Constraint, i6D690Affine,
      RationalAffineConstraint.holds, RationalAffine.evalReal,
      i6D686Coordinates, Fin.sum_univ_succ] at hbranch
    have hlower : (1 : Real) <=
        x.1.1.1 + x.1.1.2 + x.1.2 + 4 * x.2 := by
      linarith [hbranch.2]
    linarith [htheta7]
  have hbCases : label.2.1 = (0 : Fin 3) ∨
      label.2.1 = (1 : Fin 3) ∨ label.2.1 = (2 : Fin 3) := by
    let b : Fin 3 := label.2.1
    have hb : b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨ b = (2 : Fin 3) := by
      refine Fin.cases (Or.inl rfl) (fun j => ?_) b
      refine Fin.cases (Or.inr (Or.inl rfl)) (fun k => ?_) j
      refine Fin.cases (Or.inr (Or.inr rfl)) (fun l => ?_) k
      exact Fin.elim0 l
    simpa [b] using hb
  rcases hbCases with hb | hb | hb
  · exact (hne0 hb).elim
  · exact (hne1 hb).elim
  · exact hb

theorem sectionSixFirstLowBelowI6_native_target_branchZero_forces_allHigh
    (label : i6D691Label)
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D691NativeTarget label)
    (hb : label.2.1 = (0 : Fin 3)) :
    ∀ i : Fin 5, label.2.2 i = true := by
  have hregion := hx.1
  have hholds := hx.2
  have hbranch := hholds.2.1
  simp [i6D690BranchHolds, hb, i6D690Constraint, i6D690Affine,
    RationalAffineConstraint.holds, RationalAffine.evalReal,
    i6D686Coordinates, Fin.sum_univ_succ] at hbranch
  have hlower : (1 : Real) <=
      x.1.1.1 + x.1.1.2 + x.1.2 + 3 * x.2 := by
    linarith [hbranch.2]
  have hupper : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1 := by
    linarith [hbranch.1]
  have huv := hregion.2.2.2.2.1
  have htw := hregion.2.1
  have hwv := hregion.2.2.1
  have hvu := hregion.2.2.2.1
  have hC : sectionSixThetaTwo (1 / 1000000 : Real) <
      x.1.1.2 + x.1.2 + x.2 := by
    by_contra hCnot
    have hCle : x.1.1.2 + x.1.2 + x.2 <=
        sectionSixThetaTwo (1 / 1000000 : Real) := le_of_not_gt hCnot
    have hmul : 3 * (x.1.2 + 3 * x.2) <=
        4 * (x.1.1.2 + x.1.2 + x.2) := by
      linarith
    have hbound : 3 *
        (x.1.1.1 + x.1.1.2 + x.1.2 + 3 * x.2) <
        3 * sectionSixThetaOne (1 / 1000000 : Real) +
          4 * (x.1.1.2 + x.1.2 + x.2) := by
      linarith
    have hnumeric : 3 * sectionSixThetaOne (1 / 1000000 : Real) +
        4 * sectionSixThetaTwo (1 / 1000000 : Real) < (3 : Real) := by
      norm_num [sectionSixThetaOne, sectionSixThetaTwo]
    linarith
  have htwoT : 2 * x.2 <
      sectionSixThetaOne (1 / 1000000 : Real) := by
    linarith
  have hF : 1 - sectionSixThetaOne (1 / 1000000 : Real) <
      x.1.1.1 + x.1.1.2 + x.1.2 + x.2 := by
    linarith
  intro i
  fin_cases i
  · cases hs : label.2.2 (0 : Fin 5)
    · have hband := hholds.2.2 (0 : Fin 5)
      simp [i6D690SelectedBandConstraint, hs, i6D690BandLowConstraint,
        i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
        RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
        i6D690_thetaOne_cast] at hband
      have hA : x.1.1.1 + x.1.1.2 + x.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := by
        simpa [i6D690Delta, add_assoc] using hband
      have hAC : x.1.1.2 + x.1.2 + x.2 <=
          x.1.1.1 + x.1.1.2 + x.2 := by linarith
      exfalso
      norm_num [sectionSixThetaOne, sectionSixThetaTwo] at hC hA
      linarith
    · simpa using hs
  · cases hs : label.2.2 (1 : Fin 5)
    · have hband := hholds.2.2 (1 : Fin 5)
      simp [i6D690SelectedBandConstraint, hs, i6D690BandLowConstraint,
        i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
        RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
        i6D690_thetaOne_cast] at hband
      have hB : x.1.1.1 + x.1.2 + x.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := by
        simpa [i6D690Delta, add_assoc] using hband
      have hBC : x.1.1.2 + x.1.2 + x.2 <=
          x.1.1.1 + x.1.2 + x.2 := by linarith
      exfalso
      norm_num [sectionSixThetaOne, sectionSixThetaTwo] at hC hB
      linarith
    · simpa using hs
  · cases hs : label.2.2 (2 : Fin 5)
    · have hband := hholds.2.2 (2 : Fin 5)
      simp [i6D690SelectedBandConstraint, hs, i6D690BandLowConstraint,
        i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
        RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
        i6D690_thetaOne_cast] at hband
      have hC' : x.1.1.2 + x.1.2 + x.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := by
        simpa [i6D690Delta, add_assoc] using hband
      exfalso
      norm_num [sectionSixThetaOne, sectionSixThetaTwo] at hC hC'
      linarith
    · simpa using hs
  · cases hs : label.2.2 (3 : Fin 5)
    · have hband := hholds.2.2 (3 : Fin 5)
      simp [i6D690SelectedBandConstraint, hs, i6D690BandLowConstraint,
        i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
        RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
        i6D690_thetaOne_cast] at hband
      have hF' : x.1.1.1 + x.1.1.2 + x.1.2 + x.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := by
        simpa [i6D690Delta, add_assoc] using hband
      exfalso
      norm_num [sectionSixThetaOne, sectionSixThetaTwo] at hF hF'
      linarith
    · simpa using hs
  · cases hs : label.2.2 (4 : Fin 5)
    · have hband := hholds.2.2 (4 : Fin 5)
      simp [i6D690SelectedBandConstraint, hs, i6D690BandLowConstraint,
        i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
        RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
        i6D690_reflectedLow_cast] at hband
      have hF' : x.1.1.1 + x.1.1.2 + x.1.2 + x.2 <
          1 - sectionSixThetaTwo (1 / 1000000 : Real) := by
        simpa [i6D690Delta, add_assoc] using hband
      exfalso
      norm_num [sectionSixThetaOne, sectionSixThetaTwo] at hF hF'
      linarith
    · simpa using hs

theorem sectionSixFirstLowBelowI6_native_target_branchOne_forces_firstThreeHigh
    (label : i6D691Label)
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D691NativeTarget label)
    (hb : label.2.1 = (1 : Fin 3)) :
    label.2.2 (0 : Fin 5) = true ∧
      label.2.2 (1 : Fin 5) = true ∧
      label.2.2 (2 : Fin 5) = true := by
  have hregion := hx.1
  have hholds := hx.2
  have hbranch := hholds.2.1
  simp [i6D690BranchHolds, hb, i6D690Constraint, i6D690Affine,
    RationalAffineConstraint.holds, RationalAffine.evalReal,
    i6D686Coordinates, Fin.sum_univ_succ] at hbranch
  have hlower : (1 : Real) <=
      x.1.1.1 + x.1.1.2 + x.1.2 + 4 * x.2 := by
    linarith [hbranch.2]
  have huv := hregion.2.2.2.2.1
  have htw := hregion.2.1
  have hwv := hregion.2.2.1
  have hvu := hregion.2.2.2.1
  have hCsmall_impossible : ¬
      x.1.1.2 + x.1.2 + x.2 <
        sectionSixThetaOne (1 / 1000000 : Real) := by
    intro hCsmall
    have hmul : 3 * (x.1.2 + 4 * x.2) <=
        5 * (x.1.1.2 + x.1.2 + x.2) := by
      linarith
    have hbound : 3 *
        (x.1.1.1 + x.1.1.2 + x.1.2 + 4 * x.2) <
        3 * sectionSixThetaOne (1 / 1000000 : Real) +
          5 * (x.1.1.2 + x.1.2 + x.2) := by
      linarith
    have hnumeric : 8 * sectionSixThetaOne (1 / 1000000 : Real) <
        (3 : Real) := by
      norm_num [sectionSixThetaOne]
    linarith
  have h0 : label.2.2 (0 : Fin 5) = true := by
    cases hs : label.2.2 (0 : Fin 5)
    · have hband := hholds.2.2 (0 : Fin 5)
      simp [i6D690SelectedBandConstraint, hs, i6D690BandLowConstraint,
        i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
        RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
        i6D690_thetaOne_cast] at hband
      have hA : x.1.1.1 + x.1.1.2 + x.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := by
        simpa [i6D690Delta, add_assoc] using hband
      have hAC : x.1.1.2 + x.1.2 + x.2 <=
          x.1.1.1 + x.1.1.2 + x.2 := by linarith
      exfalso
      have hCsmall : x.1.1.2 + x.1.2 + x.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := lt_of_le_of_lt hAC hA
      exact (hCsmall_impossible hCsmall).elim
    · rfl
  have h1 : label.2.2 (1 : Fin 5) = true := by
    cases hs : label.2.2 (1 : Fin 5)
    · have hband := hholds.2.2 (1 : Fin 5)
      simp [i6D690SelectedBandConstraint, hs, i6D690BandLowConstraint,
        i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
        RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
        i6D690_thetaOne_cast] at hband
      have hB : x.1.1.1 + x.1.2 + x.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := by
        simpa [i6D690Delta, add_assoc] using hband
      have hBC : x.1.1.2 + x.1.2 + x.2 <=
          x.1.1.1 + x.1.2 + x.2 := by linarith
      exfalso
      have hCsmall : x.1.1.2 + x.1.2 + x.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := lt_of_le_of_lt hBC hB
      exact (hCsmall_impossible hCsmall).elim
    · rfl
  have h2 : label.2.2 (2 : Fin 5) = true := by
    cases hs : label.2.2 (2 : Fin 5)
    · have hband := hholds.2.2 (2 : Fin 5)
      simp [i6D690SelectedBandConstraint, hs, i6D690BandLowConstraint,
        i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
        RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
        i6D690_thetaOne_cast] at hband
      have hC' : x.1.1.2 + x.1.2 + x.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := by
        simpa [i6D690Delta, add_assoc] using hband
      exfalso
      exact (hCsmall_impossible hC').elim
    · rfl
  exact ⟨h0, h1, h2⟩

def sectionSixFirstLowBelowI6D731BranchPrunedLabel
    (label : i6D691Label) : Prop :=
  sectionSixFirstLowBelowI6D730ActiveLabel label ∧
    (label.1 = false -> label.2.1 = (2 : Fin 3)) ∧
    (label.2.1 = (0 : Fin 3) ->
      ∀ i : Fin 5, label.2.2 i = true) ∧
    (label.2.1 = (1 : Fin 3) ->
      label.2.2 (0 : Fin 5) = true ∧
      label.2.2 (1 : Fin 5) = true ∧
      label.2.2 (2 : Fin 5) = true)

theorem sectionSixFirstLowBelowI6_native_membership_branchPruned
    (label : i6D691Label)
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D691NativeTarget label) :
    sectionSixFirstLowBelowI6D731BranchPrunedLabel label := by
  refine ⟨sectionSixFirstLowBelowI6_native_membership_admissible label hx,
    ?_, ?_, ?_⟩
  · intro hrho
    exact sectionSixFirstLowBelowI6_native_target_rhoFalse_forces_branchTwo
      label hx hrho
  · intro hb
    exact sectionSixFirstLowBelowI6_native_target_branchZero_forces_allHigh
      label hx hb
  · intro hb
    exact sectionSixFirstLowBelowI6_native_target_branchOne_forces_firstThreeHigh
      label hx hb

end

end PrimesRestrictedDigits
