import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelGenericEmpty
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowBelowI6NativeLabelSigmaExtremes -/

open Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowBelowI6_native_target_sigmaThree_false_forces_all_low
    (label : i6D691Label)
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D691NativeTarget label)
    (hthree : label.2.2 (3 : Fin 5) = false) :
    label.1 = false ∧ ∀ i : Fin 5, label.2.2 i = false := by
  have hregion := hx.1
  have hholds := hx.2
  have hfull := hholds.2.2 (3 : Fin 5)
  simp [i6D690SelectedBandConstraint, hthree, i6D690BandLowConstraint,
    i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
    RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
    i6D690_thetaOne_cast] at hfull
  have hfull' : x.1.1.1 + x.1.1.2 + x.1.2 + x.2 <
      sectionSixThetaOne (1 / 1000000 : Real) := by
    simpa [i6D690Delta, add_assoc] using hfull
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have ht : 0 < x.2 := hgap.trans hregion.1
  have hw : 0 < x.1.2 := lt_of_lt_of_le ht hregion.2.1
  have hrho : label.1 = false := by
    cases hr : label.1
    · rfl
    · have hbase := hholds.1
      simp [i6D690BaseConstraint, hr, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, Fin.sum_univ_succ, i6D690_thetaTwo_cast] at hbase
      have hbase' : sectionSixThetaTwo (1 / 1000000 : Real) <
          x.1.1.1 + x.1.1.2 + x.1.2 := by
        simpa [i6D690Delta, add_assoc] using hbase
      norm_num [sectionSixThetaOne, sectionSixThetaTwo] at hfull' hbase'
      linarith
  have hsigmaZero : label.2.2 (0 : Fin 5) = false := by
    cases hzero : label.2.2 (0 : Fin 5)
    · rfl
    · have hband := hholds.2.2 (0 : Fin 5)
      simp [i6D690SelectedBandConstraint, hzero, i6D690BandHighConstraint,
        i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
        RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
        i6D690_thetaTwo_cast] at hband
      have hband' : sectionSixThetaTwo (1 / 1000000 : Real) <
          x.1.1.1 + x.1.1.2 + x.2 := by
        simpa [i6D690Delta, add_assoc] using hband
      norm_num [sectionSixThetaOne, sectionSixThetaTwo] at hfull' hband'
      linarith
  refine ⟨hrho, ?_⟩
  intro i
  fin_cases i
  · exact hsigmaZero
  · cases hone : label.2.2 (1 : Fin 5)
    · simpa using hone
    · have h := (sectionSixFirstLowBelowI6_native_target_sigma_monotone
          label hx).1 hone
      simp_all
  · cases htwo : label.2.2 (2 : Fin 5)
    · simpa using htwo
    · have hone := (sectionSixFirstLowBelowI6_native_target_sigma_monotone
          label hx).2 htwo
      have hzero := (sectionSixFirstLowBelowI6_native_target_sigma_monotone
          label hx).1 hone
      simp_all
  · simpa using hthree
  · by_contra hfour
    have hfour' : label.2.2 (4 : Fin 5) = true := by
      cases h : label.2.2 (4 : Fin 5) <;> simp_all
    have hband := hholds.2.2 (4 : Fin 5)
    simp [i6D690SelectedBandConstraint, hfour', i6D690BandHighConstraint,
      i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
      RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
      i6D690_reflectedHigh_cast] at hband
    have hband' : 1 - sectionSixThetaOne (1 / 1000000 : Real) <
        x.1.1.1 + x.1.1.2 + x.1.2 + x.2 := by
      simpa [i6D690Delta, add_assoc] using hband
    norm_num [sectionSixThetaOne] at hfull' hband'
    linarith

theorem sectionSixFirstLowBelowI6_native_target_sigmaFour_true_forces_all_high
    (label : i6D691Label)
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D691NativeTarget label)
    (hfour : label.2.2 (4 : Fin 5) = true) :
    label.1 = true ∧ ∀ i : Fin 5, label.2.2 i = true := by
  have hregion := hx.1
  have hholds := hx.2
  have hfull := hholds.2.2 (4 : Fin 5)
  simp [i6D690SelectedBandConstraint, hfour, i6D690BandHighConstraint,
    i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
    RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
    i6D690_reflectedHigh_cast] at hfull
  have hfull' : 1 - sectionSixThetaOne (1 / 1000000 : Real) <
      x.1.1.1 + x.1.1.2 + x.1.2 + x.2 := by
    simpa [i6D690Delta, add_assoc] using hfull
  have hsigmaTwo : label.2.2 (2 : Fin 5) = true := by
    cases htwo : label.2.2 (2 : Fin 5)
    · have hband := hholds.2.2 (2 : Fin 5)
      simp [i6D690SelectedBandConstraint, htwo, i6D690BandLowConstraint,
        i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
        RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
        i6D690_thetaOne_cast] at hband
      have hband' : x.1.1.2 + x.1.2 + x.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := by
        simpa [i6D690Delta, add_assoc] using hband
      have huv : x.1.1.1 + x.1.1.2 <
          sectionSixThetaOne (1 / 1000000 : Real) := hregion.2.2.2.2.1
      have hwv : x.1.2 ≤ x.1.1.2 := hregion.2.2.1
      have htv : x.2 ≤ x.1.1.2 := hregion.2.1.trans hwv
      norm_num [sectionSixThetaOne] at hfull' hband' huv
      linarith
    · rfl
  have hmono := sectionSixFirstLowBelowI6_native_target_sigma_monotone label hx
  have hsigmaOne := hmono.2 hsigmaTwo
  have hsigmaZero := hmono.1 hsigmaOne
  have hrho : label.1 = true := by
    cases hr : label.1
    · have hempty := i6D727_native_target_empty_of_rhoFalse_sigmaZero
          label hr hsigmaZero
      rw [hempty] at hx
      exact hx.elim
    · rfl
  refine ⟨hrho, ?_⟩
  intro i
  fin_cases i
  · exact hsigmaZero
  · exact hsigmaOne
  · exact hsigmaTwo
  · cases hthree : label.2.2 (3 : Fin 5)
    · have hlow :=
          sectionSixFirstLowBelowI6_native_target_sigmaThree_false_forces_all_low
            label hx hthree
      simp_all
    · simpa using hthree
  · exact hfour

end

end PrimesRestrictedDigits
