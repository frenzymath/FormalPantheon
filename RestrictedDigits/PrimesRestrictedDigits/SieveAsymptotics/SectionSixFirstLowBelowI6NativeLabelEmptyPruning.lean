import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelRetainedReplay
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowBelowI6NativeLabelEmptyPruning -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def i6D726Prunable (label : i6D691Label) : Prop :=
  label.1 = false ∧ label.2.2 (0 : Fin 5) = true

private theorem i6D726_nativeTarget_empty_of_prunable
    (label : i6D691Label) (hprune : i6D726Prunable label) :
    i6D691NativeTarget label =
      (∅ : Set (((Real × Real) × Real) × Real)) := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  rcases hnonempty with ⟨x, hx⟩
  have hregion := hx.1
  have hholds := hx.2
  rcases hprune with ⟨hrho, hsigma⟩
  have hbase : x.1.1.1 + x.1.1.2 + x.1.2 <
      sectionSixThetaOne (1 / 1000000 : Real) := by
    have hbase0 : (i6D690BaseConstraint false).holds
        (i6D686Coordinates x) := by
      simpa [hrho] using hholds.1
    convert hbase0 using 1
    all_goals
      simp [i6D690BaseConstraint, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, Fin.sum_univ_succ, i6D690Delta,
        i6D690_thetaOne_cast]
      ring
  have hband := hholds.2.2 (0 : Fin 5)
  simp [i6D690SelectedBandConstraint, hsigma, i6D690BandHighConstraint,
    i6D690Constraint, i6D690Affine, RationalAffineConstraint.holds,
    RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
    i6D690_thetaTwo_cast] at hband
  have hband' : sectionSixThetaTwo (1 / 1000000 : Real) <
      x.1.1.1 + x.1.1.2 + x.2 := by
    simpa [i6D690Delta, add_assoc] using hband
  have htw : x.2 ≤ x.1.2 := hregion.2.1
  have hlt : x.1.1.1 + x.1.1.2 + x.2 <
      sectionSixThetaOne (1 / 1000000 : Real) := by
    linarith
  have htheta : sectionSixThetaOne (1 / 1000000 : Real) <
      sectionSixThetaTwo (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaOne, sectionSixThetaTwo]
  linarith

theorem sectionSixFirstLowBelowI6_native_target_sigma_monotone
    (label : i6D691Label)
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D691NativeTarget label) :
    (label.2.2 1 = true -> label.2.2 0 = true) ∧
      (label.2.2 2 = true -> label.2.2 1 = true) := by
  constructor
  · intro hs1
    by_contra hs0
    have hs0' : label.2.2 0 = false := by
      cases h : label.2.2 0 <;> simp_all
    have h0 := hx.2.2.2 0
    have h1 := hx.2.2.2 1
    simp [i6D690SelectedBandConstraint, i6D690BandLowConstraint,
      i6D690BandHighConstraint, hs0', hs1, i6D690Constraint,
      i6D690Affine, RationalAffineConstraint.holds,
      RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
      i6D690_thetaOne_cast, i6D690_thetaTwo_cast] at h0 h1
    have hwv : x.1.2 ≤ x.1.1.2 := hx.1.2.2.1
    have hcomp : x.1.1.1 + x.1.2 + x.2 ≤
        x.1.1.1 + x.1.1.2 + x.2 := by
      linarith
    norm_num [i6D690Delta, sectionSixThetaOne, sectionSixThetaTwo] at h0 h1
    linarith
  · intro hs2
    by_contra hs1
    have hs1' : label.2.2 1 = false := by
      cases h : label.2.2 1 <;> simp_all
    have h1 := hx.2.2.2 1
    have h2 := hx.2.2.2 2
    simp [i6D690SelectedBandConstraint, i6D690BandLowConstraint,
      i6D690BandHighConstraint, hs1', hs2, i6D690Constraint,
      i6D690Affine, RationalAffineConstraint.holds,
      RationalAffine.evalReal, i6D686Coordinates, Fin.sum_univ_succ,
      i6D690_thetaOne_cast, i6D690_thetaTwo_cast] at h1 h2
    have hvu : x.1.1.2 ≤ x.1.1.1 := hx.1.2.2.2.1
    have hcomp : x.1.1.2 + x.1.2 + x.2 ≤
        x.1.1.1 + x.1.2 + x.2 := by
      linarith
    norm_num [i6D690Delta, sectionSixThetaOne, sectionSixThetaTwo] at h1 h2
    linarith

def sectionSixFirstLowBelowI6D726EmptyLabel : i6D691Label :=
  (false, ((0 : Fin 3), fun _ : Fin 5 => true))

def sectionSixFirstLowBelowI6D726EmptyTree :
    RationalSubdivision 4 Unit := .retain ()

def sectionSixFirstLowBelowI6D726EmptyPayloadValid
    (_ : RationalBox 4) (_ : Unit) : Bool := true

def sectionSixFirstLowBelowI6D726EmptyPayloadWeight
    (_ : RationalBox 4) (_ : Unit) : Rat := 0

theorem sectionSixFirstLowBelowI6D726EmptyLabel_nativeTarget_empty :
    i6D691NativeTarget sectionSixFirstLowBelowI6D726EmptyLabel =
      (∅ : Set (((Real × Real) × Real) × Real)) := by
  apply i6D726_nativeTarget_empty_of_prunable
  constructor <;> simp [sectionSixFirstLowBelowI6D726EmptyLabel]

theorem sectionSixFirstLowBelowI6D726EmptyTree_coverValid :
    sectionSixFirstLowBelowI6D726EmptyTree.coverValid
      (i6D691Constraints sectionSixFirstLowBelowI6D726EmptyLabel)
      sectionSixFirstLowBelowI6D726EmptyPayloadValid i6D692RootBox = true := by
  have ho : i6D692RootBox.IsOrdered := by
    intro i
    fin_cases i <;> norm_num [i6D692RootBox]
  change i6D692RootBox.orderedBool && true = true
  change decide i6D692RootBox.IsOrdered && true = true
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨ho, trivial⟩

theorem sectionSixFirstLowBelowI6D726EmptyTree_replayWeight_zero :
    sectionSixFirstLowBelowI6D726EmptyTree.replayWeightRat i6D692RootBox
      sectionSixFirstLowBelowI6D726EmptyPayloadWeight = 0 := by
  simp [sectionSixFirstLowBelowI6D726EmptyTree,
    RationalSubdivision.replayWeightRat,
    sectionSixFirstLowBelowI6D726EmptyPayloadWeight]

theorem sectionSixFirstLowBelowI6D726EmptyLabel_integral_zero :
    (∫ x in i6D691NativeTarget sectionSixFirstLowBelowI6D726EmptyLabel,
      sectionSixFirstLowBelowQuadrupleKernel x ∂volume) = 0 := by
  rw [sectionSixFirstLowBelowI6D726EmptyLabel_nativeTarget_empty]
  simp

theorem sectionSixFirstLowBelowI6D726EmptyLabel_integral_le_replayWeight :
    (∫ x in i6D691NativeTarget sectionSixFirstLowBelowI6D726EmptyLabel,
      sectionSixFirstLowBelowQuadrupleKernel x ∂volume) ≤
      (sectionSixFirstLowBelowI6D726EmptyTree.replayWeightRat i6D692RootBox
        sectionSixFirstLowBelowI6D726EmptyPayloadWeight : Real) := by
  rw [sectionSixFirstLowBelowI6D726EmptyLabel_integral_zero,
    sectionSixFirstLowBelowI6D726EmptyTree_replayWeight_zero]
  norm_num

end

end PrimesRestrictedDigits
