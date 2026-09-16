import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelEmptyPruning
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowBelowI6NativeLabelGenericEmpty -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem i6D727_native_target_empty_of_rhoFalse_sigmaZero
    (label : i6D691Label)
    (hrho : label.1 = false)
    (hsigma : label.2.2 (0 : Fin 5) = true) :
    i6D691NativeTarget label =
      (∅ : Set (((Real × Real) × Real) × Real)) := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  rcases hnonempty with ⟨x, hx⟩
  have hregion := hx.1
  have hholds := hx.2
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

theorem i6D727_native_target_integral_zero_of_rhoFalse_sigmaZero
    (label : i6D691Label)
    (hrho : label.1 = false)
    (hsigma : label.2.2 (0 : Fin 5) = true) :
    (∫ x in i6D691NativeTarget label,
      sectionSixFirstLowBelowQuadrupleKernel x ∂volume) = 0 := by
  rw [i6D727_native_target_empty_of_rhoFalse_sigmaZero label hrho hsigma]
  simp

end

end PrimesRestrictedDigits
