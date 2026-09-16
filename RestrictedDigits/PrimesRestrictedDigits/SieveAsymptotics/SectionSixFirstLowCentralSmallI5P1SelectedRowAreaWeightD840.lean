import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1SelectedRowBridgeD838
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1P1SelectedProvenanceD828
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Case1WeightedSectionD830
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1SelectedRowAreaWeightD840 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# selected P1 row-1 area and weight certificates

This fixed-delta module certifies the exact one-dimensional area integral for the zero-based
Piece1 row 1 and interval integrability of the associated weight. It also records that former
strict area premise is false. This module makes no t-fiber, source, image, aggregate, or cap
claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6.
-/

private def d840_intervalIntegralFinPoly {n : Nat} (c : Fin n -> Real)
    (a b : Real) : Real :=
  ∫ x in a..b, sectionSixFirstLowCentralSmallI5P1D828FinPoly c x

private theorem d840_intervalIntegralFinPoly_eq_sum {n : Nat}
    (c : Fin n -> Real) (a b : Real) :
    d840_intervalIntegralFinPoly c a b =
      ∑ i : Fin n, c i *
        (b ^ ((i : Nat) + 1) - a ^ ((i : Nat) + 1)) /
          (((i : Nat) : Real) + 1) := by
  classical
  unfold d840_intervalIntegralFinPoly
  simp only [sectionSixFirstLowCentralSmallI5P1D828FinPoly]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul, integral_pow]
    ring
  · intro i hi
    have hc : Continuous (fun x : Real => c i * x ^ (i : Nat)) := by
      fun_prop
    exact hc.intervalIntegrable (μ := volume) a b

theorem sectionSixFirstLowCentralSmallI5P1D840_p1Row1_area_integral_eq_fraction :
    (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
      sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d) =
      (20901274411415090963021081184957859172730724165545747937088826220595894014305156081 /
        9852343078046258963662659787589504772175787752396093440011826404545659812524851200000000 : Real) := by
  have hpoint : ∀ d : Real,
      sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d =
        sectionSixFirstLowCentralSmallI5P1D828P1SelectedCrossPoly d := by
    intro d
    rw [sectionSixFirstLowCentralSmallI5P1D838_p1Row1_lower_eq_anchor]
    rw [sectionSixFirstLowCentralSmallI5P1D830_p1Case1_area_eq_D828_formula]
    exact (sectionSixFirstLowCentralSmallI5P1D828_p1SelectedVector_eq_formula d).symm
  rw [intervalIntegral.integral_congr (fun d hd => hpoint d)]
  unfold sectionSixFirstLowCentralSmallI5P1D828P1SelectedCrossPoly
  change d840_intervalIntegralFinPoly
      sectionSixFirstLowCentralSmallI5P1D828P1SelectedCoeff
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper = _
  rw [d840_intervalIntegralFinPoly_eq_sum]
  norm_num [sectionSixFirstLowCentralSmallI5P1D828P1SelectedCoeff,
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower,
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
    Fin.sum_univ_succ]

theorem sectionSixFirstLowCentralSmallI5P1D840_p1Row1_area_integral_le_fraction :
    (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
      sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d) ≤
      (20901274411415090963021081184957859172730724165545747937088826220595894014305156081 /
        9852343078046258963662659787589504772175787752396093440011826404545659812524851200000000 : Real) := by
  rw [sectionSixFirstLowCentralSmallI5P1D840_p1Row1_area_integral_eq_fraction]

theorem sectionSixFirstLowCentralSmallI5P1D840_p1Row1_scaled_area_integral_lt :
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor *
      (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
        sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d) <
      (13 / 1000000 : Real) := by
  rw [sectionSixFirstLowCentralSmallI5P1D840_p1Row1_area_integral_eq_fraction]
  exact sectionSixFirstLowCentralSmallI5P1D838_p1Row1_factor_certificate

theorem sectionSixFirstLowCentralSmallI5P1D840_old_strict_area_premise_false :
    ¬ ((∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
        sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d) <
      (20901274411415090963021081184957859172730724165545747937088826220595894014305156081 /
        9852343078046258963662659787589504772175787752396093440011826404545659812524851200000000 : Real)) := by
  intro h
  have heq := sectionSixFirstLowCentralSmallI5P1D840_p1Row1_area_integral_eq_fraction
  linarith

private abbrev A : Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
private abbrev B : Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper
private abbrev F : Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor
private abbrev W : Real -> Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight
private abbrev Formula : Real -> Real :=
  sectionSixFirstLowCentralSmallI5P1D828P1SelectedFormula
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower

private theorem d840_formula_continuous : Continuous Formula := by
  unfold Formula
    sectionSixFirstLowCentralSmallI5P1D828P1SelectedFormula
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
    sectionSixFirstLowCentralSmallI5P1D828QCoeff
  fun_prop

private theorem d840_weight_eq_factor_formula
    {d : Real} (hd : d ∈ Set.uIcc A B) :
    W d = F * Formula d := by
  have hab : A ≤ B :=
    sectionSixFirstLowCentralSmallI5P1D838_p1Row1_endpoints.1.le
  have hd' : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab := by
    simpa [A, B, sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab,
      Set.uIcc_of_le hab] using hd
  rw [show W d = F *
      sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection A d by rfl]
  rw [sectionSixFirstLowCentralSmallI5P1D838_p1Row1_area_eq_weighted hd']
  have hformula :=
    sectionSixFirstLowCentralSmallI5P1D830_p1Case1_area_eq_D828_formula d
  have hanchor :=
    sectionSixFirstLowCentralSmallI5P1D838_p1Row1_lower_eq_anchor
  simpa [A, Formula, hanchor] using congrArg (fun x : Real => F * x) hformula

theorem sectionSixFirstLowCentralSmallI5P1D840_row1_weight_intervalIntegrable :
    IntervalIntegrable
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight volume
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper := by
  have hcontF : Continuous (fun d : Real => F * Formula d) :=
    continuous_const.mul d840_formula_continuous
  have hcont : ContinuousOn W (Set.uIcc A B) := by
    apply ContinuousOn.congr hcontF.continuousOn
    intro d hd
    exact d840_weight_eq_factor_formula hd
  exact hcont.intervalIntegrable


end
end PrimesRestrictedDigits
