import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1GenericRowOuterComparisonD853
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1WeightedSectionAreaBridgeD832
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowEndpointOrderD850
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1RowWeightIntegrabilityD854 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/--
# generic P1 row area and weight integrability

This module discharges the regularity premises. It proves continuity of the area formula and
interval integrability on each closed row; it makes no numerical, source, image, aggregate, or
cap claim.
-/

theorem sectionSixFirstLowCentralSmallI5P1D854_p1Case1Area_continuous (a : Real) :
    Continuous (fun d =>
      sectionSixFirstLowCentralSmallI5P1D830P1Case1Area a d) := by
  have heq : (fun d : Real =>
      sectionSixFirstLowCentralSmallI5P1D830P1Case1Area a d) =
      (fun d =>
        (sectionSixFirstLowCentralSmallI5P1D814Q4Primitive a
            (sectionSixFirstLowCentralSmallI5P1D807L d / 2)) ^ 2 / 2 +
        ∑ i ∈ Finset.range 5,
          (∑ j ∈ Finset.range 5,
            (∑ k ∈ Finset.range (j + 2),
              (sectionSixFirstLowCentralSmallI5P1D828QCoeff a i *
                  sectionSixFirstLowCentralSmallI5P1D828QCoeff a j *
                (j + 1 : Nat).choose k * (-1 : Real) ^ k /
                  ((j + 1 : Real) * (i + k + 1 : Real))) *
                sectionSixFirstLowCentralSmallI5P1D807L d ^ (j + 1 - k) *
                  (sectionSixFirstLowCentralSmallI5P1D807H d ^ (i + k + 1) -
                    (sectionSixFirstLowCentralSmallI5P1D807L d / 2) ^
                      (i + k + 1))))) := by
    funext d
    unfold sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
    rw [sectionSixFirstLowCentralSmallI5P1D830_p1Case1_upper_integral_eq_sum]
  rw [heq]
  have hp : Continuous (sectionSixFirstLowCentralSmallI5P1D814Q4Primitive a) := by
    unfold sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
    fun_prop
  unfold sectionSixFirstLowCentralSmallI5P1D807L
    sectionSixFirstLowCentralSmallI5P1D807H
  fun_prop

private theorem row_lower_pos (i : Fin 256) :
    0 < sectionSixFirstLowCentralSmallI5P1D849RowLower i := by
  have hds : 0 < sectionSixFirstLowCentralSmallI5P1D807Ds := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, _, _, hds, _, _⟩
    rw [hds]
    norm_num
  exact lt_of_lt_of_le hds
    (sectionSixFirstLowCentralSmallI5P1D850_ds_le_row_lower i)

private theorem row_lower_upper (i : Fin 256) :
    sectionSixFirstLowCentralSmallI5P1D849RowLower i ≤
      sectionSixFirstLowCentralSmallI5P1D849RowUpper i :=
  sectionSixFirstLowCentralSmallI5P1D850_row_lower_le_upper i

theorem sectionSixFirstLowCentralSmallI5P1D854_p1Row_area_intervalIntegrable (i : Fin 256) :
    IntervalIntegrable (fun d : Real =>
      sectionSixFirstLowCentralSmallI5P1D853P1RowFactor i * sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
        (sectionSixFirstLowCentralSmallI5P1D849RowLower i) d) volume
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i) := by
  exact (continuous_const.mul (sectionSixFirstLowCentralSmallI5P1D854_p1Case1Area_continuous
    (sectionSixFirstLowCentralSmallI5P1D849RowLower i))).intervalIntegrable _ _

theorem sectionSixFirstLowCentralSmallI5P1D854_p1Row_weight_intervalIntegrable (i : Fin 256) :
    IntervalIntegrable
      (sectionSixFirstLowCentralSmallI5P1D853P1RowWeight i) volume
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i) := by
  change IntervalIntegrable (fun d : Real =>
      sectionSixFirstLowCentralSmallI5P1D853P1RowFactor i *
        sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i) d) volume
    (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
    (sectionSixFirstLowCentralSmallI5P1D849RowUpper i)
  have harea := sectionSixFirstLowCentralSmallI5P1D854_p1Row_area_intervalIntegrable i
  apply harea.congr
  intro d hd
  have hdi : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i) :=
    by
      simpa [Set.uIcc_of_le (row_lower_upper i)] using
        (Set.uIoc_subset_uIcc hd)
  have hglobal : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr := by
    exact ⟨(sectionSixFirstLowCentralSmallI5P1D850_ds_le_row_lower i).trans hdi.1,
      hdi.2.trans (sectionSixFirstLowCentralSmallI5P1D850_row_upper_le_dr i)⟩
  have hEq := sectionSixFirstLowCentralSmallI5P1D832_p1Case1_weightedSection_eq_area
    (a := sectionSixFirstLowCentralSmallI5P1D849RowLower i) (d := d)
    (ne_of_gt (row_lower_pos i)) hglobal
  exact congrArg (fun x : Real => sectionSixFirstLowCentralSmallI5P1D853P1RowFactor i * x) hEq.symm


end
end PrimesRestrictedDigits
