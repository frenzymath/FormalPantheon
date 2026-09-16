import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1SelectedRowBridgeD838
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1SelectedRowAreaWeightD840
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
/-! # SectionSixFirstLowCentralSmallI5P1CorrectedKernelAdapterD842 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# Conditional P1 kernel integral bound

The scaled area bound combines with the iterated integral identity, the
fiber bound, and integrability of the fibers and weight.
-/

theorem sectionSixFirstLowCentralSmallI5P1D842_p1Row1_kernel_to_scaled_area
    (hIter :
      (∫ z in sectionSixFirstLowCentralSmallI5P1D838P1Row1Set,
        sectionSixFirstLowCentralSmallI5P1D809Kernel z
        ∂(volume : Measure SectionSixP1AffineT)) =
        ∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber d)
    (hFiber :
      ∀ d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab,
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber d ≤
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight d)
    (hFiberInt :
      IntervalIntegrable
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber volume
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper)
    (hWeightInt :
      IntervalIntegrable
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight volume
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D838P1Row1Set,
      sectionSixFirstLowCentralSmallI5P1D809Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) <
      (13 / 1000000 : Real) := by
  rw [hIter]
  have hab :
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower ≤
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper :=
    sectionSixFirstLowCentralSmallI5P1D838_p1Row1_endpoints.1.le
  have hmono := intervalIntegral.integral_mono_on
    (μ := (volume : Measure Real)) hab hFiberInt hWeightInt hFiber
  have hweight :
      (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight d) =
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor *
          (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
              sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
            sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
              sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d) := by
    unfold sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight
    rw [intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro d hd
    rw [sectionSixFirstLowCentralSmallI5P1D838_p1Row1_area_eq_weighted]
    simpa [sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab,
      Set.uIcc_of_le hab] using hd
  calc
    (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber d) ≤
        ∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight d := hmono
    _ = sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor *
        (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
            sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
          sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
            sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d) := hweight
    _ < (13 / 1000000 : Real) :=
      sectionSixFirstLowCentralSmallI5P1D840_p1Row1_scaled_area_integral_lt


end
end PrimesRestrictedDigits
