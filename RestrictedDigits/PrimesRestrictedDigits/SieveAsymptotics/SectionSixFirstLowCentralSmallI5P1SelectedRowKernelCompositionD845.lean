/-
premise-free selected closed-row composition. This theorem is limited to Piece1 row 1 and
inherits, without broadening, the facts.
-/
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1CorrectedKernelAdapterD842
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1SelectedRowHIterD839
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1SelectedRowFiberIntegrabilityD843
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1SelectedRowHFiberD844
/-! # SectionSixFirstLowCentralSmallI5P1SelectedRowKernelCompositionD845 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/- The first premise-free composition of the selected row adapters. -/
theorem sectionSixFirstLowCentralSmallI5P1D845_p1Row1_kernel_to_scaled_area :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D838P1Row1Set,
      sectionSixFirstLowCentralSmallI5P1D809Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) <
      (13 / 1000000 : Real) := by
  apply sectionSixFirstLowCentralSmallI5P1D842_p1Row1_kernel_to_scaled_area
  · exact sectionSixFirstLowCentralSmallI5P1D838_p1Row1_hIter_discharge
  · intro d hd
    exact sectionSixFirstLowCentralSmallI5P1D844_p1Row1_hFiber hd
  · exact sectionSixFirstLowCentralSmallI5P1D843_p1Row1_hFiberInt
  · exact sectionSixFirstLowCentralSmallI5P1D840_row1_weight_intervalIntegrable


end
end PrimesRestrictedDigits
