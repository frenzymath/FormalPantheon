import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0RowAggregateD872
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0RowCompositionD875
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0RowMajorantSumD876
/-! # SectionSixFirstLowCentralSmallI5P1Piece0RelaxedCapD877 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
# transformed Piece0 relaxed-cap composition

This module composes the overlap-safe row cover, the per-row majorant inequality, and the
exact row-majorant sum. It makes no source, image, Jacobian, partition, or full-I5 claim.
-/

theorem sectionSixFirstLowCentralSmallI5P1D877_piece0_integral_lt :
    (∫ x in sectionSixFirstLowCentralSmallI5P1D807Piece0,
      sectionSixFirstLowCentralSmallI5P1D809Kernel x
      ∂(volume : Measure SectionSixP1AffineT)) <
      (1313 / 1000000 : Real) := by
  calc
    (∫ x in sectionSixFirstLowCentralSmallI5P1D807Piece0,
        sectionSixFirstLowCentralSmallI5P1D809Kernel x
        ∂(volume : Measure SectionSixP1AffineT)) ≤
        ∑ i : Fin 256,
          ∫ x in sectionSixFirstLowCentralSmallI5P1D871P0RowSet i,
            sectionSixFirstLowCentralSmallI5P1D809Kernel x
            ∂(volume : Measure SectionSixP1AffineT) :=
      sectionSixFirstLowCentralSmallI5P1D872_piece0_integral_le_row_sum
    _ ≤ ∑ i : Fin 256,
        ∫ d in
          sectionSixFirstLowCentralSmallI5P1D871P0RowLower i..
          sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i,
          sectionSixFirstLowCentralSmallI5P1D875P0RowMajorant i d := by
      apply Finset.sum_le_sum
      intro i hi
      exact sectionSixFirstLowCentralSmallI5P1D875_p0Row_setIntegral_le_majorant i
    _ < (1313 / 1000000 : Real) :=
      sectionSixFirstLowCentralSmallI5P1D876_p0RowMajorant_sum_lt

end

end PrimesRestrictedDigits
