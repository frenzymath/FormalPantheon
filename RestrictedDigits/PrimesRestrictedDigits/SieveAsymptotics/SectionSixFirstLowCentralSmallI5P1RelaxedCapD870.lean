import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowAggregateD847
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1GenericRowHIterD857
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1ExactRowFiberSumD869
/-! # SectionSixFirstLowCentralSmallI5P1RelaxedCapD870 -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# transformed Piece1 relaxed-cap composition

This module composes the overlap-safe row-cover inequality, the per-row hIter identity, and
the exact row-fiber sum certificate. It makes no source, image, Jacobian, row-additivity, or
full-I5 claim.
-/

theorem sectionSixFirstLowCentralSmallI5P1D870_piece1_integral_lt :
    (∫ x in sectionSixFirstLowCentralSmallI5P1D807Piece1,
      sectionSixFirstLowCentralSmallI5P1D809Kernel x
      ∂(volume : Measure SectionSixP1AffineT)) < (11 / 4000 : Real) := by
  calc
    (∫ x in sectionSixFirstLowCentralSmallI5P1D807Piece1,
        sectionSixFirstLowCentralSmallI5P1D809Kernel x
        ∂(volume : Measure SectionSixP1AffineT)) ≤
        ∑ i : Fin 256,
          ∫ x in sectionSixFirstLowCentralSmallI5P1D846P1RowSet i,
            sectionSixFirstLowCentralSmallI5P1D809Kernel x
            ∂(volume : Measure SectionSixP1AffineT) :=
      sectionSixFirstLowCentralSmallI5P1D847_piece1_integral_le_row_sum
    _ = ∑ i : Fin 256,
        ∫ d in
          sectionSixFirstLowCentralSmallI5P1D849RowLower i..
          sectionSixFirstLowCentralSmallI5P1D849RowUpper i,
          sectionSixFirstLowCentralSmallI5P1D852P1RowFiber i d := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sectionSixFirstLowCentralSmallI5P1D857_p1Row_hIter]
    _ < (11 / 4000 : Real) :=
      sectionSixFirstLowCentralSmallI5P1D869_p1RowFiber_sum_lt


end
end PrimesRestrictedDigits
