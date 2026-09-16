import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2CapCompositionD885
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2RowRegularityD886
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2OuterRegularityD887
/-! # SectionSixFirstLowCentralSmallI5P1Piece2CapWrapperD888 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

theorem sectionSixFirstLowCentralSmallI5P1D888_piece2_integral_lt :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D807Piece2,
      sectionSixFirstLowCentralSmallI5P1D809Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) <
      (113 / 500000 : Real) := by
  exact sectionSixFirstLowCentralSmallI5P1D885_piece2_integral_lt
    sectionSixFirstLowCentralSmallI5P1D887_piece2_outerMajorant_intervalIntegrable
    (fun i =>
      sectionSixFirstLowCentralSmallI5P1D886_p2AnchoredRowMajorant_intervalIntegrable i)

end
end PrimesRestrictedDigits
