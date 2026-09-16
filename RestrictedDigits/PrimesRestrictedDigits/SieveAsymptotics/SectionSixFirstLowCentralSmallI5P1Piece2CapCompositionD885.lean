import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2OuterCompositionD881
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2AnchoredMeshD883
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2OuterToAnchoredMeshD884
/-! # SectionSixFirstLowCentralSmallI5P1Piece2CapCompositionD885 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/- Combining the conditional fiber and outer integral bounds. -/
theorem sectionSixFirstLowCentralSmallI5P1D885_piece2_integral_lt
    (hMajorantInt :
      IntervalIntegrable
        sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant
        (volume : Measure Real)
        sectionSixFirstLowCentralSmallI5P1D807Dr
        sectionSixFirstLowCentralSmallI5P1D807D1)
    (hRowInt :
      ∀ i : Fin 128,
        IntervalIntegrable
          (fun d =>
            sectionSixFirstLowCentralSmallI5P1D883P2AnchoredRowMajorant i d)
          (volume : Measure Real)
          (sectionSixFirstLowCentralSmallI5P1D807Dr +
            (i : Real) *
              (sectionSixFirstLowCentralSmallI5P1D807D1 -
                sectionSixFirstLowCentralSmallI5P1D807Dr) / 128)
          (sectionSixFirstLowCentralSmallI5P1D807Dr +
            (((i : Nat) + 1 : Nat) : Real) *
              (sectionSixFirstLowCentralSmallI5P1D807D1 -
                sectionSixFirstLowCentralSmallI5P1D807Dr) / 128)) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D807Piece2,
      sectionSixFirstLowCentralSmallI5P1D809Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) <
      (113 / 500000 : Real) := by
  calc
    (∫ z in sectionSixFirstLowCentralSmallI5P1D807Piece2,
        sectionSixFirstLowCentralSmallI5P1D809Kernel z
        ∂(volume : Measure SectionSixP1AffineT)) ≤
        ∫ d in sectionSixFirstLowCentralSmallI5P1D807Dr..
          sectionSixFirstLowCentralSmallI5P1D807D1,
          sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant d :=
      sectionSixFirstLowCentralSmallI5P1D881_piece2_integral_le_outerMajorant
        hMajorantInt
    _ ≤ ∑ i : Fin 128,
        ∫ d in
          (sectionSixFirstLowCentralSmallI5P1D807Dr +
            (i : Real) *
              (sectionSixFirstLowCentralSmallI5P1D807D1 -
                sectionSixFirstLowCentralSmallI5P1D807Dr) / 128)..
          (sectionSixFirstLowCentralSmallI5P1D807Dr +
            (((i : Nat) + 1 : Nat) : Real) *
              (sectionSixFirstLowCentralSmallI5P1D807D1 -
                sectionSixFirstLowCentralSmallI5P1D807Dr) / 128),
          sectionSixFirstLowCentralSmallI5P1D883P2AnchoredRowMajorant i d :=
      sectionSixFirstLowCentralSmallI5P1D884_piece2_outerMajorant_le_anchoredMesh
        hMajorantInt hRowInt
    _ < (113 / 500000 : Real) :=
      sectionSixFirstLowCentralSmallI5P1D883_p2AnchoredRowMajorant_sum_lt

end
end PrimesRestrictedDigits
