import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedKernelRegularityD809
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0RelaxedCapD877
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RelaxedCapD870
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2CapWrapperD888
/-! # SectionSixFirstLowCentralSmallI5P1TargetCapCompositionD889 -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

theorem sectionSixFirstLowCentralSmallI5P1D889_target_integral_lt :
    (∫ x in sectionSixFirstLowCentralSmallI5P1D807Target,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
      ∂(volume : Measure SectionSixP1AffineT)) < (2147 / 500000 : Real) := by
  have htarget := sectionSixFirstLowCentralSmallI5P1D809_native_integral_le_piece_sum
  have h0 :
      (∫ z in sectionSixFirstLowCentralSmallI5P1D808Piece (0 : Fin 3),
        sectionSixFirstLowCentralSmallI5P1D809Kernel z ∂volume) <
        (1313 / 1000000 : Real) := by
    simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using
      sectionSixFirstLowCentralSmallI5P1D877_piece0_integral_lt
  have h1 :
      (∫ z in sectionSixFirstLowCentralSmallI5P1D808Piece (1 : Fin 3),
        sectionSixFirstLowCentralSmallI5P1D809Kernel z ∂volume) <
        (11 / 4000 : Real) := by
    simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using
      sectionSixFirstLowCentralSmallI5P1D870_piece1_integral_lt
  have h2 :
      (∫ z in sectionSixFirstLowCentralSmallI5P1D808Piece (2 : Fin 3),
        sectionSixFirstLowCentralSmallI5P1D809Kernel z ∂volume) <
        (113 / 500000 : Real) := by
    simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using
      sectionSixFirstLowCentralSmallI5P1D888_piece2_integral_lt
  have hsum :
      (∑ i : Fin 3, ∫ z in sectionSixFirstLowCentralSmallI5P1D808Piece i,
        sectionSixFirstLowCentralSmallI5P1D809Kernel z ∂volume) <
        (4289 / 1000000 : Real) := by
    simp [Fin.sum_univ_succ]
    linarith
  exact htarget.trans_lt (hsum.trans (by norm_num))

end
end PrimesRestrictedDigits
