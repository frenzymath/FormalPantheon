import BoundedGaps.Maynard.ConcreteS2PolynomialBound
import BoundedGaps.Maynard.MaynardS2OuterFaceBox

noncomputable section

namespace BoundedGaps.Maynard

open MeasureTheory
open scoped BigOperators

set_option maxRecDepth 5000 in
theorem engelsmaS2CoordinateFiberGoodOuterMoment_le_explicitFaceBox
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple) (hR : 1 < R) :
    engelsmaS2CoordinateFiberGoodOuterMoment R D m ≤
      (Real.log R * smallKCandidateBound) ^ 2 *
        ∏ _h ∈ Finset.univ.erase m,
          maynardS2OuterSquarefreeMean (primorial D) R := by
  apply engelsmaS2CoordinateFiberGoodOuterMoment_le_faceBox_mul m
    (sq_nonneg _)
  intro r hr
  have hrData := Finset.mem_filter.mp hr
  exact
    sq_log_mul_engelsmaS2CoordinateFiberPolynomialTest_intervalIntegral_le
      m (isMaynardDivisorTuple_of_mem_support hrData.1) hR hrData.2.2

end BoundedGaps.Maynard
