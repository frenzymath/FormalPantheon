import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatternIntegralAggregate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P3TightBox
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The bookkeeping bridge substitutes the strict whole-P3 bound into the Fin 4 aggregate. The P0,
P1, and P2 summands remain symbolic; no whole-I5 or source-region claim is made.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralSmallI5PairPatternTarget_setIntegral_le_p3_tight_substituted :
    (∫ x in sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real),
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) ≤
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 0,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 1,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 2,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
      (1 / 100000 : Real) := by
  have h3 :
      (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 3,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) <
        (1 / 100000 : Real) := by
    simpa [sectionSixFirstLowCentralSmallI5PairPatternTarget,
      sectionSixFirstLowCentralSmallI5P3WideTarget,
      MeasureTheory.Measure.volume_eq_prod] using
      sectionSixFirstLowCentralSmallI5P3TightTarget_integral_lt_oneHundredThousandth
  have hagg :=
    sectionSixFirstLowCentralSmallI5PairPatternTarget_setIntegral_le_sum
  have hsum :
      (∑ b : Fin 4,
        ∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget b,
          sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) =
        (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 0,
          sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
        (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 1,
          sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
        (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 2,
          sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) +
        (∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget 3,
          sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) := by
    norm_num [Fin.sum_univ_succ]
    have hfin : (Fin.succ (2 : Fin 3) : Fin 4) = (3 : Fin 4) := by decide
    rw [hfin]
    ring
  rw [hsum] at hagg
  linarith

end
end PrimesRestrictedDigits
