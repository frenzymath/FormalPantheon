import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatterns
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5OuterIntegrability
import Mathlib.Tactic.Measurability
/-! # SectionSixFirstLowCentralSmallI5PairPatternIntegralAggregate -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-
Fixed-delta structural aggregation for the four strict pair-side patterns. The target is the
outer carrier, and the final inequality is an overcover estimate; no numerical payload
estimate is used here.
-/
def sectionSixFirstLowCentralSmallI5PairPatternTarget (b : Fin 4) :
    Set (((Real × Real) × Real) × Real) :=
  sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000 : Real) ∩
    sectionSixFirstLowCentralSmallI5PairPattern b

theorem sectionSixFirstLowCentralSmallI5PairPatternTarget_measurable
    (b : Fin 4) :
    MeasurableSet (sectionSixFirstLowCentralSmallI5PairPatternTarget b) := by
  unfold sectionSixFirstLowCentralSmallI5PairPatternTarget
    sectionSixFirstLowCentralSmallI5PairPattern
  exact sectionSixFirstLowCentralSmallUniformOuterRegion_delta5_measurable.inter
    (by measurability)

theorem sectionSixFirstLowCentralSmallI5PairPatternTarget_integrable
    (b : Fin 4) :
    IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixFirstLowCentralSmallI5PairPatternTarget b) := by
  apply sectionSixFirstLowCentralSmallUniformOuterKernel_integrable.mono_set
  intro x hx
  exact hx.1

theorem sectionSixFirstLowCentralSmallI5PairPatternTarget_nonneg
    (b : Fin 4) :
    ∀ x ∈ sectionSixFirstLowCentralSmallI5PairPatternTarget b,
      0 <= sectionSixFirstLowCentralSmallQuadrupleKernel x := by
  intro x hx
  exact sectionSixFirstLowCentralSmallUniformOuterKernel_nonneg hx.1

theorem sectionSixFirstLowCentralSmallI5PairPatternTarget_cover :
    sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000 : Real) ⊆
      ⋃ b : Fin 4, sectionSixFirstLowCentralSmallI5PairPatternTarget b := by
  intro x hx
  rcases Set.mem_iUnion.1
      (sectionSixFirstLowCentralSmallI5_pairPattern_cover hx) with ⟨b, hb⟩
  exact Set.mem_iUnion.2 ⟨b, ⟨hx, hb⟩⟩

theorem sectionSixFirstLowCentralSmallI5PairPatternTarget_setIntegral_le_sum :
    (∫ x in sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real),
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) ≤
      ∑ b : Fin 4,
        ∫ x in sectionSixFirstLowCentralSmallI5PairPatternTarget b,
          sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume := by
  have h := setIntegral_le_finset_setIntegral_of_cover
    (μ := volume) (cells := (Finset.univ : Finset (Fin 4)))
    (target := sectionSixFirstLowCentralSmallUniformOuterRegion
      (1 / 1000000 : Real))
    (cell := sectionSixFirstLowCentralSmallI5PairPatternTarget)
    (f := sectionSixFirstLowCentralSmallQuadrupleKernel)
    sectionSixFirstLowCentralSmallUniformOuterRegion_delta5_measurable
    (fun b hb => sectionSixFirstLowCentralSmallI5PairPatternTarget_measurable b)
    (fun b hb => sectionSixFirstLowCentralSmallI5PairPatternTarget_integrable b)
    (fun b hb => sectionSixFirstLowCentralSmallI5PairPatternTarget_nonneg b)
    (by
      intro x hx
      rcases Set.mem_iUnion.1
          (sectionSixFirstLowCentralSmallI5PairPatternTarget_cover hx) with
        ⟨b, hb⟩
      exact Set.mem_iUnion.2 ⟨b, Set.mem_iUnion.2
        ⟨Finset.mem_univ b, hb⟩⟩)
  simpa using h

end

end PrimesRestrictedDigits
