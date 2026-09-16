import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0AmbientIntegrability
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0FiberAmbientUnion
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum

/-!
# P0 source slice to ambient finite integral cover

The fixed-delta P0 source slice is covered one-way by the three ambient closed cells. The
compact carrier supplies the kernel sign on the overcover, allowing the finite set-integral
comparison without any source equality or numerical cap claim.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P0QuadrupleSource :
    Set ((((Real × Real) × Real) × Real)) :=
  sectionSixFirstLowCentralSmallUniformOuterRegion
      (1 / 1000000 : Real) ∩
    sectionSixFirstLowCentralSmallI5PairPattern 0

theorem sectionSixFirstLowCentralSmallI5P0QuadrupleSource_measurableSet :
    MeasurableSet sectionSixFirstLowCentralSmallI5P0QuadrupleSource := by
  unfold sectionSixFirstLowCentralSmallI5P0QuadrupleSource
  unfold sectionSixFirstLowCentralSmallUniformOuterRegion
    sectionSixFirstLowCentralSmallI5PairPattern
  measurability

theorem sectionSixFirstLowCentralSmallI5P0AmbientCell_kernel_nonneg
    (b : Fin 3) {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P0AmbientCell b) :
    0 <= sectionSixFirstLowCentralSmallQuadrupleKernel x := by
  have hcarrier := sectionSixFirstLowCentralSmallI5P0AmbientCell_subset_compactCarrier b hx
  have hcap : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 ≤ 1 := hcarrier.2
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have htPos : 0 < x.2 := hgap.trans_le hcarrier.1.2.1
  have huPos : 0 < x.1.1.1 := hgap.trans_le hcarrier.1.1.1.1.1
  have hvPos : 0 < x.1.1.2 := hgap.trans_le hcarrier.1.1.1.2.1
  have hwPos : 0 < x.1.2 := hgap.trans_le hcarrier.1.1.2.1
  have harg : 1 ≤
      (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
    rw [le_div_iff₀ htPos]
    linarith
  have hbuch : 0 ≤ buchstabFunction
      ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) := by
    have h := (buchstabFunction_mem_Icc harg).1
    linarith
  have hden : 0 < x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    exact mul_pos (mul_pos (mul_pos huPos hvPos) hwPos) (pow_pos htPos 2)
  simp only [sectionSixFirstLowCentralSmallQuadrupleKernel]
  exact div_nonneg hbuch hden.le

theorem sectionSixFirstLowCentralSmallI5P0QuadrupleSource_subset_ambientCell_iUnion :
    sectionSixFirstLowCentralSmallI5P0QuadrupleSource ⊆
      ⋃ b : Fin 3, sectionSixFirstLowCentralSmallI5P0AmbientCell b := by
  intro x hx
  change (((x.1.1), x.1.2), x.2) ∈
      sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real) ∧
    (((x.1.1), x.1.2), x.2) ∈
      sectionSixFirstLowCentralSmallI5PairPattern 0 at hx
  have hfiber : x.2 ∈ sectionSixFirstLowCentralSmallI5P0Fiber
      x.1.1.1 x.1.1.2 x.1.2 := hx
  exact sectionSixFirstLowCentralSmallI5P0Fiber_mem_ambientCell_iUnion hfiber

theorem sectionSixFirstLowCentralSmallI5P0QuadrupleSource_setIntegral_le_ambientCell_sum :
    (∫ x in sectionSixFirstLowCentralSmallI5P0QuadrupleSource,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) <=
      ∑ b : Fin 3,
        ∫ x in sectionSixFirstLowCentralSmallI5P0AmbientCell b,
          sectionSixFirstLowCentralSmallQuadrupleKernel x
            ∂(volume.prod volume) := by
  apply setIntegral_le_finset_setIntegral_of_cover
    (volume.prod volume) (Finset.univ : Finset (Fin 3))
    sectionSixFirstLowCentralSmallI5P0QuadrupleSource
    sectionSixFirstLowCentralSmallI5P0AmbientCell
    sectionSixFirstLowCentralSmallQuadrupleKernel
  · exact sectionSixFirstLowCentralSmallI5P0QuadrupleSource_measurableSet
  · intro b hb
    exact sectionSixFirstLowCentralSmallI5P0AmbientCell_measurableSet b
  · intro b hb
    exact sectionSixFirstLowCentralSmallI5P0AmbientCell_integrable b
  · intro b hb x hx
    exact sectionSixFirstLowCentralSmallI5P0AmbientCell_kernel_nonneg b hx
  · intro x hx
    have h := sectionSixFirstLowCentralSmallI5P0QuadrupleSource_subset_ambientCell_iUnion hx
    rcases Set.mem_iUnion.mp h with ⟨b, hb⟩
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    exact Set.mem_iUnion.mpr ⟨Finset.mem_univ b, hb⟩

end

end PrimesRestrictedDigits
