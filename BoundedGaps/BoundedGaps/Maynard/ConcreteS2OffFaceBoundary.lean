import BoundedGaps.Maynard.ConcreteS2OffFaceOscillation
import BoundedGaps.Maynard.ConcreteSimplexOuter

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def normalizedEngelsmaS2OffFaceBoundaryGridStepMass
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexBoundaryGridIndex
      (engelsmaOffFaceFinset m) mesh,
    normalizedMaynardS2OuterSquarefreeTupleShellMass
      (engelsmaOffFaceFinset m) alpha N
      (fun h => engelsmaMaynardRadius
        (alpha * fractionalGridLower mesh j h) N)
      (fun h => engelsmaMaynardRadius
        (alpha * fractionalGridUpper mesh j h) N)

set_option maxRecDepth 7000 in
set_option maxHeartbeats 800000 in
theorem tendsto_normalizedEngelsmaS2OffFaceBoundaryGridStepMass
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple)
    {mesh : ℕ} (hmesh : 0 < mesh) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2OffFaceBoundaryGridStepMass alpha m mesh N)
      atTop (nhds (simplexBoundaryGridVolume
        (engelsmaOffFaceFinset m) mesh)) := by
  let H := engelsmaOffFaceFinset m
  let I := fractionalSimplexBoundaryGridIndex H mesh
  have hlim :=
    tendsto_finite_linear_combination_normalizedMaynardS2OuterSquarefreeTupleShellMass
      halpha I (fun _ => (1 : ℝ))
      (fun j => fractionalGridLower mesh j)
      (fun j => fractionalGridUpper mesh j)
      (fun j hj h => (fractionalGridEndpoints_mem_Icc hmesh
        (Finset.mem_filter.mp hj).1 h).1)
      (fun j hj h => (fractionalGridEndpoints_mem_Icc hmesh
        (Finset.mem_filter.mp hj).1 h).2.1)
      (fun j hj h => (fractionalGridEndpoints_mem_Icc hmesh
        (Finset.mem_filter.mp hj).1 h).2.2)
  simpa [normalizedEngelsmaS2OffFaceBoundaryGridStepMass, I, H,
    simplexBoundaryGridVolume] using hlim

theorem engelsmaOffFaceFinset_nonempty
    (m : BoundedGaps.engelsmaTuple) :
    (engelsmaOffFaceFinset m).Nonempty := by
  have hcard : (engelsmaOffFaceFinset m).card = 104 := by
    unfold engelsmaOffFaceFinset
    rw [Finset.card_erase_of_mem m.property,
      BoundedGaps.engelsmaTuple_card]
  exact Finset.nonempty_iff_ne_empty.mpr (by
    intro h
    rw [h] at hcard
    simp at hcard)

theorem tendsto_simplexBoundaryGridVolume_engelsmaS2OffFace_zero
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun mesh : ℕ => simplexBoundaryGridVolume
        (engelsmaOffFaceFinset m) mesh) atTop (nhds 0) := by
  obtain ⟨h, hh⟩ := engelsmaOffFaceFinset_nonempty m
  exact tendsto_simplexBoundaryGridVolume_zero
    (⟨h, hh⟩ : engelsmaOffFaceFinset m)

end BoundedGaps.Maynard
