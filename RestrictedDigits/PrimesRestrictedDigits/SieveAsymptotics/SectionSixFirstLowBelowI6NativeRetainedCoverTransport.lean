import PrimesRestrictedDigits.BasicEstimates.FiniteRationalSubdivision
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6GenericNestedBoxCell

/-!
# Native transport of a retained-leaf cover

This is a set-theoretic coordinate adapter. It transports the generic `Fin 4 -> Real`
retained-leaf cover to the native left-associated I6 tuple type. It makes no measure, payload,
replay, or numerical claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem i6D689_native_target_subset_retainedLeaves
    {alpha : Type*}
    (constraints : List (RationalAffineConstraint 4))
    (payloadValid : RationalBox 4 -> alpha -> Bool)
    (box : RationalBox 4)
    (tree : RationalSubdivision 4 alpha)
    (target : Set (((Real × Real) × Real) × Real))
    (hvalid : tree.coverValid constraints payloadValid box = true)
    (hconstraints :
      ∀ x ∈ target, ∀ constraint ∈ constraints,
        constraint.holds (i6D686Coordinates x))
    (hroot : target ⊆ i6D688NestedBoxCell box) :
    target ⊆ ⋃ i : Fin (tree.retainedLeaves box).length,
        i6D688NestedBoxCell ((tree.retainedLeaves box).get i).1 := by
  let targetCoord : Set (AffinePoint 4) := i6D686Coordinates '' target
  have hconstraintsCoord :
      ∀ z ∈ targetCoord, ∀ constraint ∈ constraints,
        constraint.holds z := by
    intro z hz constraint hc
    rcases hz with ⟨x, hx, rfl⟩
    exact hconstraints x hx constraint hc
  have hrootCoord : targetCoord ⊆ box.region := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact i6D688_mem_nestedBoxCell_iff.mp (hroot hx)
  have hcoord := RationalSubdivision.target_subset_retainedLeaves
    constraints payloadValid box tree targetCoord hvalid
      hconstraintsCoord hrootCoord
  intro x hx
  have hxcoord : i6D686Coordinates x ∈ targetCoord := ⟨x, hx, rfl⟩
  have hcover := hcoord hxcoord
  rcases Set.mem_iUnion.1 hcover with ⟨i, hi⟩
  apply Set.mem_iUnion.2
  refine ⟨i, ?_⟩
  exact i6D688_mem_nestedBoxCell_iff.mpr hi

end

end PrimesRestrictedDigits
