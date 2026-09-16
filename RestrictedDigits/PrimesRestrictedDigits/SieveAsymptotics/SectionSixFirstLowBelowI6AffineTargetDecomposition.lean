import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6AffineSideWitness
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6RationalBoxAdapter

/-!
# Finite affine target decomposition for the fixed I6 region

This module is the set-theoretic adapter between pointwise affine side witnesses and per-label
target interface. It proves only the indexed native/coordinate over-covers and the per-label
constraint premises.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

abbrev i6D691Label := Bool × (Fin 3 × (Fin 5 → Bool))

def i6D691Constraints (label : i6D691Label) :
    List (RationalAffineConstraint 4) :=
  i6D690ConstraintList label.1 label.2.1 label.2.2

def i6D691NativeTarget (label : i6D691Label) :
    Set (((Real × Real) × Real) × Real) :=
  {x |
    x ∈ sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real) ∧
    i6D690Holds label.1 label.2.1 label.2.2
      (i6D686Coordinates x)}

def i6D691AffineTarget (label : i6D691Label) :
    Set (AffinePoint 4) :=
  i6D686Coordinates '' i6D691NativeTarget label

theorem i6D691_exactRegion_subset_iUnion_nativeTarget :
    sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real) ⊆
      ⋃ label : i6D691Label, i6D691NativeTarget label := by
  intro x hx
  obtain ⟨rho, b, sigma, hholds⟩ :=
    i6D690_exists_affine_side_witness hx
  refine Set.mem_iUnion.2 ⟨(rho, (b, sigma)), ?_⟩
  exact ⟨hx, hholds⟩

theorem i6D691_exactRegion_image_subset_iUnion_affineTarget :
    i6D686Coordinates ''
        sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real) ⊆
      ⋃ label : i6D691Label, i6D691AffineTarget label := by
  rintro z ⟨x, hx, rfl⟩
  have hnative := i6D691_exactRegion_subset_iUnion_nativeTarget hx
  rcases Set.mem_iUnion.1 hnative with ⟨label, hlabel⟩
  refine Set.mem_iUnion.2 ⟨label, ?_⟩
  exact ⟨x, hlabel, rfl⟩

theorem i6D691_nativeTarget_hconstraints
    (label : i6D691Label) {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D691NativeTarget label) :
    ∀ c ∈ i6D691Constraints label,
      c.holds (i6D686Coordinates x) := by
  exact (i6D690Holds_iff_forall_mem label.1 label.2.1 label.2.2
    (i6D686Coordinates x)).1 hx.2

theorem i6D691_affineTarget_constraints
    (label : i6D691Label) {z : AffinePoint 4}
    (hz : z ∈ i6D691AffineTarget label) :
    ∀ c ∈ i6D691Constraints label, c.holds z := by
  rcases hz with ⟨x, hx, rfl⟩
  exact i6D691_nativeTarget_hconstraints label hx

end

end PrimesRestrictedDigits
