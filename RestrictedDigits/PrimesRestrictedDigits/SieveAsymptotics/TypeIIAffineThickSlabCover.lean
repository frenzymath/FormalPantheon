import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineThickSlabCount
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIProjectedZeroNormal
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRemainderCount

/-!
# Projected thick-slab covers

This file transfers a full affine boundary witness through canonical sum-one completion to the
thick projected grid slabs. Degenerate projected normals are excluded by the witness statement
and are handled by the zero-normal classification.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A nonzero projected normal sends one full slab witness in a doubled cell
to the corresponding thick projected anchor slab.  The `bound` here is the
full-coordinate bound; the projected bound appears only in the conclusion. -/
theorem mem_typeIIAffineThickSlabAnchors_of_projected_witness
    {k : Nat} {delta gamma : Real}
    {normal : Fin (k + 1) -> Real} {bound : Real}
    (hdelta : 0 < delta)
    (hprojected : typeIIProjectedAffineNormal normal ≠ 0)
    {anchor : Fin k -> Nat} {x : Fin k -> Real}
    (hgrid : anchor ∈ typeIINaturalCubeGrid k delta)
    (hxCube : x ∈ typeIIDoubledProjectedCube delta anchor)
    (hxSlab : |typeIIAffineValue normal
        (completeProjectedLogTuple x) - bound| <= gamma) :
    anchor ∈ typeIIAffineThickSlabAnchors delta gamma
      (typeIIProjectedAffineNormal normal)
      (typeIIProjectedAffineBound normal bound) := by
  have hdistance :=
    abs_typeIIAffineValue_scaled_sub_le_of_mem_doubledProjectedCube
      hdelta.le (normal := typeIIProjectedAffineNormal normal) hxCube
  have hrewrite :
      typeIIAffineValue (typeIIProjectedAffineNormal normal) x -
          typeIIProjectedAffineBound normal bound =
        typeIIAffineValue normal (completeProjectedLogTuple x) - bound := by
    rw [typeIIAffineValue_completeProjectedLogTuple]
    simp only [typeIIProjectedAffineBound]
    ring_nf
  have hanchorSlab :
      |typeIIAffineValue (typeIIProjectedAffineNormal normal)
          (scaledNaturalCubeAnchor delta anchor) -
          typeIIProjectedAffineBound normal bound| <=
        gamma + 2 * delta *
          typeIIAffineNormalMass (typeIIProjectedAffineNormal normal) := by
    calc
      |typeIIAffineValue (typeIIProjectedAffineNormal normal)
          (scaledNaturalCubeAnchor delta anchor) -
          typeIIProjectedAffineBound normal bound| <=
          |typeIIAffineValue (typeIIProjectedAffineNormal normal)
              (scaledNaturalCubeAnchor delta anchor) -
            typeIIAffineValue (typeIIProjectedAffineNormal normal) x| +
          |typeIIAffineValue (typeIIProjectedAffineNormal normal) x -
            typeIIProjectedAffineBound normal bound| :=
        abs_sub_le _ _ _
      _ <= 2 * delta *
            typeIIAffineNormalMass (typeIIProjectedAffineNormal normal) +
          gamma := by
        apply add_le_add hdistance
        simpa [hrewrite] using hxSlab
      _ = gamma + 2 * delta *
          typeIIAffineNormalMass (typeIIProjectedAffineNormal normal) := by
        ring
  exact mem_typeIIAffineThickSlabAnchors.mpr
    ⟨hgrid, hprojected, hanchorSlab⟩

/-- The finite union of thick slabs attached to all constraints of a full
affine presentation.  Each constituent thick slab itself excludes a zero
projected normal. -/
noncomputable def typeIIAffinePresentationThickSlabAnchors
    {k : Nat} {region : Set (Fin (k + 1) -> Real)}
    (delta gamma : Real)
    (presentation : TypeIIAffineHalfspacePresentation region) :
    Finset (Fin k -> Nat) := by
  classical
  exact Finset.univ.biUnion fun j =>
    typeIIAffineThickSlabAnchors delta gamma
      (typeIIProjectedAffineNormal (presentation.normal j))
      (typeIIProjectedAffineBound (presentation.normal j)
        (presentation.bound j))

@[simp] theorem mem_typeIIAffinePresentationThickSlabAnchors
    {k : Nat} {delta gamma : Real}
    {region : Set (Fin (k + 1) -> Real)}
    {presentation : TypeIIAffineHalfspacePresentation region}
    {anchor : Fin k -> Nat} :
    anchor ∈ typeIIAffinePresentationThickSlabAnchors delta gamma presentation ↔
      ∃ j, anchor ∈ typeIIAffineThickSlabAnchors delta gamma
        (typeIIProjectedAffineNormal (presentation.normal j))
        (typeIIProjectedAffineBound (presentation.normal j)
          (presentation.bound j)) := by
  classical
  simp [typeIIAffinePresentationThickSlabAnchors]

/-- Relevant anchors are covered when every region point has a boundary
witness whose projected normal is nonzero. -/
theorem typeIIRelevantCubeAnchors_subset_affinePresentationThickSlabAnchors
    {k : Nat} {delta gamma : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region)
    (hdelta : 0 < delta)
    (hboundary : ∀ e, e ∈ region →
      ∃ j, typeIIProjectedAffineNormal (presentation.normal j) ≠ 0 ∧
        |typeIIAffineValue (presentation.normal j) e -
          presentation.bound j| <= gamma) :
    typeIIRelevantCubeAnchors delta region ⊆
      typeIIAffinePresentationThickSlabAnchors delta gamma presentation := by
  intro anchor hanchor
  obtain ⟨x, hxCube, hxRegion⟩ :=
    (mem_typeIIRelevantCubeAnchors.mp hanchor).2
  obtain ⟨j, hprojected, hxSlab⟩ :=
    hboundary (completeProjectedLogTuple x) hxRegion
  rw [mem_typeIIAffinePresentationThickSlabAnchors]
  exact ⟨j, mem_typeIIAffineThickSlabAnchors_of_projected_witness
    hdelta hprojected
    (typeIIRelevantCubeAnchors_subset_grid delta region hanchor)
    hxCube hxSlab⟩

/--
The arbitrary-witness form of the cover. A projected-zero constraint is ruled out by the exact
scalar classification.
-/
theorem typeIIRelevantCubeAnchors_subset_affinePresentationThickSlabAnchors_of_zero_inactive
    {k : Nat} {delta gamma : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region)
    (hdelta : 0 < delta)
    (hboundary : ∀ e, e ∈ region →
      ∃ j, |typeIIAffineValue (presentation.normal j) e -
        presentation.bound j| <= gamma)
    (hzeroInactive : ∀ j,
      typeIIProjectedAffineNormal (presentation.normal j) = 0 →
      ¬ |presentation.normal j (Fin.last k) - presentation.bound j| <= gamma) :
    typeIIRelevantCubeAnchors delta region ⊆
      typeIIAffinePresentationThickSlabAnchors delta gamma presentation := by
  intro anchor hanchor
  obtain ⟨x, hxCube, hxRegion⟩ :=
    (mem_typeIIRelevantCubeAnchors.mp hanchor).2
  obtain ⟨j, hxSlab⟩ :=
    hboundary (completeProjectedLogTuple x) hxRegion
  have hprojected :
      typeIIProjectedAffineNormal (presentation.normal j) ≠ 0 := by
    intro hzero
    apply hzeroInactive j hzero
    have hxProjectedSlab : x ∈ typeIIProjectedAffineSlab
        (presentation.normal j) (presentation.bound j) gamma := by
      simp only [typeIIProjectedAffineSlab, Set.mem_setOf_eq]
      exact hxSlab
    exact (mem_typeIIProjectedAffineSlab_iff_of_projected_eq_zero
      hzero).mp hxProjectedSlab
  rw [mem_typeIIAffinePresentationThickSlabAnchors]
  exact ⟨j, mem_typeIIAffineThickSlabAnchors_of_projected_witness
    hdelta hprojected
    (typeIIRelevantCubeAnchors_subset_grid delta region hanchor)
    hxCube hxSlab⟩

end

end PrimesRestrictedDigits
