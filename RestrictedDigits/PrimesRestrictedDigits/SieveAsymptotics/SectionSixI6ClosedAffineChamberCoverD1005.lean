import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ClosedAffineChamberDataD1005
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6AffineEndpointSelectionD1004

/-!
# Closed affine chamber cover of every I6 ordered fiber base

The exact root supplies the upper sentinel bound. Ties and equality fibers remain in the
cover; no disjointness or numerical estimate is asserted. Source: `MAYNARD-PRD-PUBLISHED`,
Section 6, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace PrimesRestrictedDigits

theorem i6D1005Chamber_endpoints (label : i6D691Label) (l h : Fin 7)
    {x : Fin 3 -> Real} (hx : x ∈ i6D1005Chamber label l h) :
    (i6D1004LowerAffine label.2.1 l).evalReal x =
      sectionSixFirstLowBelowI6CellLower (x 0) (x 1) (x 2) label.2.1 label.2.2 ∧
    (i6D1004UpperAffine label.2.1 h).evalReal x =
      sectionSixFirstLowBelowI6CellUpper (x 0) (x 1) (x 2) label.2.1 label.2.2 := by
  rcases hx with ⟨hl, hh, hroot, hwalls⟩
  have hparts := (i6D1005ChamberWalls_nonneg_iff label l h x).mp hwalls
  have hbounds := (i6D999_mem_orderedPairRoot_iff x).mp hroot
  let z := sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 x
  have hcoords : sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z = x :=
    sectionSixFirstLowCentralSmallI5P0RationalCoordinates3_nestedPoint3 x
  have hw : z.2 ≤ 1 := by
    change x 2 ≤ 1
    linarith [hbounds.1, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2]
  constructor
  · apply le_antisymm
    · have hle := (i6D1004_cellLower_le_iff label z _).mp le_rfl l hl
      rw [hcoords] at hle
      exact hle
    · apply (i6D1004_cellLower_le_iff label z _).mpr
      simpa only [hcoords] using hparts.2.2.1
  · apply le_antisymm
    · apply (i6D1004_le_cellUpper_iff label z _ hw).mpr
      simpa only [hcoords] using hparts.2.2.2
    · have hle := (i6D1004_le_cellUpper_iff label z _ hw).mp le_rfl h hh
      rw [hcoords] at hle
      exact hle

theorem i6D1005Chamber_subset_orderedOuter (label : i6D691Label) (l h : Fin 7) :
    i6D1005Chamber label l h ⊆
      {x | sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 x ∈
        orderedOuter (i6D996TailBase label.1)
          (fun z => sectionSixFirstLowBelowI6CellLower z.1.1 z.1.2 z.2 label.2.1 label.2.2)
          (fun z => sectionSixFirstLowBelowI6CellUpper z.1.1 z.1.2 z.2 label.2.1 label.2.2)} := by
  intro x hx
  have hend := i6D1005Chamber_endpoints label l h hx
  have hparts := (i6D1005ChamberWalls_nonneg_iff label l h x).mp hx.2.2.2
  have hbounds := (i6D999_mem_orderedPairRoot_iff x).mp hx.2.2.1
  change ((x 0, x 1), x 2) ∈ i6D996TailBase label.1 ∧
    sectionSixFirstLowBelowI6CellLower (x 0) (x 1) (x 2) label.2.1 label.2.2 ≤
      sectionSixFirstLowBelowI6CellUpper (x 0) (x 1) (x 2) label.2.1 label.2.2
  constructor
  · refine ⟨?_, hbounds.2.1, hbounds.2.2.1, ?_, ?_⟩
    · change ((sectionSixThetaGap (1 / 1000000) ≤ x 0 ∧
          x 0 ≤ sectionSixThetaOne (1 / 1000000)) ∧
        (sectionSixThetaGap (1 / 1000000) ≤ x 1 ∧
          x 1 ≤ sectionSixThetaOne (1 / 1000000))) ∧
        (sectionSixThetaGap (1 / 1000000) ≤ x 2 ∧
          x 2 ≤ sectionSixThetaOne (1 / 1000000))
      norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩ <;>
        linarith [hbounds.1, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2]
    · norm_num [sectionSixThetaOne]
      exact hbounds.2.2.2
    · have hbase := hparts.1
      rw [i6D1005BaseWall_eval] at hbase
      cases hrho : label.1 <;> simp only [hrho, Bool.false_eq_true, ↓reduceIte] at hbase ⊢
      all_goals
        norm_num [sectionSixThetaOne, sectionSixThetaTwo]
        linarith
  · rw [← hend.1, ← hend.2]
    exact hparts.2.1

theorem i6D1005OrderedOuter_subset_iUnion_chambers (label : i6D691Label) :
    {x | sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 x ∈
      orderedOuter (i6D996TailBase label.1)
        (fun z => sectionSixFirstLowBelowI6CellLower z.1.1 z.1.2 z.2 label.2.1 label.2.2)
        (fun z => sectionSixFirstLowBelowI6CellUpper z.1.1 z.1.2 z.2 label.2.1 label.2.2)} ⊆
      ⋃ l : Fin 7, ⋃ h : Fin 7, i6D1005Chamber label l h := by
  intro x hx
  let z := sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 x
  have hbase : z ∈ i6D996TailBase label.1 := hx.1
  have hcoords : sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z = x :=
    sectionSixFirstLowCentralSmallI5P0RationalCoordinates3_nestedPoint3 x
  have hw : z.2 ≤ 1 := by
    have hupper := hbase.1.2.2
    norm_num [sectionSixThetaOne] at hupper
    linarith
  obtain ⟨l, hl, heql⟩ := i6D1004_exists_lower_endpoint label z
  obtain ⟨h, hh, heqh⟩ := i6D1004_exists_upper_endpoint label z hw
  rw [hcoords] at heql heqh
  refine Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨h, hl, hh, ?_, ?_⟩⟩
  · exact i6D999TailBase_subset_root label.1 hbase
  · apply (i6D1005ChamberWalls_nonneg_iff label l h x).mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hside := hbase.2.2.2.2
      rw [i6D1005BaseWall_eval]
      change (match label.1 with
        | false => x 0 + x 1 + x 2 ≤ sectionSixThetaOne (1 / 1000000)
        | true => sectionSixThetaTwo (1 / 1000000) ≤ x 0 + x 1 + x 2) at hside
      cases hrho : label.1 <;> simp only [hrho, Bool.false_eq_true, ↓reduceIte] at hside ⊢
      all_goals
        norm_num [sectionSixThetaOne, sectionSixThetaTwo] at hside
        linarith
    · rw [heql, heqh]
      exact hx.2
    · have hrows := (i6D1004_cellLower_le_iff label z _).mp le_rfl
      rw [hcoords] at hrows
      intro i hi
      rw [heql]
      exact hrows i hi
    · have hrows := (i6D1004_le_cellUpper_iff label z _ hw).mp le_rfl
      rw [hcoords] at hrows
      intro i hi
      rw [heqh]
      exact hrows i hi

end PrimesRestrictedDigits
