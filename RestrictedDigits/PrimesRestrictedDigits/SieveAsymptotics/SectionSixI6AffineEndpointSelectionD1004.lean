import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6AffineEndpointRowsD1004
import Mathlib.Data.Finset.Max

/-!
# Attained affine endpoints for every I6 fiber

The upper one-sentinel is redundant under the explicit bound on w. Source:
`MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits

theorem i6D1004_cellLower_le_iff
    (label : i6D691Label) (z : (Real × Real) × Real) (s : Real) :
    sectionSixFirstLowBelowI6CellLower z.1.1 z.1.2 z.2 label.2.1 label.2.2 ≤ s ↔
      ∀ i : Fin 7, i6D1004LowerActive label i = true ->
        (i6D1004LowerAffine label.2.1 i).evalReal
          (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z) ≤ s := by
  let high : Fin 5 -> Real := fun i => if label.2.2 i = true then
    sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 i else 0
  change max (sectionSixThetaGap (1 / 1000000))
    (max (sectionSixFirstLowBelowI6BranchLower z.1.1 z.1.2 z.2 label.2.1)
      (max 0 (max (high 0) (max (high 1) (max (high 2) (max (high 3) (high 4)))))))
        ≤ s ↔ _
  have heval (i : Fin 7) := congrFun (i6D1004LowerAffine_eval label.2.1 z) i
  by_cases hfloor : sectionSixThetaGap (1 / 1000000) ≤ s
  · have hs : 0 ≤ s := (show (0 : Real) ≤ sectionSixThetaGap (1 / 1000000) by
      norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]).trans hfloor
    have hband (i : Fin 5) : high i ≤ s ↔
        (label.2.2 i = true -> sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 i ≤ s) := by
      by_cases hi : label.2.2 i = true <;> simp [high, hi, hs]
    have hbranch :
        sectionSixFirstLowBelowI6BranchLower z.1.1 z.1.2 z.2 label.2.1 ≤ s ↔
        (label.2.1 ≠ 2 ->
          sectionSixFirstLowBelowI6BranchLower z.1.1 z.1.2 z.2 label.2.1 ≤ s) := by
      by_cases hb : label.2.1 = 2
      · simpa [hb, sectionSixFirstLowBelowI6BranchLower] using hfloor
      · simp [hb]
    simp only [max_le_iff]
    rw [hbranch]
    simp only [one_div] at hfloor
    simp [hband, hfloor, hs, heval,
      i6D1004LowerActive, Fin.forall_fin_succ]
  · constructor
    · intro h
      simp only [max_le_iff] at h
      exact (hfloor h.1).elim
    · intro h
      have hzero := h 0 rfl
      rw [heval 0] at hzero
      exact (hfloor hzero).elim

theorem i6D1004_le_cellUpper_iff
    (label : i6D691Label) (z : (Real × Real) × Real) (s : Real) (hw : z.2 ≤ 1) :
    s ≤ sectionSixFirstLowBelowI6CellUpper z.1.1 z.1.2 z.2 label.2.1 label.2.2 ↔
      ∀ i : Fin 7, i6D1004UpperActive label i = true ->
        s ≤ (i6D1004UpperAffine label.2.1 i).evalReal
          (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z) := by
  let low : Fin 5 -> Real := fun i => if label.2.2 i = true then 1 else
    sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 i
  change s ≤ min z.2
    (min (sectionSixFirstLowBelowI6BranchUpper z.1.1 z.1.2 z.2 label.2.1)
      (min 1 (min (low 0) (min (low 1) (min (low 2) (min (low 3) (low 4))))))) ↔ _
  have heval (i : Fin 7) := congrFun (i6D1004UpperAffine_eval label.2.1 z) i
  by_cases hceiling : s ≤ z.2
  · have hs : s ≤ 1 := hceiling.trans hw
    have hband (i : Fin 5) : s ≤ low i ↔
        (label.2.2 i = false -> s ≤ sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 i) := by
      cases hi : label.2.2 i <;> simp [low, hi, hs]
    simp [hband, hceiling, hs, heval,
      i6D1004UpperActive, Fin.forall_fin_succ]
  · simp [hceiling, heval, i6D1004UpperActive, Fin.forall_fin_succ]

theorem i6D1004_exists_lower_endpoint (label : i6D691Label) (z : (Real × Real) × Real) :
    ∃ i : Fin 7, i6D1004LowerActive label i = true ∧
      (i6D1004LowerAffine label.2.1 i).evalReal
        (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z) =
        sectionSixFirstLowBelowI6CellLower z.1.1 z.1.2 z.2 label.2.1 label.2.2 := by
  let active := Finset.univ.filter (fun i => i6D1004LowerActive label i = true)
  let value (i : Fin 7) := (i6D1004LowerAffine label.2.1 i).evalReal
    (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z)
  have hne : active.Nonempty := ⟨0, by simp [active, i6D1004LowerActive]⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image active value hne
  have hiActive : i6D1004LowerActive label i = true := (Finset.mem_filter.mp hi).2
  refine ⟨i, hiActive, le_antisymm ?_ ?_⟩
  · exact (i6D1004_cellLower_le_iff label z _).mp le_rfl i hiActive
  · apply (i6D1004_cellLower_le_iff label z (value i)).mpr
    intro j hj
    exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

theorem i6D1004_exists_upper_endpoint
    (label : i6D691Label) (z : (Real × Real) × Real) (hw : z.2 ≤ 1) :
    ∃ i : Fin 7, i6D1004UpperActive label i = true ∧
      (i6D1004UpperAffine label.2.1 i).evalReal
        (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z) =
        sectionSixFirstLowBelowI6CellUpper z.1.1 z.1.2 z.2 label.2.1 label.2.2 := by
  let active := Finset.univ.filter (fun i => i6D1004UpperActive label i = true)
  let value (i : Fin 7) := (i6D1004UpperAffine label.2.1 i).evalReal
    (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z)
  have hne : active.Nonempty := ⟨0, by simp [active, i6D1004UpperActive]⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image active value hne
  have hiActive : i6D1004UpperActive label i = true := (Finset.mem_filter.mp hi).2
  refine ⟨i, hiActive, le_antisymm ?_ ?_⟩
  · apply (i6D1004_le_cellUpper_iff label z (value i) hw).mpr
    intro j hj
    exact hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  · exact (i6D1004_le_cellUpper_iff label z _ hw).mp le_rfl i hiActive

end PrimesRestrictedDigits
