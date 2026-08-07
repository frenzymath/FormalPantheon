import BoundedGaps.Maynard.ConcreteS2OuterUnitBoundary
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

def finiteSimplexOf (H : Finset ℕ) : Set (H → ℝ) :=
  {t | t ∈ maynardCubeOf H ∧ ∑ h, t h ≤ 1}

def fractionalGridCell {H : Finset ℕ}
    (mesh : ℕ) (j : H → ℕ) : Set (H → ℝ) :=
  Set.pi Set.univ fun h => Set.Ico
    (fractionalGridLower mesh j h) (fractionalGridUpper mesh j h)

def fractionalGridCellUnion {H : Finset ℕ}
    (I : Finset (H → ℕ)) (mesh : ℕ) : Set (H → ℝ) :=
  ⋃ j ∈ I, fractionalGridCell mesh j

def fractionalCoordinateOneFaces (H : Finset ℕ) : Set (H → ℝ) :=
  ⋃ h : H, {x | x h = 1}

theorem measurableSet_fractionalGridCell {H : Finset ℕ}
    (mesh : ℕ) (j : H → ℕ) :
    MeasurableSet (fractionalGridCell mesh j) := by
  apply MeasurableSet.univ_pi
  intro h
  exact measurableSet_Ico

theorem measurableSet_fractionalGridCellUnion {H : Finset ℕ}
    (I : Finset (H → ℕ)) (mesh : ℕ) :
    MeasurableSet (fractionalGridCellUnion I mesh) := by
  unfold fractionalGridCellUnion
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro hj
  exact measurableSet_fractionalGridCell mesh j

theorem volume_fractionalGridCell_toReal {H : Finset ℕ}
    {mesh : ℕ} (hmesh : 0 < mesh) (j : H → ℕ) :
    (volume (fractionalGridCell mesh j)).toReal =
      ∏ h : H, (fractionalGridUpper mesh j h -
        fractionalGridLower mesh j h) := by
  rw [fractionalGridCell, Real.volume_pi_Ico_toReal]
  intro h
  rw [fractionalGridUpper_eq_lower_add_inv hmesh]
  exact le_add_of_nonneg_right (by positivity)

set_option maxRecDepth 8000 in
theorem pairwiseDisjoint_fractionalGridCell {H : Finset ℕ}
    {mesh : ℕ} (hmesh : 0 < mesh) :
    (fractionalGridIndex H mesh : Set (H → ℕ)).PairwiseDisjoint
      (fractionalGridCell mesh) := by
  rw [Set.pairwiseDisjoint_iff]
  intro j hj k hk hinter
  obtain ⟨x, hxj, hxk⟩ := hinter
  rw [fractionalGridCell, Set.mem_univ_pi] at hxj hxk
  funext h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hsucc : j h + 1 ≤ k h := Nat.succ_le_iff.mpr hjk
    have hupperLower : fractionalGridUpper mesh j h ≤
        fractionalGridLower mesh k h := by
      unfold fractionalGridUpper fractionalGridLower
      exact (div_le_div_iff_of_pos_right
        (by exact_mod_cast hmesh)).mpr (by exact_mod_cast hsucc)
    linarith [(hxj h).2, (hxk h).1]
  · have hsucc : k h + 1 ≤ j h := Nat.succ_le_iff.mpr hkj
    have hupperLower : fractionalGridUpper mesh k h ≤
        fractionalGridLower mesh j h := by
      unfold fractionalGridUpper fractionalGridLower
      exact (div_le_div_iff_of_pos_right
        (by exact_mod_cast hmesh)).mpr (by exact_mod_cast hsucc)
    linarith [(hxk h).2, (hxj h).1]

set_option maxRecDepth 8000 in
theorem volume_fractionalGridCellUnion_toReal {H : Finset ℕ}
    {mesh : ℕ} (hmesh : 0 < mesh)
    {I : Finset (H → ℕ)} (hI : I ⊆ fractionalGridIndex H mesh) :
    (volume (fractionalGridCellUnion I mesh)).toReal =
      ∑ j ∈ I, ∏ h : H, (fractionalGridUpper mesh j h -
        fractionalGridLower mesh j h) := by
  have hISet : (I : Set (H → ℕ)) ⊆
      (fractionalGridIndex H mesh : Set (H → ℕ)) := hI
  have hd : (I : Set (H → ℕ)).PairwiseDisjoint
      (fractionalGridCell mesh) :=
    Set.Pairwise.mono hISet (pairwiseDisjoint_fractionalGridCell hmesh)
  have hfinite : ∀ j ∈ I, volume (fractionalGridCell mesh j) ≠ ⊤ := by
    intro j hj
    rw [fractionalGridCell, Real.volume_pi_Ico]
    apply ENNReal.prod_ne_top
    intro h hh
    exact ENNReal.ofReal_ne_top
  rw [← MeasureTheory.measureReal_def, fractionalGridCellUnion,
    MeasureTheory.measureReal_biUnion_finset hd
      (fun j hj => measurableSet_fractionalGridCell mesh j) hfinite]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MeasureTheory.measureReal_def, volume_fractionalGridCell_toReal hmesh]

set_option maxRecDepth 8000 in
theorem fractionalGridCell_subset_finiteSimplexOf_inner
    {H : Finset ℕ} {mesh : ℕ} (hmesh : 0 < mesh)
    {j : H → ℕ} (hj : j ∈ fractionalSimplexInnerGridIndex H mesh) :
    fractionalGridCell mesh j ⊆ finiteSimplexOf H := by
  intro x hx
  have hjData := fractionalSimplexInnerGridIndex_data hmesh hj
  have hxCoord := Set.mem_univ_pi.mp hx
  constructor
  · rw [maynardCubeOf, Set.mem_pi]
    intro h hh
    have hend := hjData.1 h
    exact ⟨hend.1.1.trans (hxCoord h).1,
      (hxCoord h).2.le.trans hend.2.1.2⟩
  · have hsumLe : (∑ h : H, x h) ≤
        ∑ h : H, fractionalGridUpper mesh j h := by
      apply Finset.sum_le_sum
      intro h hh
      exact (hxCoord h).2.le
    exact hsumLe.trans hjData.2.le

def fractionalRealGridIndex {H : Finset ℕ}
    (mesh : ℕ) (x : H → ℝ) : H → ℕ :=
  fun h => ⌊(mesh : ℝ) * x h⌋₊

theorem fractionalRealGridIndex_mem {H : Finset ℕ}
    {mesh : ℕ} (hmesh : 0 < mesh) {x : H → ℝ}
    (hxCube : x ∈ maynardCubeOf H) (hxOne : ∀ h, x h ≠ 1) :
    fractionalRealGridIndex mesh x ∈ fractionalGridIndex H mesh := by
  rw [fractionalGridIndex, Fintype.mem_piFinset]
  intro h
  apply Finset.mem_range.mpr
  rw [fractionalRealGridIndex, Nat.floor_lt]
  · have hx := hxCube h (by simp)
    have hxlt : x h < 1 := lt_of_le_of_ne hx.2 (hxOne h)
    have hmeshReal : (0 : ℝ) < mesh := by exact_mod_cast hmesh
    nlinarith
  · have hx := hxCube h (by simp)
    exact mul_nonneg (by exact_mod_cast hmesh.le) hx.1

theorem mem_fractionalGridCell_realGridIndex {H : Finset ℕ}
    {mesh : ℕ} (hmesh : 0 < mesh) {x : H → ℝ}
    (hxCube : x ∈ maynardCubeOf H) :
    x ∈ fractionalGridCell mesh (fractionalRealGridIndex mesh x) := by
  rw [fractionalGridCell, Set.mem_univ_pi]
  intro h
  have hx := hxCube h (by simp)
  have hmeshReal : (0 : ℝ) < mesh := by exact_mod_cast hmesh
  constructor
  · unfold fractionalGridLower fractionalRealGridIndex
    apply (div_le_iff₀ hmeshReal).mpr
    simpa [mul_comm] using Nat.floor_le (mul_nonneg hmeshReal.le hx.1)
  · unfold fractionalGridUpper fractionalRealGridIndex
    apply (lt_div_iff₀ hmeshReal).mpr
    have hfloor := Nat.lt_floor_add_one ((mesh : ℝ) * x h)
    push_cast
    simpa [mul_comm] using hfloor

theorem finiteSimplexOf_subset_inner_boundary_faces {H : Finset ℕ}
    (mesh : ℕ) (hmesh : 0 < mesh) :
    finiteSimplexOf H ⊆
      fractionalGridCellUnion (fractionalSimplexInnerGridIndex H mesh) mesh ∪
        fractionalGridCellUnion
          (fractionalSimplexBoundaryGridIndex H mesh) mesh ∪
        fractionalCoordinateOneFaces H := by
  intro x hx
  by_cases hface : ∃ h : H, x h = 1
  · right
    rw [fractionalCoordinateOneFaces, Set.mem_iUnion]
    exact hface
  · have hxOne : ∀ h : H, x h ≠ 1 := not_exists.mp hface
    let j := fractionalRealGridIndex mesh x
    have hjGrid := fractionalRealGridIndex_mem hmesh hx.1 hxOne
    have hxCell := mem_fractionalGridCell_realGridIndex hmesh hx.1
    have hjPartition : j ∈ fractionalSimplexInnerGridIndex H mesh ∪
        (fractionalSimplexBoundaryGridIndex H mesh ∪
          fractionalSimplexOuterGridIndex H mesh) := by
      rw [← fractionalGridIndex_eq_inner_union_boundary_union_outer]
      exact hjGrid
    rcases Finset.mem_union.mp hjPartition with hjInner | hjRest
    · apply Or.inl
      apply Or.inl
      rw [fractionalGridCellUnion, Set.mem_iUnion]
      exact ⟨j, Set.mem_iUnion_of_mem hjInner hxCell⟩
    · rcases Finset.mem_union.mp hjRest with hjBoundary | hjOuter
      · apply Or.inl
        apply Or.inr
        rw [fractionalGridCellUnion, Set.mem_iUnion]
        exact ⟨j, Set.mem_iUnion_of_mem hjBoundary hxCell⟩
      · have houter := (Finset.mem_filter.mp hjOuter).2
        have hxCoord := Set.mem_univ_pi.mp hxCell
        have hsumLe : (∑ h : H, fractionalGridLower mesh j h) ≤
            ∑ h : H, x h := by
          apply Finset.sum_le_sum
          intro h hh
          exact (hxCoord h).1
        linarith [hx.2]

theorem volume_fractionalCoordinateOneFaces (H : Finset ℕ) :
    volume (fractionalCoordinateOneFaces H) = 0 := by
  rw [fractionalCoordinateOneFaces]
  apply measure_iUnion_null
  intro h
  rw [MeasureTheory.volume_pi]
  exact Measure.pi_hyperplane (fun _ : H => volume) h 1

end BoundedGaps.Maynard
