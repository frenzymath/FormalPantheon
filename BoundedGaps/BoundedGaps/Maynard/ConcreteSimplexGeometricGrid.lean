import BoundedGaps.Maynard.ConcreteSimplexGridOscillation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

def engelsmaGridUpperPoint
    (m : ℕ) (j : BoundedGaps.engelsmaTuple → ℕ) : Fin 105 → ℝ :=
  fun i => fractionalGridUpper m j (engelsmaIndexEquiv.symm i)

def engelsmaGridCell
    (m : ℕ) (j : BoundedGaps.engelsmaTuple → ℕ) : Set (Fin 105 → ℝ) :=
  Set.pi Set.univ fun i => Set.Ico
    (engelsmaGridLowerPoint m j i) (engelsmaGridUpperPoint m j i)

def engelsmaGridCellUnion
    (I : Finset (BoundedGaps.engelsmaTuple → ℕ)) (m : ℕ) :
    Set (Fin 105 → ℝ) :=
  ⋃ j ∈ I, engelsmaGridCell m j

def engelsmaCoordinateOneFaces : Set (Fin 105 → ℝ) :=
  ⋃ i : Fin 105, {x | x i = 1}

theorem measurableSet_engelsmaGridCell (m : ℕ)
    (j : BoundedGaps.engelsmaTuple → ℕ) :
    MeasurableSet (engelsmaGridCell m j) := by
  apply MeasurableSet.univ_pi
  intro i
  exact measurableSet_Ico

theorem volume_engelsmaGridCell_toReal
    {m : ℕ} (hm : 0 < m) (j : BoundedGaps.engelsmaTuple → ℕ) :
    (volume (engelsmaGridCell m j)).toReal =
      ∏ h : BoundedGaps.engelsmaTuple,
        (fractionalGridUpper m j h - fractionalGridLower m j h) := by
  rw [engelsmaGridCell, Real.volume_pi_Ico_toReal]
  · change (∏ i : Fin 105,
        (fractionalGridUpper m j (engelsmaIndexEquiv.symm i) -
          fractionalGridLower m j (engelsmaIndexEquiv.symm i))) = _
    simpa using (engelsmaIndexEquiv.symm.prod_comp
      (fun h : BoundedGaps.engelsmaTuple =>
        fractionalGridUpper m j h - fractionalGridLower m j h))
  · intro i
    simp only [engelsmaGridLowerPoint, engelsmaGridUpperPoint]
    rw [fractionalGridUpper_eq_lower_add_inv hm]
    exact le_add_of_nonneg_right (by positivity)

set_option maxRecDepth 10000 in
theorem pairwiseDisjoint_engelsmaGridCell {m : ℕ} (hm : 0 < m) :
    (fractionalGridIndex BoundedGaps.engelsmaTuple m :
      Set (BoundedGaps.engelsmaTuple → ℕ)).PairwiseDisjoint
        (engelsmaGridCell m) := by
  rw [Set.pairwiseDisjoint_iff]
  intro j hj k hk hinter
  obtain ⟨x, hxj, hxk⟩ := hinter
  rw [engelsmaGridCell, Set.mem_univ_pi] at hxj hxk
  funext h
  have hxjh : fractionalGridLower m j h ≤ x (engelsmaIndexEquiv h) ∧
      x (engelsmaIndexEquiv h) < fractionalGridUpper m j h := by
    simpa [engelsmaGridLowerPoint, engelsmaGridUpperPoint] using
      hxj (engelsmaIndexEquiv h)
  have hxkh : fractionalGridLower m k h ≤ x (engelsmaIndexEquiv h) ∧
      x (engelsmaIndexEquiv h) < fractionalGridUpper m k h := by
    simpa [engelsmaGridLowerPoint, engelsmaGridUpperPoint] using
      hxk (engelsmaIndexEquiv h)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hsucc : j h + 1 ≤ k h := Nat.succ_le_iff.mpr hjk
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    have hupperLower : fractionalGridUpper m j h ≤
        fractionalGridLower m k h := by
      unfold fractionalGridUpper fractionalGridLower
      exact (div_le_div_iff_of_pos_right hmReal).mpr (by exact_mod_cast hsucc)
    linarith
  · have hsucc : k h + 1 ≤ j h := Nat.succ_le_iff.mpr hkj
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    have hupperLower : fractionalGridUpper m k h ≤
        fractionalGridLower m j h := by
      unfold fractionalGridUpper fractionalGridLower
      exact (div_le_div_iff_of_pos_right hmReal).mpr (by exact_mod_cast hsucc)
    linarith

set_option maxRecDepth 10000 in
theorem volume_engelsmaGridCellUnion_toReal
    {m : ℕ} (hm : 0 < m)
    {I : Finset (BoundedGaps.engelsmaTuple → ℕ)}
    (hI : I ⊆ fractionalGridIndex BoundedGaps.engelsmaTuple m) :
    (volume (engelsmaGridCellUnion I m)).toReal =
      ∑ j ∈ I, ∏ h : BoundedGaps.engelsmaTuple,
        (fractionalGridUpper m j h - fractionalGridLower m j h) := by
  have hISet : (I : Set (BoundedGaps.engelsmaTuple → ℕ)) ⊆
      (fractionalGridIndex BoundedGaps.engelsmaTuple m :
        Set (BoundedGaps.engelsmaTuple → ℕ)) := by
    intro j hj
    exact hI hj
  have hd : (I : Set (BoundedGaps.engelsmaTuple → ℕ)).PairwiseDisjoint
      (engelsmaGridCell m) :=
    Set.Pairwise.mono hISet (pairwiseDisjoint_engelsmaGridCell hm)
  have hfinite : ∀ j ∈ I, volume (engelsmaGridCell m j) ≠ ⊤ := by
    intro j hj
    rw [engelsmaGridCell, Real.volume_pi_Ico]
    apply ENNReal.prod_ne_top
    intro i hi
    exact ENNReal.ofReal_ne_top
  rw [← MeasureTheory.measureReal_def, engelsmaGridCellUnion,
    MeasureTheory.measureReal_biUnion_finset hd
      (fun j hj => measurableSet_engelsmaGridCell m j) hfinite]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [MeasureTheory.measureReal_def, volume_engelsmaGridCell_toReal hm]

set_option maxRecDepth 10000 in
theorem engelsmaGridCell_subset_maynardSimplex_of_inner
    {m : ℕ} (hm : 0 < m)
    {j : BoundedGaps.engelsmaTuple → ℕ}
    (hj : j ∈ fractionalSimplexInnerGridIndex
      BoundedGaps.engelsmaTuple m) :
    engelsmaGridCell m j ⊆ maynardSimplex 105 := by
  intro x hx
  have hjData := fractionalSimplexInnerGridIndex_data hm hj
  have hxCoord := Set.mem_univ_pi.mp hx
  rw [maynardSimplex, maynardCube, maynardCubeOf]
  constructor
  · rw [Set.mem_pi]
    intro i hi
    have hxi := hxCoord i
    change engelsmaGridLowerPoint m j i ≤ x i ∧
      x i < engelsmaGridUpperPoint m j i at hxi
    have hend := hjData.1 (engelsmaIndexEquiv.symm i)
    exact ⟨hend.1.1.trans hxi.1, hxi.2.le.trans hend.2.1.2⟩
  · have hsumLe : (∑ i : Fin 105, x i) ≤
        ∑ i : Fin 105, engelsmaGridUpperPoint m j i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hxCoord i).2.le
    have hsumUpper : (∑ i : Fin 105, engelsmaGridUpperPoint m j i) =
        ∑ h : BoundedGaps.engelsmaTuple, fractionalGridUpper m j h := by
      exact engelsmaIndexEquiv.symm.sum_comp _
    rw [hsumUpper] at hsumLe
    exact hsumLe.trans hjData.2.le

def engelsmaRealGridIndex (m : ℕ) (x : Fin 105 → ℝ) :
    BoundedGaps.engelsmaTuple → ℕ :=
  fun h => ⌊(m : ℝ) * x (engelsmaIndexEquiv h)⌋₊

theorem engelsmaRealGridIndex_mem
    {m : ℕ} (hm : 0 < m) {x : Fin 105 → ℝ}
    (hxCube : x ∈ maynardCube 105)
    (hxOne : ∀ i, x i ≠ 1) :
    engelsmaRealGridIndex m x ∈
      fractionalGridIndex BoundedGaps.engelsmaTuple m := by
  rw [fractionalGridIndex, Fintype.mem_piFinset]
  intro h
  apply Finset.mem_range.mpr
  rw [engelsmaRealGridIndex, Nat.floor_lt]
  · have hx := hxCube (engelsmaIndexEquiv h) (by simp)
    have hxlt : x (engelsmaIndexEquiv h) < 1 :=
      lt_of_le_of_ne hx.2 (hxOne _)
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    nlinarith
  · have hx := hxCube (engelsmaIndexEquiv h) (by simp)
    exact mul_nonneg (by exact_mod_cast hm.le) hx.1

theorem mem_engelsmaGridCell_realGridIndex
    {m : ℕ} (hm : 0 < m) {x : Fin 105 → ℝ}
    (hxCube : x ∈ maynardCube 105) :
    x ∈ engelsmaGridCell m (engelsmaRealGridIndex m x) := by
  rw [engelsmaGridCell, Set.mem_univ_pi]
  intro i
  have hxi := hxCube i (by simp)
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  change fractionalGridLower m (engelsmaRealGridIndex m x)
      (engelsmaIndexEquiv.symm i) ≤ x i ∧
    x i < fractionalGridUpper m (engelsmaRealGridIndex m x)
      (engelsmaIndexEquiv.symm i)
  have hequiv : engelsmaIndexEquiv (engelsmaIndexEquiv.symm i) = i :=
    engelsmaIndexEquiv.apply_symm_apply i
  constructor
  · unfold fractionalGridLower engelsmaRealGridIndex
    rw [hequiv]
    apply (div_le_iff₀ hmReal).mpr
    simpa [mul_comm] using Nat.floor_le (mul_nonneg hmReal.le hxi.1)
  · unfold fractionalGridUpper engelsmaRealGridIndex
    rw [hequiv]
    apply (lt_div_iff₀ hmReal).mpr
    have hfloor := Nat.lt_floor_add_one ((m : ℝ) * x i)
    push_cast
    simpa [mul_comm] using hfloor

set_option maxRecDepth 10000 in
theorem not_mem_fractionalSimplexOuterGridIndex_of_cell_simplex
    {m : ℕ} {j : BoundedGaps.engelsmaTuple → ℕ}
    {x : Fin 105 → ℝ} (hxCell : x ∈ engelsmaGridCell m j)
    (hxSimplex : x ∈ maynardSimplex 105) :
    j ∉ fractionalSimplexOuterGridIndex BoundedGaps.engelsmaTuple m := by
  intro hjOuter
  have houter := (Finset.mem_filter.mp hjOuter).2
  have hxCoord := Set.mem_univ_pi.mp hxCell
  have hsumLe : (∑ h : BoundedGaps.engelsmaTuple,
      fractionalGridLower m j h) ≤ ∑ i : Fin 105, x i := by
    rw [← engelsmaIndexEquiv.symm.sum_comp (fun h => fractionalGridLower m j h)]
    apply Finset.sum_le_sum
    intro i hi
    exact (hxCoord i).1
  linarith [hxSimplex.2]

set_option maxRecDepth 10000 in
theorem maynardSimplex_subset_inner_boundary_faces (m : ℕ) (hm : 0 < m) :
    maynardSimplex 105 ⊆
      engelsmaGridCellUnion
          (fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m) m ∪
        engelsmaGridCellUnion
          (fractionalSimplexBoundaryGridIndex BoundedGaps.engelsmaTuple m) m ∪
        engelsmaCoordinateOneFaces := by
  intro x hx
  by_cases hface : ∃ i : Fin 105, x i = 1
  · right
    rw [engelsmaCoordinateOneFaces, Set.mem_iUnion]
    exact hface
  · have hxOne : ∀ i, x i ≠ 1 := not_exists.mp hface
    let j := engelsmaRealGridIndex m x
    have hjGrid := engelsmaRealGridIndex_mem hm hx.1 hxOne
    have hxCell := mem_engelsmaGridCell_realGridIndex hm hx.1
    have hjPartition : j ∈
        fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m ∪
          (fractionalSimplexBoundaryGridIndex BoundedGaps.engelsmaTuple m ∪
            fractionalSimplexOuterGridIndex BoundedGaps.engelsmaTuple m) := by
      rw [← fractionalGridIndex_eq_inner_union_boundary_union_outer]
      exact hjGrid
    rcases Finset.mem_union.mp hjPartition with hjInner | hjRest
    · left; left
      rw [engelsmaGridCellUnion, Set.mem_iUnion]
      exact ⟨j, Set.mem_iUnion_of_mem hjInner hxCell⟩
    · rcases Finset.mem_union.mp hjRest with hjBoundary | hjOuter
      · left; right
        rw [engelsmaGridCellUnion, Set.mem_iUnion]
        exact ⟨j, Set.mem_iUnion_of_mem hjBoundary hxCell⟩
      · exact False.elim
          ((not_mem_fractionalSimplexOuterGridIndex_of_cell_simplex
            hxCell hx) hjOuter)

theorem volume_engelsmaCoordinateOneFaces :
    volume engelsmaCoordinateOneFaces = 0 := by
  rw [engelsmaCoordinateOneFaces]
  apply measure_iUnion_null
  intro i
  rw [MeasureTheory.volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin 105 => volume) i 1

end BoundedGaps.Maynard
