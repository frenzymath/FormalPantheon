import BoundedGaps.Maynard.ConcreteSimplexInnerGridDisjoint

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

theorem biUnion_range_adjacent_sdiff_eq_sdiff
    {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (m : ℕ)
    (hmono : ∀ j < m, S j ⊆ S (j + 1)) :
    (Finset.range m).biUnion (fun j => S (j + 1) \ S j) =
      S m \ S 0 := by
  revert hmono
  induction m with
  | zero => intro hmono; simp
  | succ m ih =>
    intro hmono
    have hrange : Finset.range (Nat.succ m) = insert m (Finset.range m) := by
      ext j
      simp only [Finset.mem_range, Finset.mem_insert]
      omega
    have hmono' : ∀ j < m, S j ⊆ S (j + 1) := by
      intro j hj
      exact hmono j (lt_trans hj (Nat.lt_succ_self m))
    rw [hrange, Finset.biUnion_insert, ih hmono']
    have hbase : S 0 ⊆ S m := by
      have hchain : ∀ k, k ≤ m → S 0 ⊆ S k := by
        intro k
        induction k with
        | zero => intro; exact Finset.Subset.rfl
        | succ k ih =>
          intro hk
          have hk' : k ≤ m := Nat.le_trans (Nat.le_of_succ_le hk) (Nat.le_refl m)
          exact Finset.Subset.trans (ih hk')
            (hmono k (Nat.lt_succ_of_le hk'))
      exact hchain m (Nat.le_refl m)
    exact Finset.sdiff_union_sdiff_cancel
      (hmono m (Nat.lt_succ_self m)) hbase

def fractionalGridPoint (m j : ℕ) : ℝ := (j : ℝ) / m

def engelsmaFractionalCoordinateGridShellUnion
    (W : ℕ) (alpha : ℝ) (m N : ℕ) : Finset ℕ :=
  (Finset.range m).biUnion fun j =>
    squarefreeCoprimeCoordinateShell W
      (engelsmaMaynardRadius (alpha * fractionalGridPoint m j) N)
      (engelsmaMaynardRadius (alpha * fractionalGridPoint m (j + 1)) N)

theorem eventually_engelsmaFractionalCoordinateGridShellUnion_eq
    {alpha : ℝ} (halpha : 0 < alpha) {m : ℕ} (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaFractionalCoordinateGridShellUnion
          (engelsmaMaynardModulus N) alpha m N =
        squarefreeCoprimeCoordinateSupport
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) \
        squarefreeCoprimeCoordinateSupport
          (engelsmaMaynardModulus N) 1 := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hradius : ∀ a b : ℝ, a ≤ b →
      engelsmaMaynardRadius a N ≤ engelsmaMaynardRadius b N := by
    intro a b hab
    unfold engelsmaMaynardRadius maynardDivisorCutoff
    apply Nat.floor_mono
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (show 1 ≤ N - 1 by omega)
    · exact hab
  have hmono : ∀ j < m,
      squarefreeCoprimeCoordinateSupport
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius
            (alpha * fractionalGridPoint m j) N) ⊆
        squarefreeCoprimeCoordinateSupport
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius
            (alpha * fractionalGridPoint m (j + 1)) N) := by
    intro j hj
    apply squarefreeCoprimeCoordinateSupport_subset
    apply hradius
    apply mul_le_mul_of_nonneg_left _ halpha.le
    unfold fractionalGridPoint
    apply (div_le_div_iff_of_pos_right (by exact_mod_cast hm)).2
    exact_mod_cast Nat.le_succ j
  unfold engelsmaFractionalCoordinateGridShellUnion
    squarefreeCoprimeCoordinateShell
  rw [
    biUnion_range_adjacent_sdiff_eq_sdiff _ _ hmono]
  · congr 2
    · unfold fractionalGridPoint
      field_simp [hm.ne']
    · simp [fractionalGridPoint, engelsmaMaynardRadius,
        maynardDivisorCutoff]

def engelsmaFractionalTupleGridShellUnion
    (H : Finset ℕ) (alpha : ℝ) (m N : ℕ) : Finset (H → ℕ) :=
  (fractionalGridIndex H m).biUnion fun j =>
    engelsmaFractionalTupleShell H alpha
      (fractionalGridLower m j) (fractionalGridUpper m j) N

theorem mem_engelsmaFractionalTupleGridShellUnion_of_coordinate_mem
    {H : Finset ℕ} {alpha : ℝ} {m N : ℕ} {u : H → ℕ}
    (hu : ∀ h : H,
      u h ∈ engelsmaFractionalCoordinateGridShellUnion
        (engelsmaMaynardModulus N) alpha m N) :
    u ∈ engelsmaFractionalTupleGridShellUnion H alpha m N := by
  have hex : ∀ h : H, ∃ j : ℕ, j < m ∧
      u h ∈ squarefreeCoprimeCoordinateShell
        (engelsmaMaynardModulus N)
        (engelsmaMaynardRadius
          (alpha * fractionalGridPoint m j) N)
        (engelsmaMaynardRadius
          (alpha * fractionalGridPoint m (j + 1)) N) := by
    intro h
    have hh := hu h
    rw [engelsmaFractionalCoordinateGridShellUnion,
      Finset.mem_biUnion] at hh
    obtain ⟨j, hj, hjmem⟩ := hh
    exact ⟨j, Finset.mem_range.mp hj, hjmem⟩
  choose j hj hmem using hex
  have hjGrid : j ∈ fractionalGridIndex H m := by
    rw [fractionalGridIndex, Fintype.mem_piFinset]
    intro h
    exact Finset.mem_range.mpr (hj h)
  apply Finset.mem_biUnion.mpr
  refine ⟨j, hjGrid, ?_⟩
  rw [engelsmaFractionalTupleShell, squarefreeCoprimeTupleShell,
    Fintype.mem_piFinset]
  intro h
  simpa [fractionalGridLower, fractionalGridUpper, fractionalGridPoint] using
    hmem h

theorem eventually_preSievedSimplexTupleSupport_mem_gridShellUnion_of_no_unit
    {H : Finset ℕ} {alpha : ℝ} {m : ℕ}
    (halpha : 0 < alpha) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ u : H → ℕ,
      u ∈ preSievedSimplexTupleSupport H
          (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) →
      (∀ h : H, u h ≠ 1) →
      u ∈ engelsmaFractionalTupleGridShellUnion H alpha m N := by
  have hgrid := eventually_engelsmaFractionalCoordinateGridShellUnion_eq
    (alpha := alpha) halpha hm
  filter_upwards [hgrid] with N hgridN u hu hunit
  apply mem_engelsmaFractionalTupleGridShellUnion_of_coordinate_mem
  intro h
  rw [hgridN]
  apply Finset.mem_sdiff.mpr
  constructor
  · have huCommon := (mem_preSievedSimplexTupleSupport_iff.mp hu).1
    have huh := Fintype.mem_piFinset.mp huCommon h
    have huhData := Finset.mem_filter.mp huh
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (preSievedSimplexTupleSupport_coordinate hu h).1.ne',
          (Finset.mem_range.mp huhData.1).le⟩
    · exact huhData.2.2
  · intro huOne
    have huOneData := Finset.mem_filter.mp huOne
    have huOneIcc := Finset.mem_Icc.mp huOneData.1
    exact hunit h (by omega)

theorem eventually_preSievedSimplexTupleSupport_mem_gridShellUnion_or_unit
    {H : Finset ℕ} {alpha : ℝ} {m : ℕ}
    (halpha : 0 < alpha) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ u : H → ℕ,
      u ∈ preSievedSimplexTupleSupport H
          (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) →
      u ∈ engelsmaFractionalTupleGridShellUnion H alpha m N ∨
        ∃ h : H, u h = 1 := by
  have hcover := eventually_preSievedSimplexTupleSupport_mem_gridShellUnion_of_no_unit
    (H := H) halpha hm
  filter_upwards [hcover] with N hcover u hu
  by_cases hunit : ∀ h : H, u h ≠ 1
  · exact Or.inl (hcover u hu hunit)
  · obtain ⟨h, hh⟩ := not_forall.mp hunit
    exact Or.inr ⟨h, not_ne_iff.mp hh⟩

def fractionalSimplexBoundaryGridIndex (H : Finset ℕ) (m : ℕ) :
    Finset (H → ℕ) :=
  (fractionalGridIndex H m).filter fun j =>
    (∑ h : H, fractionalGridLower m j h) ≤ 1 ∧
      1 ≤ ∑ h : H, fractionalGridUpper m j h

def fractionalSimplexOuterGridIndex (H : Finset ℕ) (m : ℕ) :
    Finset (H → ℕ) :=
  (fractionalGridIndex H m).filter fun j =>
    1 < ∑ h : H, fractionalGridLower m j h

theorem fractionalGridIndex_eq_inner_union_boundary_union_outer
    (H : Finset ℕ) (m : ℕ) :
    fractionalGridIndex H m =
      fractionalSimplexInnerGridIndex H m ∪
        (fractionalSimplexBoundaryGridIndex H m ∪
          fractionalSimplexOuterGridIndex H m) := by
  ext j
  constructor
  · intro hj
    by_cases hinner : ∑ h : H, fractionalGridUpper m j h < 1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hj, hinner⟩))
    · by_cases houter : 1 < ∑ h : H, fractionalGridLower m j h
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_union.mpr
            (Or.inr (Finset.mem_filter.mpr ⟨hj, houter⟩))))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_union.mpr
            (Or.inl (Finset.mem_filter.mpr
              ⟨hj, ⟨le_of_not_gt houter, le_of_not_gt hinner⟩⟩))))
  · intro hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact (Finset.mem_filter.mp hj).1
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact (Finset.mem_filter.mp hj).1
      · exact (Finset.mem_filter.mp hj).1

theorem disjoint_fractionalSimplexInnerGridIndex_boundary
    (H : Finset ℕ) (m : ℕ) :
    Disjoint (fractionalSimplexInnerGridIndex H m)
      (fractionalSimplexBoundaryGridIndex H m) := by
  apply Finset.disjoint_left.mpr
  intro j hjInner hjBoundary
  have hinner := (Finset.mem_filter.mp hjInner).2
  have hboundary := (Finset.mem_filter.mp hjBoundary).2
  linarith

theorem disjoint_fractionalSimplexInnerGridIndex_outer
    (H : Finset ℕ) (m : ℕ) :
    Disjoint (fractionalSimplexInnerGridIndex H m)
      (fractionalSimplexOuterGridIndex H m) := by
  apply Finset.disjoint_left.mpr
  intro j hjInner hjOuter
  have hinner := (Finset.mem_filter.mp hjInner).2
  have houter := (Finset.mem_filter.mp hjOuter).2
  have hupperLower : (∑ h : H, fractionalGridLower m j h) ≤
      ∑ h : H, fractionalGridUpper m j h := by
    apply Finset.sum_le_sum
    intro h hh
    unfold fractionalGridLower fractionalGridUpper
    by_cases hm : m = 0
    · simp [hm]
    · apply (div_le_div_iff_of_pos_right (by exact_mod_cast Nat.pos_of_ne_zero hm)).2
      exact_mod_cast Nat.le_succ (j h)
  linarith

theorem disjoint_fractionalSimplexBoundaryGridIndex_outer
    (H : Finset ℕ) (m : ℕ) :
    Disjoint (fractionalSimplexBoundaryGridIndex H m)
      (fractionalSimplexOuterGridIndex H m) := by
  apply Finset.disjoint_left.mpr
  intro j hjBoundary hjOuter
  have hboundary := (Finset.mem_filter.mp hjBoundary).2
  have houter := (Finset.mem_filter.mp hjOuter).2
  linarith

end BoundedGaps.Maynard
