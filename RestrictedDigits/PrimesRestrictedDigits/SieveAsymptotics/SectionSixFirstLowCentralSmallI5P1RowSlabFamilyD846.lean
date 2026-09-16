import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1SelectedRowKernelCompositionD845
/-! # SectionSixFirstLowCentralSmallI5P1RowSlabFamilyD846 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# parameterized closed Piece1 row-slab geometry

The 256 closed d-slabs cover the Piece1 d interval, and the induced row-family union is
exactly Piece1. Index 1 is identified with the closed row. This module is set-theoretic
infrastructure only: adjacent closed slabs overlap at endpoints, and no analytic estimate or
integral decomposition is asserted.
-/

private def d846RowNode (i : Nat) : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Ds +
    (i : Real) *
      (sectionSixFirstLowCentralSmallI5P1D807Dr -
        sectionSixFirstLowCentralSmallI5P1D807Ds) / 256

private def d846RowSlabNat (i : Nat) : Set Real :=
  Set.Icc (d846RowNode i) (d846RowNode (i + 1))

def sectionSixFirstLowCentralSmallI5P1D846P1RowSlab
    (i : Fin 256) : Set Real :=
  d846RowSlabNat i.1

def sectionSixFirstLowCentralSmallI5P1D846P1RowSet
    (i : Fin 256) : Set SectionSixP1AffineT :=
  sectionSixFirstLowCentralSmallI5P1D807Piece1 ∩
    {z | z.1.1.1 ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i}

private def d846RowPrefix : Nat → Set Real
  | 0 => d846RowSlabNat 0
  | n + 1 => d846RowPrefix n ∪ d846RowSlabNat (n + 1)

private theorem d846RowNode_mono {i j : Nat} (hij : i ≤ j) :
    d846RowNode i ≤ d846RowNode j := by
  have hwidth :
      0 ≤ (sectionSixFirstLowCentralSmallI5P1D807Dr -
        sectionSixFirstLowCentralSmallI5P1D807Ds) / 256 := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, _, _, hds, hdr, _⟩
    rw [hds, hdr]
    norm_num
  unfold d846RowNode
  have hcast : (i : Real) ≤ (j : Real) := by exact_mod_cast hij
  have hmul := mul_le_mul_of_nonneg_right hcast hwidth
  nlinarith

private theorem d846RowPrefix_eq (n : Nat) :
    d846RowPrefix n = Set.Icc (d846RowNode 0) (d846RowNode (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [d846RowPrefix, ih]
      exact Set.Icc_union_Icc_eq_Icc
        (d846RowNode_mono (Nat.zero_le (n + 1)))
        (d846RowNode_mono (Nat.le_succ (n + 1)))

private theorem d846_mem_rowPrefix_iff {x : Real} (n : Nat) :
    x ∈ d846RowPrefix n ↔ ∃ i, i ≤ n ∧ x ∈ d846RowSlabNat i := by
  induction n with
  | zero =>
      constructor
      · intro hx
        exact ⟨0, le_rfl, hx⟩
      · rintro ⟨i, hi, hx⟩
        have : i = 0 := by omega
        simpa [d846RowPrefix, this] using hx
  | succ n ih =>
      rw [d846RowPrefix]
      constructor
      · intro hx
        rcases hx with hx | hx
        · rcases (ih.mp hx) with ⟨i, hi, hxi⟩
          exact ⟨i, hi.trans (Nat.le_succ n), hxi⟩
        · exact ⟨n + 1, le_rfl, hx⟩
      · rintro ⟨i, hi, hxi⟩
        by_cases hin : i ≤ n
        · exact Or.inl (ih.mpr ⟨i, hin, hxi⟩)
        · have hieq : i = n + 1 := by omega
          exact Or.inr (hieq ▸ hxi)

private theorem d846RowNode_zero :
    d846RowNode 0 = sectionSixFirstLowCentralSmallI5P1D807Ds := by
  simp [d846RowNode]

private theorem d846RowNode_256 :
    d846RowNode 256 = sectionSixFirstLowCentralSmallI5P1D807Dr := by
  ring_nf
  simp [d846RowNode]

theorem sectionSixFirstLowCentralSmallI5P1D846_p1RowSlabs_cover :
    (⋃ i : Fin 256, sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i) =
      Set.Icc sectionSixFirstLowCentralSmallI5P1D807Ds
        sectionSixFirstLowCentralSmallI5P1D807Dr := by
  rw [← d846RowNode_zero, ← d846RowNode_256,
    ← d846RowPrefix_eq 255]
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    apply (d846_mem_rowPrefix_iff 255).mpr
    exact ⟨i.1, by omega, hi⟩
  · intro hx
    rcases (d846_mem_rowPrefix_iff 255).mp hx with ⟨i, hi, hxi⟩
    have hil : i < 256 := by omega
    exact Set.mem_iUnion.mpr ⟨⟨i, hil⟩, hxi⟩

theorem sectionSixFirstLowCentralSmallI5P1D846_piece1_eq_rowUnion :
    sectionSixFirstLowCentralSmallI5P1D807Piece1 =
      ⋃ i : Fin 256, sectionSixFirstLowCentralSmallI5P1D846P1RowSet i := by
  ext z
  constructor
  · intro hz
    have hd : z.1.1.1 ∈ Set.Icc
        sectionSixFirstLowCentralSmallI5P1D807Ds
        sectionSixFirstLowCentralSmallI5P1D807Dr := hz.1
    rw [← sectionSixFirstLowCentralSmallI5P1D846_p1RowSlabs_cover] at hd
    rcases Set.mem_iUnion.mp hd with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hz, hi⟩
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    exact hi.1

private theorem d846RowNode_one_eq_d838 :
    d846RowNode 1 =
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, hds, hdr, _⟩
  unfold d846RowNode
  rw [hds, hdr]
  norm_num [d846RowNode,
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower,
    sectionSixFirstLowCentralSmallI5P1D807Ds,
    sectionSixFirstLowCentralSmallI5P1D807Dr]

private theorem d846RowNode_two_eq_d838 :
    d846RowNode 2 =
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, hds, hdr, _⟩
  unfold d846RowNode
  rw [hds, hdr]
  norm_num [d846RowNode,
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
    sectionSixFirstLowCentralSmallI5P1D807Ds,
    sectionSixFirstLowCentralSmallI5P1D807Dr]

theorem sectionSixFirstLowCentralSmallI5P1D846_rowOne_eq_d838 :
    sectionSixFirstLowCentralSmallI5P1D846P1RowSet ⟨1, by omega⟩ =
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Set := by
  ext z
  simp only [sectionSixFirstLowCentralSmallI5P1D846P1RowSet,
    sectionSixFirstLowCentralSmallI5P1D846P1RowSlab,
    d846RowSlabNat, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_Icc, sectionSixFirstLowCentralSmallI5P1D838P1Row1Set,
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab]
  rw [d846RowNode_one_eq_d838, d846RowNode_two_eq_d838]



end
end PrimesRestrictedDigits
