import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedGeometryD807
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1Piece0RowFamilyD871 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# transformed Piece0 row-family geometry

This file supplies a closed 256-row cover of the transformed Piece0 d-range. The rows may
overlap at adjacent endpoints; no integral or numerical conclusion is asserted.
-/

private abbrev d871D0 : Real :=
  sectionSixFirstLowCentralSmallI5P1D807D0

private abbrev d871Ds : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Ds

private def d871RowNode (i : Nat) : Real :=
  d871D0 + (i : Real) * (d871Ds - d871D0) / 256

def sectionSixFirstLowCentralSmallI5P1D871P0RowLower
    (i : Fin 256) : Real :=
  sectionSixFirstLowCentralSmallI5P1D807D0 +
    (i.1 : Real) *
      (sectionSixFirstLowCentralSmallI5P1D807Ds -
        sectionSixFirstLowCentralSmallI5P1D807D0) / 256

def sectionSixFirstLowCentralSmallI5P1D871P0RowUpper
    (i : Fin 256) : Real :=
  sectionSixFirstLowCentralSmallI5P1D807D0 +
    ((i.1 + 1 : Nat) : Real) *
      (sectionSixFirstLowCentralSmallI5P1D807Ds -
        sectionSixFirstLowCentralSmallI5P1D807D0) / 256

def sectionSixFirstLowCentralSmallI5P1D871P0RowSlab
    (i : Fin 256) : Set Real :=
  Set.Icc
    (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
    (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i)

def sectionSixFirstLowCentralSmallI5P1D871P0RowSet
    (i : Fin 256) : Set SectionSixP1AffineT :=
  sectionSixFirstLowCentralSmallI5P1D807Piece0 ∩
    {z | z.1.1.1 ∈
      sectionSixFirstLowCentralSmallI5P1D871P0RowSlab i}

private def d871RowSlabNat (i : Nat) : Set Real :=
  Set.Icc (d871RowNode i) (d871RowNode (i + 1))

private def d871RowPrefix : Nat → Set Real
  | 0 => d871RowSlabNat 0
  | n + 1 => d871RowPrefix n ∪ d871RowSlabNat (n + 1)

private theorem d871_width_nonneg : 0 <= (d871Ds - d871D0) / 256 := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, hD0, hDs, _, _⟩
  change 0 <=
    (sectionSixFirstLowCentralSmallI5P1D807Ds -
      sectionSixFirstLowCentralSmallI5P1D807D0) / 256
  rw [hD0, hDs]
  norm_num

private theorem d871RowNode_mono {i j : Nat} (hij : i <= j) :
    d871RowNode i <= d871RowNode j := by
  unfold d871RowNode
  have hcast : (i : Real) <= (j : Real) := by exact_mod_cast hij
  have hmul := mul_le_mul_of_nonneg_right hcast d871_width_nonneg
  linarith

private theorem d871RowNode_zero : d871RowNode 0 = d871D0 := by
  simp [d871RowNode]

private theorem d871RowNode_256 : d871RowNode 256 = d871Ds := by
  unfold d871RowNode
  ring

theorem sectionSixFirstLowCentralSmallI5P1D871_p0Row_endpoint_order
    (i : Fin 256) :
    sectionSixFirstLowCentralSmallI5P1D807D0 <=
        sectionSixFirstLowCentralSmallI5P1D871P0RowLower i ∧
      sectionSixFirstLowCentralSmallI5P1D871P0RowLower i <=
        sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i ∧
      sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i <=
        sectionSixFirstLowCentralSmallI5P1D807Ds := by
  have hi : i.1 + 1 <= 256 := by omega
  change d871D0 <= d871RowNode i.1 ∧
    d871RowNode i.1 <= d871RowNode (i.1 + 1) ∧
    d871RowNode (i.1 + 1) <= d871Ds
  rw [← d871RowNode_zero, ← d871RowNode_256]
  exact ⟨d871RowNode_mono (Nat.zero_le _),
    d871RowNode_mono (Nat.le_succ _), d871RowNode_mono hi⟩

private theorem d871RowPrefix_eq (n : Nat) :
    d871RowPrefix n = Set.Icc (d871RowNode 0) (d871RowNode (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [d871RowPrefix, ih]
      exact Set.Icc_union_Icc_eq_Icc
        (d871RowNode_mono (Nat.zero_le (n + 1)))
        (d871RowNode_mono (Nat.le_succ (n + 1)))

private theorem d871_mem_rowPrefix_iff {x : Real} (n : Nat) :
    x ∈ d871RowPrefix n ↔ ∃ i, i <= n ∧ x ∈ d871RowSlabNat i := by
  induction n with
  | zero =>
      constructor
      · intro hx
        exact ⟨0, le_rfl, hx⟩
      · rintro ⟨i, hi, hx⟩
        have : i = 0 := by omega
        simpa [d871RowPrefix, this] using hx
  | succ n ih =>
      rw [d871RowPrefix]
      constructor
      · intro hx
        rcases hx with hx | hx
        · rcases ih.mp hx with ⟨i, hi, hxi⟩
          exact ⟨i, hi.trans (Nat.le_succ n), hxi⟩
        · exact ⟨n + 1, le_rfl, hx⟩
      · rintro ⟨i, hi, hxi⟩
        by_cases hin : i <= n
        · exact Or.inl (ih.mpr ⟨i, hin, hxi⟩)
        · have hieq : i = n + 1 := by omega
          exact Or.inr (hieq ▸ hxi)

theorem sectionSixFirstLowCentralSmallI5P1D871_p0RowSlabs_cover :
    (⋃ i : Fin 256,
      sectionSixFirstLowCentralSmallI5P1D871P0RowSlab i) =
      Set.Icc sectionSixFirstLowCentralSmallI5P1D807D0
        sectionSixFirstLowCentralSmallI5P1D807Ds := by
  have hslab (i : Fin 256) :
      sectionSixFirstLowCentralSmallI5P1D871P0RowSlab i =
        d871RowSlabNat i.1 := by
    rfl
  change (⋃ i : Fin 256,
      sectionSixFirstLowCentralSmallI5P1D871P0RowSlab i) =
    Set.Icc d871D0 d871Ds
  rw [← d871RowNode_zero, ← d871RowNode_256,
    ← d871RowPrefix_eq 255]
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    apply (d871_mem_rowPrefix_iff 255).mpr
    exact ⟨i.1, by omega, hslab i ▸ hi⟩
  · intro hx
    rcases (d871_mem_rowPrefix_iff 255).mp hx with ⟨i, hi, hxi⟩
    have hil : i < 256 := by omega
    exact Set.mem_iUnion.mpr
      ⟨⟨i, hil⟩, (hslab ⟨i, hil⟩).symm ▸ hxi⟩

theorem sectionSixFirstLowCentralSmallI5P1D871_piece0_eq_rowUnion :
    sectionSixFirstLowCentralSmallI5P1D807Piece0 =
      ⋃ i : Fin 256,
        sectionSixFirstLowCentralSmallI5P1D871P0RowSet i := by
  ext z
  constructor
  · intro hz
    have hd : z.1.1.1 ∈ Set.Icc d871D0 d871Ds := hz.1
    rw [← sectionSixFirstLowCentralSmallI5P1D871_p0RowSlabs_cover] at hd
    rcases Set.mem_iUnion.mp hd with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hz, hi⟩
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    exact hi.1



end
end PrimesRestrictedDigits
