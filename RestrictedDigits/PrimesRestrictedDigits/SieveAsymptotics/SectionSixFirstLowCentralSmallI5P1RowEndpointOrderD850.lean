import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowEndpointApiD849
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
/-! # SectionSixFirstLowCentralSmallI5P1RowEndpointOrderD850 -/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits
noncomputable section

/-!
# order arithmetic for the closed Piece1 row endpoints

The six public facts below provide only weak endpoint order, monotonicity, and the
neighboring-node identity. rows remain closed and overlapping; no partition or analytic
conclusion is asserted here.
-/

private theorem d850_width_nonneg :
    0 ≤ (sectionSixFirstLowCentralSmallI5P1D807Dr -
      sectionSixFirstLowCentralSmallI5P1D807Ds) / 256 := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, hds, hdr, _⟩
  rw [hds, hdr]
  norm_num

private theorem d850_node_mono {i j : Fin 256} (hij : i.1 ≤ j.1) :
    sectionSixFirstLowCentralSmallI5P1D849RowLower i ≤
      sectionSixFirstLowCentralSmallI5P1D849RowLower j := by
  unfold sectionSixFirstLowCentralSmallI5P1D849RowLower
  have hcast : (i.1 : Real) ≤ (j.1 : Real) := by exact_mod_cast hij
  have hmul := mul_le_mul_of_nonneg_right hcast d850_width_nonneg
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D850_row_lower_le_upper
    (i : Fin 256) :
    sectionSixFirstLowCentralSmallI5P1D849RowLower i ≤
      sectionSixFirstLowCentralSmallI5P1D849RowUpper i := by
  unfold sectionSixFirstLowCentralSmallI5P1D849RowLower
    sectionSixFirstLowCentralSmallI5P1D849RowUpper
  have hcast : (i.1 : Real) ≤ ((i.1 + 1 : Nat) : Real) := by
    exact_mod_cast (Nat.le_succ i.1)
  have hmul := mul_le_mul_of_nonneg_right hcast d850_width_nonneg
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D850_ds_le_row_lower
    (i : Fin 256) :
    sectionSixFirstLowCentralSmallI5P1D807Ds ≤
      sectionSixFirstLowCentralSmallI5P1D849RowLower i := by
  unfold sectionSixFirstLowCentralSmallI5P1D849RowLower
  have hi : (0 : Real) ≤ (i.1 : Real) := by positivity
  have hmul := mul_nonneg hi d850_width_nonneg
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D850_row_upper_le_dr
    (i : Fin 256) :
    sectionSixFirstLowCentralSmallI5P1D849RowUpper i ≤
      sectionSixFirstLowCentralSmallI5P1D807Dr := by
  unfold sectionSixFirstLowCentralSmallI5P1D849RowUpper
  have hi : (i.1 + 1 : Nat) ≤ 256 := by omega
  have hcast : ((i.1 + 1 : Nat) : Real) ≤ (256 : Real) := by
    exact_mod_cast hi
  have hmul := mul_le_mul_of_nonneg_right hcast d850_width_nonneg
  nlinarith [hmul]

theorem sectionSixFirstLowCentralSmallI5P1D850_row_lower_mono
    {i j : Fin 256} (hij : i.1 ≤ j.1) :
    sectionSixFirstLowCentralSmallI5P1D849RowLower i ≤
      sectionSixFirstLowCentralSmallI5P1D849RowLower j :=
  d850_node_mono hij

theorem sectionSixFirstLowCentralSmallI5P1D850_row_upper_mono
    {i j : Fin 256} (hij : i.1 ≤ j.1) :
    sectionSixFirstLowCentralSmallI5P1D849RowUpper i ≤
      sectionSixFirstLowCentralSmallI5P1D849RowUpper j := by
  unfold sectionSixFirstLowCentralSmallI5P1D849RowUpper
  have hcast : ((i.1 + 1 : Nat) : Real) ≤ ((j.1 + 1 : Nat) : Real) := by
    exact_mod_cast (Nat.add_le_add_right hij 1)
  have hmul := mul_le_mul_of_nonneg_right hcast d850_width_nonneg
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D850_adjacent
    {i : Fin 256} (hi : i.1 < 255) :
    sectionSixFirstLowCentralSmallI5P1D849RowUpper i =
      sectionSixFirstLowCentralSmallI5P1D849RowLower ⟨i.1 + 1, by omega⟩ := by
  unfold sectionSixFirstLowCentralSmallI5P1D849RowUpper
    sectionSixFirstLowCentralSmallI5P1D849RowLower
  rfl


end
end PrimesRestrictedDigits
