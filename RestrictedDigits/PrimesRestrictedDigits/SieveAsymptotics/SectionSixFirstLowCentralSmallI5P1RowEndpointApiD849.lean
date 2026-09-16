import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowSlabFamilyD846
/-! # SectionSixFirstLowCentralSmallI5P1RowEndpointApiD849 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
namespace PrimesRestrictedDigits
noncomputable section

/-!
# public endpoint aliases for the closed Piece1 row family

These definitions expose the affine endpoints used privately. The equalities below are
set-theoretic unfoldings only; closed rows intentionally overlap at adjacent endpoints, and no
analytic decomposition is asserted.
-/

def sectionSixFirstLowCentralSmallI5P1D849RowLower (i : Fin 256) : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Ds +
    (i.1 : Real) *
      (sectionSixFirstLowCentralSmallI5P1D807Dr -
        sectionSixFirstLowCentralSmallI5P1D807Ds) / 256

def sectionSixFirstLowCentralSmallI5P1D849RowUpper (i : Fin 256) : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Ds +
    ((i.1 + 1 : Nat) : Real) *
      (sectionSixFirstLowCentralSmallI5P1D807Dr -
        sectionSixFirstLowCentralSmallI5P1D807Ds) / 256

theorem sectionSixFirstLowCentralSmallI5P1D849_rowSlab_eq_Icc
    (i : Fin 256) :
    sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i =
      Set.Icc
        (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
        (sectionSixFirstLowCentralSmallI5P1D849RowUpper i) := by
  rfl

theorem sectionSixFirstLowCentralSmallI5P1D849_rowSet_eq_inter_preimage
    (i : Fin 256) :
    sectionSixFirstLowCentralSmallI5P1D846P1RowSet i =
      sectionSixFirstLowCentralSmallI5P1D807Piece1 ∩
        {z | z.1.1.1 ∈ Set.Icc
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
          (sectionSixFirstLowCentralSmallI5P1D849RowUpper i)} := by
  rfl


end
end PrimesRestrictedDigits
