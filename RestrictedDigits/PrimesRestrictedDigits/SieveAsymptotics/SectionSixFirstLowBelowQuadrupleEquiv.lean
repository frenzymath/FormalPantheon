import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowBelowIndices

/-!
# Nested equivalence for the low-below clean quadruple carrier

This module fixes the recurrence-native left-associated role order `(((p, q), r), s)` used by
the exact finite carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.13), region `R_4`.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The recurrence-native quadruple roles in their literal nested order. -/
def sectionSixFirstLowBelowQuadrupleNestedEquiv :
    SectionSixFirstLowBelowQuadrupleIndex ≃
      (((Nat × Nat) × Nat) × Nat) where
  toFun index :=
    (((index.1.1.1, index.1.1.2), index.1.2), index.2)
  invFun quadruple :=
    ⟨⟨⟨quadruple.1.1.1, quadruple.1.1.2⟩, quadruple.1.2⟩,
      quadruple.2⟩
  left_inv index := by
    rcases index with ⟨⟨⟨p, q⟩, r⟩, s⟩
    rfl
  right_inv quadruple := by
    rcases quadruple with ⟨⟨⟨p, q⟩, r⟩, s⟩
    rfl

end

end PrimesRestrictedDigits
