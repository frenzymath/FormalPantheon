import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import PrimesRestrictedDigits.SieveAsymptotics.TypeIISignedStrictAffineCompiler
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Section 6 first-term low-central-large continuation-band presentation

This file packages the three affine walls of the closed `q * r` continuation band from the
first Buchstab term as a mixed strict/weak Type-II presentation.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, especially Eq. (6.8), the following
continuation display, and the paragraph before Eqs. (6.10)--(6.11). The Type-II input is
Proposition 6.2, pp. 137--138.
-/

namespace PrimesRestrictedDigits

open Set

noncomputable section

/-- The three source-facing affine walls for the low-central-large closed
continuation band, in the coordinate order `(q, r, p)`. -/
def sectionSixFirstLowCentralLargeBandRegion
    (epsilon : Real) : Set (Fin 3 -> Real) :=
  {x | x 0 < x 1 ∧
    x 2 <= sectionSixThetaOne epsilon ∧
    1 - sectionSixThetaOne epsilon <= x 2 + 2 * x 0}

/-- The exact three-wall mixed-affine presentation of
`sectionSixFirstLowCentralLargeBandRegion`. -/
noncomputable def sectionSixFirstLowCentralLargeBandPresentation
    (epsilon : Real) :
    TypeIIAffineMixedPresentation
      (sectionSixFirstLowCentralLargeBandRegion epsilon) where
  constraintCount := 3
  normal := ![
    ![(1 : Real), -1, 0],
    ![0, 0, (1 : Real)],
    ![(-2 : Real), 0, -1]]
  bound := ![
    (0 : Real),
    sectionSixThetaOne epsilon,
    -(1 - sectionSixThetaOne epsilon)]
  isStrict := ![true, false, false]
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hqr, hp, hsquare⟩ c
      fin_cases c <;>
        simp [typeIIAffineValue, Fin.sum_univ_succ] <;>
        linarith
    · intro h
      have hqr := h (0 : Fin 3)
      have hp := h (1 : Fin 3)
      have hsquare := h (2 : Fin 3)
      change typeIIAffineValue ![(1 : Real), -1, 0] x < 0 at hqr
      change typeIIAffineValue ![0, 0, (1 : Real)] x <=
        sectionSixThetaOne epsilon at hp
      change typeIIAffineValue ![(-2 : Real), 0, -1] x <=
        -(1 - sectionSixThetaOne epsilon) at hsquare
      simp [sectionSixFirstLowCentralLargeBandRegion, typeIIAffineValue,
        Fin.sum_univ_succ] at hqr hp hsquare ⊢
      exact ⟨by linarith, by linarith, by linarith⟩

end

end PrimesRestrictedDigits
