import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import PrimesRestrictedDigits.SieveAsymptotics.TypeIISignedStrictAffineCompiler
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Low central-small Proposition 6.1 base presentations

This file packages the independent affine walls of the pair and triple base sums in the low
central-small branch. The tuple orders are `![q, p]` and `![r, q, p]`; the remaining source
walls follow from these walls and the Proposition 6.1 carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137--138, and Section 6, p. 143,
especially Eq. (6.12).
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The three independent pair walls, in normalized-log order `![q, p]`. -/
def sectionSixFirstLowCentralSmallPairRegion
    (epsilon : Real) : Set (Fin 2 -> Real) :=
  {x | x 1 <= sectionSixThetaOne epsilon /\
    sectionSixThetaTwo epsilon < x 1 + x 0 /\
    x 1 + 2 * x 0 < 1 - sectionSixThetaOne epsilon}

/-- The inherited pair walls followed by the strict `r` floor, in
normalized-log order `![r, q, p]`. -/
def sectionSixFirstLowCentralSmallTripleRegion
    (epsilon : Real) : Set (Fin 3 -> Real) :=
  {x | x 2 <= sectionSixThetaOne epsilon /\
    sectionSixThetaTwo epsilon < x 2 + x 1 /\
    x 2 + 2 * x 1 < 1 - sectionSixThetaOne epsilon /\
    sectionSixThetaGap epsilon < x 0}

/-- The exact three-wall mixed presentation of the pair base region. -/
noncomputable def sectionSixFirstLowCentralSmallPairPresentation
    (epsilon : Real) :
    TypeIIAffineMixedPresentation
      (sectionSixFirstLowCentralSmallPairRegion epsilon) where
  constraintCount := 3
  normal := ![
    ![(0 : Real), 1],
    ![(-1 : Real), -1],
    ![(2 : Real), 1]]
  bound := ![
    sectionSixThetaOne epsilon,
    -sectionSixThetaTwo epsilon,
    1 - sectionSixThetaOne epsilon]
  isStrict := ![false, true, true]
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hpCap, hcentral, hsquare⟩ c
      fin_cases c <;>
        simp [typeIIAffineValue, Fin.sum_univ_two] <;>
        linarith
    · intro h
      have hpCap := h (0 : Fin 3)
      have hcentral := h (1 : Fin 3)
      have hsquare := h (2 : Fin 3)
      change typeIIAffineValue ![(0 : Real), 1] x <=
          sectionSixThetaOne epsilon at hpCap
      change typeIIAffineValue ![(-1 : Real), -1] x <
          -sectionSixThetaTwo epsilon at hcentral
      change typeIIAffineValue ![(2 : Real), 1] x <
          1 - sectionSixThetaOne epsilon at hsquare
      simp [sectionSixFirstLowCentralSmallPairRegion, typeIIAffineValue,
        Fin.sum_univ_two] at hpCap hcentral hsquare ⊢
      exact ⟨by linarith, by linarith, by linarith⟩

/-- The exact four-wall mixed presentation of the triple base region. -/
noncomputable def sectionSixFirstLowCentralSmallTriplePresentation
    (epsilon : Real) :
    TypeIIAffineMixedPresentation
      (sectionSixFirstLowCentralSmallTripleRegion epsilon) where
  constraintCount := 4
  normal := ![
    ![(0 : Real), 0, 1],
    ![(0 : Real), -1, -1],
    ![(0 : Real), 2, 1],
    ![(-1 : Real), 0, 0]]
  bound := ![
    sectionSixThetaOne epsilon,
    -sectionSixThetaTwo epsilon,
    1 - sectionSixThetaOne epsilon,
    -sectionSixThetaGap epsilon]
  isStrict := ![false, true, true, true]
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hpCap, hcentral, hsquare, hrFloor⟩ c
      fin_cases c <;>
        simp [typeIIAffineValue, Fin.sum_univ_succ] <;>
        linarith
    · intro h
      have hpCap := h (0 : Fin 4)
      have hcentral := h (1 : Fin 4)
      have hsquare := h (2 : Fin 4)
      have hrFloor := h (3 : Fin 4)
      change typeIIAffineValue ![(0 : Real), 0, 1] x <=
          sectionSixThetaOne epsilon at hpCap
      change typeIIAffineValue ![(0 : Real), -1, -1] x <
          -sectionSixThetaTwo epsilon at hcentral
      change typeIIAffineValue ![(0 : Real), 2, 1] x <
          1 - sectionSixThetaOne epsilon at hsquare
      change typeIIAffineValue ![(-1 : Real), 0, 0] x <
          -sectionSixThetaGap epsilon at hrFloor
      simp [sectionSixFirstLowCentralSmallTripleRegion, typeIIAffineValue,
        Fin.sum_univ_succ] at hpCap hcentral hsquare hrFloor ⊢
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end

end PrimesRestrictedDigits
