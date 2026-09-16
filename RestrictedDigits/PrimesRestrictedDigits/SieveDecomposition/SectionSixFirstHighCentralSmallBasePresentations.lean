import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import PrimesRestrictedDigits.SieveAsymptotics.TypeIISignedStrictAffineCompiler
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# High central-small Proposition 6.1 base presentations

This file packages the independent affine walls of the pair and triple base sums in the high
central-small branch. The tuple orders are `![q, p]` and `![r, q, p]`; the remaining source
walls are consequences of the Proposition 6.1 carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137--138, and the `S3` decomposition,
pp. 145--146, especially Eq. (6.16).
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The four independent pair walls, in normalized-log order `![q, p]`. -/
def sectionSixFirstHighCentralSmallPairRegion
    (epsilon : Real) : Set (Fin 2 -> Real) :=
  {x | sectionSixThetaGap epsilon < x 0 ∧
    sectionSixThetaTwo epsilon < x 1 ∧
    x 1 <= (1 / 2 : Real) ∧
    x 1 + 2 * x 0 < 1 - sectionSixThetaOne epsilon}

/-- The four independent triple walls, in normalized-log order
`![r, q, p]`. -/
def sectionSixFirstHighCentralSmallTripleRegion
    (epsilon : Real) : Set (Fin 3 -> Real) :=
  {x | sectionSixThetaGap epsilon < x 0 ∧
    sectionSixThetaTwo epsilon < x 2 ∧
    x 2 <= (1 / 2 : Real) ∧
    x 2 + 2 * x 1 < 1 - sectionSixThetaOne epsilon}

/-- The exact four-wall mixed presentation of the pair base region. -/
noncomputable def sectionSixFirstHighCentralSmallPairPresentation
    (epsilon : Real) :
    TypeIIAffineMixedPresentation
      (sectionSixFirstHighCentralSmallPairRegion epsilon) where
  constraintCount := 4
  normal := ![
    ![(-1 : Real), 0],
    ![0, (-1 : Real)],
    ![0, (1 : Real)],
    ![(2 : Real), 1]]
  bound := ![
    -sectionSixThetaGap epsilon,
    -sectionSixThetaTwo epsilon,
    (1 / 2 : Real),
    1 - sectionSixThetaOne epsilon]
  isStrict := ![true, true, false, true]
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hq, hp, hpHalf, hsquare⟩ c
      fin_cases c <;>
        simp [typeIIAffineValue, Fin.sum_univ_two] <;>
        linarith
    · intro h
      have hq := h (0 : Fin 4)
      have hp := h (1 : Fin 4)
      have hpHalf := h (2 : Fin 4)
      have hsquare := h (3 : Fin 4)
      change typeIIAffineValue ![(-1 : Real), 0] x <
          -sectionSixThetaGap epsilon at hq
      change typeIIAffineValue ![0, (-1 : Real)] x <
          -sectionSixThetaTwo epsilon at hp
      change typeIIAffineValue ![0, (1 : Real)] x <=
          (1 / 2 : Real) at hpHalf
      change typeIIAffineValue ![(2 : Real), 1] x <
          1 - sectionSixThetaOne epsilon at hsquare
      simp [sectionSixFirstHighCentralSmallPairRegion, typeIIAffineValue,
        Fin.sum_univ_two] at hq hp hpHalf hsquare ⊢
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The exact four-wall mixed presentation of the triple base region. -/
noncomputable def sectionSixFirstHighCentralSmallTriplePresentation
    (epsilon : Real) :
    TypeIIAffineMixedPresentation
      (sectionSixFirstHighCentralSmallTripleRegion epsilon) where
  constraintCount := 4
  normal := ![
    ![(-1 : Real), 0, 0],
    ![0, 0, (-1 : Real)],
    ![0, 0, (1 : Real)],
    ![0, (2 : Real), 1]]
  bound := ![
    -sectionSixThetaGap epsilon,
    -sectionSixThetaTwo epsilon,
    (1 / 2 : Real),
    1 - sectionSixThetaOne epsilon]
  isStrict := ![true, true, false, true]
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hr, hp, hpHalf, hsquare⟩ c
      fin_cases c <;>
        simp [typeIIAffineValue, Fin.sum_univ_succ] <;>
        linarith
    · intro h
      have hr := h (0 : Fin 4)
      have hp := h (1 : Fin 4)
      have hpHalf := h (2 : Fin 4)
      have hsquare := h (3 : Fin 4)
      change typeIIAffineValue ![(-1 : Real), 0, 0] x <
          -sectionSixThetaGap epsilon at hr
      change typeIIAffineValue ![0, 0, (-1 : Real)] x <
          -sectionSixThetaTwo epsilon at hp
      change typeIIAffineValue ![0, 0, (1 : Real)] x <=
          (1 / 2 : Real) at hpHalf
      change typeIIAffineValue ![0, (2 : Real), 1] x <
          1 - sectionSixThetaOne epsilon at hsquare
      simp [sectionSixFirstHighCentralSmallTripleRegion, typeIIAffineValue,
        Fin.sum_univ_succ] at hr hp hpHalf hsquare ⊢
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end

end PrimesRestrictedDigits
