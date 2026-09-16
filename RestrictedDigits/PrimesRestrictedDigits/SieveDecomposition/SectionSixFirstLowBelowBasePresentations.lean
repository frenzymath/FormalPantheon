import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import PrimesRestrictedDigits.SieveAsymptotics.TypeIISignedStrictAffineCompiler
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Low-below Proposition 6.1 base presentations

This file packages the two independent affine walls of the pair and triple base sums in the
low-below branch. The tuple orders are `![q, p]` and `![r, q, p]`; order, coordinate floors,
and full-product caps remain Proposition 6.1 carrier data.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137--138, and Section 6, pp. 143--144,
especially Eq. (6.13).
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The two independent pair walls, in normalized-log order `![q, p]`. -/
def sectionSixFirstLowBelowPairRegion
    (epsilon : Real) : Set (Fin 2 -> Real) :=
  {x | sectionSixThetaGap epsilon < x 0 /\
    x 1 + x 0 < sectionSixThetaOne epsilon}

/-- The two independent triple walls, in normalized-log order `![r, q, p]`. -/
def sectionSixFirstLowBelowTripleRegion
    (epsilon : Real) : Set (Fin 3 -> Real) :=
  {x | sectionSixThetaGap epsilon < x 0 /\
    x 2 + x 1 < sectionSixThetaOne epsilon}

/-- The exact two-wall mixed presentation of the pair base region. -/
noncomputable def sectionSixFirstLowBelowPairPresentation
    (epsilon : Real) :
    TypeIIAffineMixedPresentation
      (sectionSixFirstLowBelowPairRegion epsilon) where
  constraintCount := 2
  normal := ![![(-1 : Real), 0], ![(1 : Real), 1]]
  bound := ![-sectionSixThetaGap epsilon, sectionSixThetaOne epsilon]
  isStrict := ![true, true]
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hgap, hsum⟩ c
      fin_cases c <;>
        simp [typeIIAffineValue, Fin.sum_univ_two] <;> linarith
    · intro h
      have hgap := h (0 : Fin 2)
      have hsum := h (1 : Fin 2)
      simp [typeIIAffineValue, Fin.sum_univ_two,
        sectionSixFirstLowBelowPairRegion] at hgap hsum ⊢
      exact ⟨by linarith, by linarith⟩

/-- The exact two-wall mixed presentation of the triple base region. -/
noncomputable def sectionSixFirstLowBelowTriplePresentation
    (epsilon : Real) :
    TypeIIAffineMixedPresentation
      (sectionSixFirstLowBelowTripleRegion epsilon) where
  constraintCount := 2
  normal := ![![(-1 : Real), 0, 0], ![(0 : Real), 1, 1]]
  bound := ![-sectionSixThetaGap epsilon, sectionSixThetaOne epsilon]
  isStrict := ![true, true]
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hgap, hsum⟩ c
      fin_cases c <;>
        simp [typeIIAffineValue, Fin.sum_univ_succ] <;> linarith
    · intro h
      have hgap := h (0 : Fin 2)
      have hsum := h (1 : Fin 2)
      simp [typeIIAffineValue, Fin.sum_univ_succ,
        sectionSixFirstLowBelowTripleRegion] at hgap hsum ⊢
      exact ⟨by linarith, by linarith⟩

end

end PrimesRestrictedDigits
