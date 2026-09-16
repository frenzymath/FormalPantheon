import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstPairRegions
import PrimesRestrictedDigits.SieveAsymptotics.TypeIISignedStrictAffineCompiler
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Proposition 6.2 presentations for the first strict pair residuals

The residual tuple is ordered as `![q,p]`.  These regions are written in the
normalized logarithmic coordinates used by Proposition 6.2; strict lower
walls remain strict and the theta/half upper walls are weak.
-/

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowResidualRegion (epsilon : Real) : Set (Fin 2 -> Real) :=
  {x | sectionSixThetaGap epsilon < x 0 ∧
    sectionSixThetaGap epsilon < x 1 ∧
    x 1 <= sectionSixThetaOne epsilon}

def sectionSixFirstHighResidualRegion (epsilon : Real) : Set (Fin 2 -> Real) :=
  {x | sectionSixThetaGap epsilon < x 0 ∧
    sectionSixThetaTwo epsilon < x 1 ∧
    x 1 <= (1 / 2 : Real)}

noncomputable def sectionSixFirstLowResidualPresentation (epsilon : Real) :
  TypeIIAffineMixedPresentation (sectionSixFirstLowResidualRegion epsilon) where
  constraintCount := 3
  normal := ![![(-1 : Real), 0], ![0, (-1 : Real)], ![0, (1 : Real)]]
  bound := ![-sectionSixThetaGap epsilon, -sectionSixThetaGap epsilon,
    sectionSixThetaOne epsilon]
  isStrict := ![true, true, false]
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hx0, hx1, hx2⟩ c
      fin_cases c
      · simpa [typeIIAffineValue] using (neg_lt_neg hx0)
      · simpa [typeIIAffineValue] using (neg_lt_neg hx1)
      · simpa [typeIIAffineValue] using hx2
    · intro h
      have h0 := h (0 : Fin 3)
      have h1 := h (1 : Fin 3)
      have h2 := h (2 : Fin 3)
      change typeIIAffineValue ![(-1 : Real), 0] x <
          -sectionSixThetaGap epsilon at h0
      change typeIIAffineValue ![0, (-1 : Real)] x <
          -sectionSixThetaGap epsilon at h1
      change typeIIAffineValue ![0, (1 : Real)] x <=
          sectionSixThetaOne epsilon at h2
      simp [sectionSixFirstLowResidualRegion, typeIIAffineValue,
        Fin.sum_univ_two] at h0 h1 h2 ⊢
      exact ⟨by linarith, by linarith, by linarith⟩

noncomputable def sectionSixFirstHighResidualPresentation (epsilon : Real) :
  TypeIIAffineMixedPresentation (sectionSixFirstHighResidualRegion epsilon) where
  constraintCount := 3
  normal := ![![(-1 : Real), 0], ![0, (-1 : Real)], ![0, (1 : Real)]]
  bound := ![-sectionSixThetaGap epsilon, -sectionSixThetaTwo epsilon,
    (1 / 2 : Real)]
  isStrict := ![true, true, false]
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hx0, hx1, hx2⟩ c
      fin_cases c
      · simpa [typeIIAffineValue] using (neg_lt_neg hx0)
      · simpa [typeIIAffineValue] using (neg_lt_neg hx1)
      · simpa [typeIIAffineValue] using hx2
    · intro h
      have h0 := h (0 : Fin 3)
      have h1 := h (1 : Fin 3)
      have h2 := h (2 : Fin 3)
      change typeIIAffineValue ![(-1 : Real), 0] x <
          -sectionSixThetaGap epsilon at h0
      change typeIIAffineValue ![0, (-1 : Real)] x <
          -sectionSixThetaTwo epsilon at h1
      change typeIIAffineValue ![0, (1 : Real)] x <=
          (1 / 2 : Real) at h2
      simp [sectionSixFirstHighResidualRegion, typeIIAffineValue,
        Fin.sum_univ_two] at h0 h1 h2 ⊢
      exact ⟨by linarith, by linarith, by linarith⟩

end

end PrimesRestrictedDigits
