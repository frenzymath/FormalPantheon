import PrimesRestrictedDigits.BasicEstimates.BuchstabFunction
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowBelowIndices

/-!
# Buchstab sums for the low-below clean quadruple term

The two coefficient-one finite sums used to normalize the clean `I_6` term.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.13), region `R_4`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def sectionSixFirstLowBelowQuadrupleBuchstabMainSum
    (epsilon : Real) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstLowBelowQuadrupleIndices epsilon length,
    buchstabFunction
        (Real.log (X /
          ((sectionSixFirstLowBelowTripleProduct index.1 * index.2 :
            Nat) : Real)) / Real.log (index.2 : Real)) /
      ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
        (index.1.2 : Real) * (index.2 : Real) * Real.log (index.2 : Real))

noncomputable def sectionSixFirstLowBelowQuadrupleRoughErrorSum
    (epsilon : Real) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstLowBelowQuadrupleIndices epsilon length,
    1 / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
      (index.1.2 : Real) * (index.2 : Real) *
      Real.log (X /
        ((sectionSixFirstLowBelowTripleProduct index.1 * index.2 :
          Nat) : Real)) ^ 2)

end

end PrimesRestrictedDigits
