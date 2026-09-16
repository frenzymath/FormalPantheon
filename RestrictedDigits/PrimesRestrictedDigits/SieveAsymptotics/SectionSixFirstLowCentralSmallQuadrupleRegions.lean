import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The low central-small strict quadruple region

This file defines the exact eight-wall region, literal source region, and Buchstab integral
for Maynard's `I_5` term. The five pair-product exclusions belong to the clean finite carrier,
while the source region opens the five affine boundary faces used in the published integral.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12) and `R_3`.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallQuadrupleRegion
    (epsilon : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.2 ∧
    x.2 <= x.1.2 ∧
    x.1.2 <= x.1.1.2 ∧
    x.1.1.2 <= x.1.1.1 ∧
    x.1.1.1 <= sectionSixThetaOne epsilon ∧
    sectionSixThetaTwo epsilon < x.1.1.1 + x.1.1.2 ∧
    x.1.1.1 + 2 * x.1.1.2 < 1 - sectionSixThetaOne epsilon ∧
    x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1 ∧
    x.1.1.1 + x.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.1 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.2 + x.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)}

def sectionSixFirstLowCentralSmallQuadrupleSourceRegion
    (epsilon : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.2 ∧
    x.2 < x.1.2 ∧
    x.1.2 < x.1.1.2 ∧
    x.1.1.2 < x.1.1.1 ∧
    x.1.1.1 < sectionSixThetaOne epsilon ∧
    x.1.1.1 + 2 * x.1.1.2 < 1 - sectionSixThetaOne epsilon ∧
    x.1.1.1 + x.1.1.2 + 2 * x.1.2 < 1 ∧
    x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1 ∧
    sectionSixThetaTwo epsilon < x.1.1.1 + x.1.1.2 ∧
    x.1.1.1 + x.1.1.2 < 1 - sectionSixThetaTwo epsilon ∧
    x.1.1.1 + x.1.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.1 + x.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.1 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.2 + x.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)}

def sectionSixFirstLowCentralSmallQuadrupleKernel
    (x : (((Real × Real) × Real) × Real)) : Real :=
  buchstabFunction
      ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) /
    (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat))

noncomputable def sectionSixFirstLowCentralSmallQuadrupleIntegral
    (epsilon : Real) : Real :=
  ∫ x in sectionSixFirstLowCentralSmallQuadrupleRegion epsilon,
    sectionSixFirstLowCentralSmallQuadrupleKernel x

end

end PrimesRestrictedDigits
