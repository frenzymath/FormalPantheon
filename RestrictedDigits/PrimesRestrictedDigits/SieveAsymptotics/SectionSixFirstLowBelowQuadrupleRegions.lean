import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The low-below strict quadruple region

This file defines the exact clean region, literal source region, and Buchstab integral for
Maynard's `I_6` term. The exact region retains the weak role-order faces of the finite
carrier, while the source region opens those three faces.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.13) and `R_4`.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowBelowQuadrupleRegion
    (epsilon : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.2 /\
    x.2 <= x.1.2 /\
    x.1.2 <= x.1.1.2 /\
    x.1.1.2 <= x.1.1.1 /\
    x.1.1.1 + x.1.1.2 < sectionSixThetaOne epsilon /\
    x.1.1.1 + x.1.1.2 + x.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) /\
    x.1.1.1 + x.1.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) /\
    x.1.1.1 + x.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) /\
    x.1.1.2 + x.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) /\
    x.1.1.1 + x.1.1.2 + x.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) /\
    x.1.1.1 + x.1.1.2 + x.1.2 + x.2 ∉
      Set.Icc (1 - sectionSixThetaTwo epsilon)
        (1 - sectionSixThetaOne epsilon)}

def sectionSixFirstLowBelowQuadrupleSourceRegion
    (epsilon : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.2 /\
    x.2 < x.1.2 /\
    x.1.2 < x.1.1.2 /\
    x.1.1.2 < x.1.1.1 /\
    x.1.1.1 < sectionSixThetaOne epsilon /\
    x.1.1.1 + x.1.1.2 < sectionSixThetaOne epsilon /\
    x.1.1.1 + x.1.1.2 + x.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) /\
    x.1.1.1 + x.1.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) /\
    x.1.1.1 + x.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) /\
    x.1.1.2 + x.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) /\
    x.1.1.1 + x.1.1.2 + x.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) /\
    x.1.1.1 + x.1.1.2 + x.1.2 + x.2 ∉
      Set.Icc (1 - sectionSixThetaTwo epsilon)
        (1 - sectionSixThetaOne epsilon)}

def sectionSixFirstLowBelowQuadrupleKernel
    (x : (((Real × Real) × Real) × Real)) : Real :=
  buchstabFunction
      ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) /
    (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat))

noncomputable def sectionSixFirstLowBelowQuadrupleIntegral
    (epsilon : Real) : Real :=
  ∫ x in sectionSixFirstLowBelowQuadrupleRegion epsilon,
    sectionSixFirstLowBelowQuadrupleKernel x

end

end PrimesRestrictedDigits
