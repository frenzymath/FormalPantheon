import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract

/-!
# Section 6 cutoff scales

This file defines the six real cutoffs used in the sieve decomposition and proves their strict
order on the accepted epsilon range.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 138.
-/

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixZOne (epsilon X : Real) : Real :=
  X ^ sectionSixThetaGap epsilon

def sectionSixZTwo (epsilon X : Real) : Real :=
  X ^ sectionSixThetaOne epsilon

def sectionSixZThree (epsilon X : Real) : Real :=
  X ^ sectionSixThetaTwo epsilon

def sectionSixZFour (X : Real) : Real :=
  Real.sqrt X

def sectionSixZFive (epsilon X : Real) : Real :=
  X ^ (1 - sectionSixThetaTwo epsilon)

def sectionSixZSix (epsilon X : Real) : Real :=
  X ^ (1 - sectionSixThetaOne epsilon)

theorem sectionSixZFour_eq_rpow (X : Real) :
    sectionSixZFour X = X ^ (1 / 2 : Real) := by
  rw [sectionSixZFour, Real.sqrt_eq_rpow]

theorem sectionSix_cutoffs_strict
    {epsilon X : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) (hX : 1 < X) :
    sectionSixZOne epsilon X < sectionSixZTwo epsilon X ∧
      sectionSixZTwo epsilon X < sectionSixZThree epsilon X ∧
      sectionSixZThree epsilon X < sectionSixZFour X ∧
      sectionSixZFour X < sectionSixZFive epsilon X ∧
      sectionSixZFive epsilon X < sectionSixZSix epsilon X := by
  have hgapPos : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hgapThetaOne :
      sectionSixThetaGap epsilon < sectionSixThetaOne epsilon := by
    rw [sectionSixThetaGap_eq]
    simp only [sectionSixThetaOne]
    linarith
  have hthetaOneTwo :
      sectionSixThetaOne epsilon < sectionSixThetaTwo epsilon := by
    rw [← sub_pos]
    exact hgapPos
  have hthetaTwoHalf : sectionSixThetaTwo epsilon < (1 / 2 : Real) := by
    simp only [sectionSixThetaTwo]
    linarith
  have hhalfThetaFive :
      (1 / 2 : Real) < 1 - sectionSixThetaTwo epsilon := by
    linarith
  have hthetaFiveSix :
      1 - sectionSixThetaTwo epsilon < 1 - sectionSixThetaOne epsilon := by
    linarith
  rw [sectionSixZFour_eq_rpow]
  simp only [sectionSixZOne, sectionSixZTwo, sectionSixZThree,
    sectionSixZFive, sectionSixZSix]
  exact ⟨
    Real.rpow_lt_rpow_of_exponent_lt hX hgapThetaOne,
    Real.rpow_lt_rpow_of_exponent_lt hX hthetaOneTwo,
    Real.rpow_lt_rpow_of_exponent_lt hX hthetaTwoHalf,
    Real.rpow_lt_rpow_of_exponent_lt hX hhalfThetaFive,
    Real.rpow_lt_rpow_of_exponent_lt hX hthetaFiveSix⟩

end

end PrimesRestrictedDigits
