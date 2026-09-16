import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearIntervals
import PrimesRestrictedDigits.GenericMinorArcs.GenericFrequencyBounds
import PrimesRestrictedDigits.LatticeEstimates.RationalApproximationBands
import PrimesRestrictedDigits.MajorArcs.Phase

/-!
# The exceptional bilinear sum

This file defines the literal finite sum in repaired Lemma 13.1 of `MAYNARD-PRD-PUBLISHED`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Frequencies lying in both the repaired rational band and the weak
exceptional digit-frequency carrier. -/
noncomputable def exceptionalRationalFrequencies
    (digit : Fin 10) (length : Nat) (Q E : Real) :
    Finset (Fin (10 ^ length)) :=
  latticeRationalApproximationBand Q E ∩
    genericExceptionalFrequencies digit length

@[simp]
theorem mem_exceptionalRationalFrequencies_iff
    {digit : Fin 10} {length : Nat} {Q E : Real}
    {a : Fin (10 ^ length)} :
    a ∈ exceptionalRationalFrequencies digit length Q E ↔
      a ∈ latticeRationalApproximationBand Q E ∧
        a ∈ genericExceptionalFrequencies digit length := by
  simp [exceptionalRationalFrequencies]

/-- The complex bilinear sum from repaired Lemma 13.1. -/
noncomputable def exceptionalBilinearSum
    (digit : Fin 10) (length : Nat) (N M Q E : Real)
    (alpha beta : Nat -> Complex)
    (gamma : Fin (10 ^ length) -> Complex) : Complex :=
  ∑ a ∈ exceptionalRationalFrequencies digit length Q E,
    ∑ n ∈ sourceFactorTenNaturalInterval N,
      ∑ m ∈ sourceFactorTenNaturalInterval M,
        (normalizedPaddedDigitFourierMagnitude
            digit length a.val : Complex) *
          alpha n * beta m * gamma a *
            majorArcPhase
              (-((a.val : Real) * (n : Real) * (m : Real) /
                ((10 ^ length : Nat) : Real)))

end PrimesRestrictedDigits
