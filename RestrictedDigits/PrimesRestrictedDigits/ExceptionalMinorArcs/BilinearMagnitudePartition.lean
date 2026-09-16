import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearMagnitudeBands
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearReduction

/-!
# Rational exceptional magnitude fibers

This intersects the canonical magnitude partition with the repaired rational carrier and
records the exact decomposition used in Lemma 13.1.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The repaired rational exceptional frequencies whose canonical magnitude
index is `j`. -/
noncomputable def exceptionalRationalMagnitudeBandFrequencies
    (digit : Fin 10) (length : Nat) (Q E : Real) (j : Nat) :
    Finset (Fin (10 ^ length)) := by
  classical
  exact (exceptionalRationalFrequencies digit length Q E).filter fun a =>
    exceptionalMagnitudeBandIndex digit length a = j

@[simp]
theorem mem_exceptionalRationalMagnitudeBandFrequencies_iff
    {digit : Fin 10} {length : Nat} {Q E : Real} {j : Nat}
    {a : Fin (10 ^ length)} :
    a ∈ exceptionalRationalMagnitudeBandFrequencies
        digit length Q E j ↔
      a ∈ latticeRationalApproximationBand Q E ∧
        a ∈ genericExceptionalFrequencies digit length ∧
          exceptionalMagnitudeBandIndex digit length a = j := by
  simp [exceptionalRationalMagnitudeBandFrequencies, and_assoc]

theorem exceptionalRationalMagnitudeBandFrequencies_subset_exceptional
    {digit : Fin 10} {length : Nat} {Q E : Real} {j : Nat} :
    exceptionalRationalMagnitudeBandFrequencies digit length Q E j ⊆
      genericExceptionalFrequencies digit length := by
  intro a ha
  exact (mem_exceptionalRationalMagnitudeBandFrequencies_iff.mp ha).2.1

theorem exceptionalRationalMagnitudeBandFrequencies_subset_rational
    {digit : Fin 10} {length : Nat} {Q E : Real} {j : Nat} :
    exceptionalRationalMagnitudeBandFrequencies digit length Q E j ⊆
      latticeRationalApproximationBand Q E := by
  intro a ha
  exact (mem_exceptionalRationalMagnitudeBandFrequencies_iff.mp ha).1

/-- Each rational exceptional fiber remains in its source comparable band. -/
theorem exceptionalRationalMagnitudeBandFrequencies_subset_comparable
    {digit : Fin 10} {length : Nat} {Q E : Real} {j : Nat} :
    exceptionalRationalMagnitudeBandFrequencies digit length Q E j ⊆
      comparableMagnitudeFrequencies digit length (10 ^ j : Nat) := by
  intro a ha
  have hdata := mem_exceptionalRationalMagnitudeBandFrequencies_iff.mp ha
  apply exceptionalMagnitudeBandFrequencies_subset_comparable
  exact mem_exceptionalMagnitudeBandFrequencies_iff.mpr
    ⟨hdata.2.1, hdata.2.2⟩

/-- A nonempty rational exceptional fiber has canonical scale at most the
terminal source magnitude. -/
theorem exceptionalRationalMagnitudeBandScale_le_sourceLimit
    {digit : Fin 10} {length : Nat} {Q E : Real} {j : Nat}
    (hne : (exceptionalRationalMagnitudeBandFrequencies
      digit length Q E j).Nonempty) :
    ((10 ^ j : Nat) : Real) <=
      (((10 ^ length : Nat) : Real) ^ (23 / 80 : Real)) := by
  obtain ⟨a, ha⟩ := hne
  have hdata := mem_exceptionalRationalMagnitudeBandFrequencies_iff.mp ha
  exact exceptionalMagnitudeBandScale_le_sourceLimit_of_mem
    (mem_exceptionalMagnitudeBandFrequencies_iff.mpr
      ⟨hdata.2.1, hdata.2.2⟩)

/-- The rational exceptional carrier is the disjoint sum of its canonical
magnitude fibers. -/
theorem sum_exceptionalRationalMagnitudeBandFrequencies
    {M : Type*} [AddCommMonoid M]
    (digit : Fin 10) {length : Nat} (hlength : 0 < length)
    (Q E : Real) (f : Fin (10 ^ length) -> M) :
    (∑ j ∈ Finset.range length,
      ∑ a ∈ exceptionalRationalMagnitudeBandFrequencies
        digit length Q E j, f a) =
      ∑ a ∈ exceptionalRationalFrequencies digit length Q E, f a := by
  classical
  unfold exceptionalRationalMagnitudeBandFrequencies
  apply Finset.sum_fiberwise_of_maps_to
  intro a ha
  have haExceptional :=
    (mem_exceptionalRationalFrequencies_iff.mp ha).2
  exact Finset.mem_range.mpr
    (exceptionalMagnitudeBandIndex_lt hlength haExceptional)

/-- Exact decomposition of the repaired bilinear sum by magnitude fibers. -/
theorem sum_exceptionalBilinearSumOver_magnitudeBands
    (digit : Fin 10) {length : Nat} (hlength : 0 < length)
    (N M Q E : Real) (alpha beta : Nat -> Complex)
    (gamma : Fin (10 ^ length) -> Complex) :
    (∑ j ∈ Finset.range length,
      exceptionalBilinearSumOver digit length
        (exceptionalRationalMagnitudeBandFrequencies digit length Q E j)
          N M alpha beta gamma) =
      exceptionalBilinearSum digit length N M Q E alpha beta gamma := by
  simpa only [exceptionalBilinearSumOver, exceptionalBilinearSum] using
    sum_exceptionalRationalMagnitudeBandFrequencies digit hlength Q E
      (fun a =>
        ∑ n ∈ sourceFactorTenNaturalInterval N,
          ∑ m ∈ sourceFactorTenNaturalInterval M,
            (normalizedPaddedDigitFourierMagnitude
                digit length a.val : Complex) *
              alpha n * beta m * gamma a *
                majorArcPhase
                  (-((a.val : Real) * (n : Real) * (m : Real) /
                    ((10 ^ length : Nat) : Real))))

/-- Triangle inequality after the exact magnitude-fiber decomposition. -/
theorem norm_exceptionalBilinearSum_le_sum_magnitudeBands
    (digit : Fin 10) {length : Nat} (hlength : 0 < length)
    (N M Q E : Real) (alpha beta : Nat -> Complex)
    (gamma : Fin (10 ^ length) -> Complex) :
    ‖exceptionalBilinearSum digit length N M Q E alpha beta gamma‖ <=
      ∑ j ∈ Finset.range length,
        ‖exceptionalBilinearSumOver digit length
          (exceptionalRationalMagnitudeBandFrequencies digit length Q E j)
            N M alpha beta gamma‖ := by
  rw [← sum_exceptionalBilinearSumOver_magnitudeBands
    digit hlength N M Q E alpha beta gamma]
  exact norm_sum_le _ _

end PrimesRestrictedDigits
