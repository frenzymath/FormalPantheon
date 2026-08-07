import BoundedGaps.BombieriVinogradov.StandardStatement
import BoundedGaps.BombieriVinogradov.Analytic.WeightedStatement

/-!
# Compatibility of the standard and historical weighted interfaces

This file is the finite, definitional bridge between the independent public
standard statement and the historical natural-endpoint interface.  It does
not import, or consume, any closed Bombieri--Vinogradov theorem.
-/

namespace BoundedGaps.BombieriVinogradov

open scoped BigOperators ArithmeticFunction.vonMangoldt

theorem reducedResidues_eq_coprimeResidues (q : Nat) :
    reducedResidues q = BoundedGaps.Maynard.coprimeResidues q := by
  rfl

theorem chebyshevProgressionSum_eq_maynard (x q a : Nat) :
    chebyshevProgressionSum x q a =
      BoundedGaps.Maynard.chebyshevProgressionSum x q a := by
  rfl

theorem weightedProgressionDiscrepancy_eq_maynard (x q a : Nat) :
    weightedProgressionDiscrepancy x q a =
      BoundedGaps.Maynard.weightedProgressionDiscrepancy x q a := by
  rfl

theorem maxWeightedProgressionDiscrepancyUpTo_eq_maynard
    (x q : Nat) :
    maxWeightedProgressionDiscrepancyUpTo x q =
      BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo x q := by
  by_cases hx : 2 ≤ x
  · by_cases hq : 0 < q
    · simp only [maxWeightedProgressionDiscrepancyUpTo,
        BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo, dif_pos hx,
        BoundedGaps.Maynard.maxWeightedProgressionDiscrepancy, dif_pos hq]
      exact (Finset.sup'_comm (endpointRange_nonempty hx)
        (reducedResidues_nonempty hq)
        (fun y a => weightedProgressionDiscrepancy y q a)).symm
    · simp only [maxWeightedProgressionDiscrepancyUpTo,
        BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo, dif_pos hx,
        BoundedGaps.Maynard.maxWeightedProgressionDiscrepancy, dif_neg hq,
        Finset.sup'_const]
  · simp [maxWeightedProgressionDiscrepancyUpTo,
      BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo, hx]

theorem weightedBombieriVinogradov_iff_maynard :
    weightedBombieriVinogradov ↔
      BoundedGaps.Maynard.hasWeightedBombieriVinogradovWindow := by
  rw [weightedBombieriVinogradov,
    BoundedGaps.Maynard.hasWeightedBombieriVinogradovWindow]
  simp_rw [maxWeightedProgressionDiscrepancyUpTo_eq_maynard]

end BoundedGaps.BombieriVinogradov
