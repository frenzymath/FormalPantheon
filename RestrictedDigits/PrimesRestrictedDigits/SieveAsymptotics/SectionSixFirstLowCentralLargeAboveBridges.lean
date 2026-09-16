import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowBridges

/-!
# Finite bridge for the low central-large above term

This file reindexes the raw continuation Buchstab main sum by the exact left-associated
normalized triple carrier. The kernel algebra contributes exactly one division by `log X`.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.11).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralLargeAboveBuchstabMainSum_eq_normalized
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
        epsilon length .above =
      normalizedPrimeLogTripleSum
          (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
          (sectionSixFirstLowCentralLargeAboveRegion epsilon)
          sectionSixFirstLowCentralLargeAboveKernel /
        Real.log ((10 ^ length : Nat) : Real) := by
  classical
  let indices := sectionSixFirstLowCentralLargeContinuationPieceIndices
    epsilon length .above
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hpoint : ∀ index ∈ indices,
      buchstabFunction
          (Real.log (X /
            ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) /
              Real.log (index.2 : Real)) /
        ((index.1.1 : Real) * (index.1.2 : Real) *
          (index.2 : Real) * Real.log (index.2 : Real)) =
        normalizedPrimeLogWeight XNat index.1.1 *
            normalizedPrimeLogWeight XNat index.1.2 *
            normalizedPrimeLogWeight XNat index.2 *
            sectionSixFirstLowCentralLargeAboveKernel
              ((normalizedPrimeLog XNat index.1.1,
                normalizedPrimeLog XNat index.1.2),
                normalizedPrimeLog XNat index.2) /
          Real.log X := by
    intro index hindex
    have hdata := sectionSixFirstLowCentralLargeContinuation_indexData
      (by simpa only [indices] using hindex)
    simpa only [sectionSixFirstLowCentralLargeAboveKernel] using
      sectionSixFirstLowCentralLargeBelowBuchstabSummand_eq hlength index
        hdata.1 hdata.2.1 hdata.2.2.1
  unfold sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
    normalizedPrimeLogTripleSum
  dsimp only [X, XNat, indices]
  rw [← image_sectionSixFirstLowCentralLargeAboveContinuationIndices
      epsilon hepsilon hepsilonSmall hlength,
    Finset.sum_image
      sectionSixFirstLowCentralLargeContinuationNatTriple_injective.injOn,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro index hindex
  exact hpoint index hindex

end

end PrimesRestrictedDigits
