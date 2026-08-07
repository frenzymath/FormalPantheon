import BoundedGaps.BombieriVinogradov.Proof.MainTheorem
import BoundedGaps.PrimeNumberTheorem.Proof.MainTheorem
import BoundedGaps.Maynard.ConcreteConditionalPNTIntegration

/-!
# Unconditional constant-600 bounded gaps

This module composes the independently proved Bombieri--Vinogradov theorem and
ordinary prime number theorem with the conditional Maynard integration. It
exports the exact proposition frozen in `BoundedGaps/Statement.lean`.
Source: `Maynard2013v3`, Section 1, Theorem 1.3
(`thrm:Unconditional`), source lines 85--88. Semantic review: `SEM-581`.
-/

namespace BoundedGaps

/-- Maynard's unconditional theorem: bounded prime gaps of size at most 600
occur arbitrarily far out. -/
theorem unconditional_boundedGapsStatement :
    boundedGapsStatement := by
  apply Maynard.boundedGapsStatement_of_bombieriVinogradov_and_pnt
    Maynard.unconditional_bombieriVinogradov
  simpa only [Maynard.primeCountTotal, ordinaryPrimeNumberTheorem] using
    unconditional_ordinaryPrimeNumberTheorem

end BoundedGaps
