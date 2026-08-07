import BoundedGaps.BombieriVinogradov.ProductionContract

/-!
# Production-backed Bombieri--Vinogradov interface mirror

This module mirrors the standalone Challenge declarations in the isolated
namespace `BoundedGaps.BombieriVinogradov.Comparator`. Definitions delegate
definitionally to the reviewed production surface, and theorem bodies close
from production proofs.
-/

namespace BoundedGaps.BombieriVinogradov.Comparator

open scoped BigOperators ArithmeticFunction.vonMangoldt

/-- Reduced residue representatives in the range `0 <= a < q`. -/
def coprimeResidues (q : ℕ) : Finset ℕ := BoundedGaps.Maynard.coprimeResidues q

theorem coprimeResidues_nonempty {q : ℕ} (hq : 0 < q) :
    (coprimeResidues q).Nonempty := by
  change (BoundedGaps.Maynard.coprimeResidues q).Nonempty
  exact BoundedGaps.Maynard.coprimeResidues_nonempty hq

/-- The number of primes `n <= x` in the residue class `a (mod q)`. -/
def primeCountUpTo (x q a : ℕ) : ℕ :=
  BoundedGaps.Maynard.primeCountUpTo x q a

/-- The total number of primes `n <= x`. -/
def primeCountTotal (x : ℕ) : ℕ := BoundedGaps.Maynard.primeCountTotal x

/-- Absolute discrepancy for one reduced residue representative. -/
noncomputable def progressionDiscrepancy (x q a : ℕ) : ℝ :=
  BoundedGaps.Maynard.progressionDiscrepancy x q a

/-- The largest discrepancy among reduced residue representatives.

The zero-modulus branch is outside the theorem's positive-modulus sum. It
makes this definition total without hiding a nonzero hypothesis.
-/
noncomputable def maxProgressionDiscrepancy (x q : ℕ) : ℝ :=
  BoundedGaps.Maynard.maxProgressionDiscrepancy x q

/-- The integral modulus cutoff `floor(x^theta)` for natural `x`. -/
noncomputable def modulusCutoff (θ : ℝ) (x : ℕ) : ℕ :=
  BoundedGaps.Maynard.modulusCutoff θ x

/-- Prime level of distribution `theta`, with all asymptotic uniformity
quantifiers explicit. Constants may depend on `A` and `theta`, but not on the
natural asymptotic variable `x`. -/
def hasPrimeLevel (θ : ℝ) : Prop := BoundedGaps.Maynard.hasPrimeLevel θ

/-- Bombieri--Vinogradov in the exact level language used by Maynard: every
fixed positive level below one half is available. -/
def bombieriVinogradov : Prop := BoundedGaps.Maynard.bombieriVinogradov

/-- Bombieri--Vinogradov supplies every fixed positive prime level strictly
below one half. -/
theorem unconditional_bombieriVinogradov : bombieriVinogradov := by
  change BoundedGaps.Maynard.bombieriVinogradov
  exact BoundedGaps.Maynard.unconditional_bombieriVinogradov

/-- Reduced residue representatives in the range `0 <= a < q`. -/
def reducedResidues (q : Nat) : Finset Nat :=
  BoundedGaps.BombieriVinogradov.reducedResidues q

theorem reducedResidues_nonempty {q : Nat} (hq : 0 < q) :
    (reducedResidues q).Nonempty := by
  change (BoundedGaps.BombieriVinogradov.reducedResidues q).Nonempty
  exact BoundedGaps.BombieriVinogradov.reducedResidues_nonempty hq

theorem endpointRange_nonempty {x : Nat} (hx : 2 <= x) :
    (Finset.Icc 2 x).Nonempty := by
  exact BoundedGaps.BombieriVinogradov.endpointRange_nonempty hx

/-- The von Mangoldt sum over positive `n <= x` in the class `a (mod q)`. -/
noncomputable def chebyshevProgressionSum (x q a : Nat) : Real :=
  BoundedGaps.BombieriVinogradov.chebyshevProgressionSum x q a

/-- Weighted progression discrepancy centered at the source term `x / phi(q)`. -/
noncomputable def weightedProgressionDiscrepancy
    (x q a : Nat) : Real :=
  BoundedGaps.BombieriVinogradov.weightedProgressionDiscrepancy x q a

/-- The source-ordered maximum over reduced residues and natural endpoints. -/
noncomputable def maxWeightedProgressionDiscrepancyUpTo
    (x q : Nat) : Real :=
  BoundedGaps.BombieriVinogradov.maxWeightedProgressionDiscrepancyUpTo x q

/-- Vaughan's natural-endpoint logarithmic-window weighted contract. -/
def weightedBombieriVinogradov : Prop :=
  BoundedGaps.BombieriVinogradov.weightedBombieriVinogradov

/-- The unconditional standard weighted Bombieri--Vinogradov theorem. -/
theorem unconditional_weightedBombieriVinogradov :
    weightedBombieriVinogradov := by
  change BoundedGaps.BombieriVinogradov.weightedBombieriVinogradov
  exact BoundedGaps.BombieriVinogradov.unconditional_weightedBombieriVinogradov

end BoundedGaps.BombieriVinogradov.Comparator
