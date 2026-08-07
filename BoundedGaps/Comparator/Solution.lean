import BoundedGaps.ProductionContract

/-!
# Production-backed bounded-gaps solution

This module exactly mirrors the standalone `Comparator.Challenge` declarations
in the isolated namespace `BoundedGaps.Comparator`. Definition bodies are
repeated exactly so the official comparator can compare their exported
constants, while theorem bodies close from production proofs.
-/

namespace BoundedGaps.Comparator

/-- The fixed numerical constant in Maynard2013v3, Theorem 1.3. -/
def boundedGapConstant : ℕ := 600

/-- A prime pair strictly beyond `N` with the required gap bound.

The use of natural subtraction is harmless because `p < q` is an explicit
hypothesis.  This is the public, indexing-independent form of the theorem.
-/
def HasBoundedPrimePair (N : ℕ) : Prop :=
  ∃ p q : ℕ,
    N < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q - p ≤ boundedGapConstant

/-- The exact proposition exported by the final proof module. -/
def boundedGapsStatement : Prop := ∀ N : ℕ, HasBoundedPrimePair N

/-- `p` and `q` are consecutive primes, with no prime strictly between them. -/
def IsConsecutivePrimePair (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬r.Prime

/-- The index-free formulation using arbitrarily large lower endpoints of
consecutive bounded gaps. -/
def infinitelyManyBoundedConsecutiveGaps : Prop :=
  ∀ N : ℕ, ∃ p q : ℕ,
    N < p ∧ IsConsecutivePrimePair p q ∧ q - p ≤ boundedGapConstant

/-- The paper's liminf formulation, using Mathlib's increasing enumeration
`Nat.nth Nat.Prime` (indexed from zero) and the filter `atTop`. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

def paperLiminfStatement : Prop :=
  Filter.liminf (fun n : ℕ => (primeGap n : EReal)) Filter.atTop ≤
    (boundedGapConstant : EReal)

theorem boundedGapsStatement_iff_consecutive :
    boundedGapsStatement ↔ infinitelyManyBoundedConsecutiveGaps := by
  change BoundedGaps.boundedGapsStatement ↔
    BoundedGaps.infinitelyManyBoundedConsecutiveGaps
  exact BoundedGaps.boundedGapsStatement_iff_consecutive

theorem paperLiminfStatement_iff_consecutive :
    paperLiminfStatement ↔ infinitelyManyBoundedConsecutiveGaps := by
  change BoundedGaps.paperLiminfStatement ↔
    BoundedGaps.infinitelyManyBoundedConsecutiveGaps
  exact BoundedGaps.paperLiminfStatement_iff_consecutive

theorem paperLiminfStatement_iff_boundedGapsStatement :
    paperLiminfStatement ↔ boundedGapsStatement := by
  change BoundedGaps.paperLiminfStatement ↔ BoundedGaps.boundedGapsStatement
  exact BoundedGaps.paperLiminfStatement_iff_boundedGapsStatement

/-- Maynard's unconditional theorem: bounded prime gaps of size at most 600
occur arbitrarily far out. -/
theorem unconditional_boundedGapsStatement : boundedGapsStatement := by
  change BoundedGaps.boundedGapsStatement
  exact BoundedGaps.unconditional_boundedGapsStatement

end BoundedGaps.Comparator
