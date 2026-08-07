import Mathlib.Data.EReal.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.LiminfLimsup

/-!
# Standalone bounded-gaps challenge

Mathlib-only specification of the public bounded-gaps interface. The four
theorem placeholders are authorized only in this isolated Challenge module by
PUB-SEM-029. This module must never enter a production proof closure.

Primary source: `Maynard2013v3`, Theorem 1.3, TeX lines 85--88; the exact
diameter-600 specialization is at TeX lines 241--243.
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
  sorry

theorem paperLiminfStatement_iff_consecutive :
    paperLiminfStatement ↔ infinitelyManyBoundedConsecutiveGaps := by
  sorry

theorem paperLiminfStatement_iff_boundedGapsStatement :
    paperLiminfStatement ↔ boundedGapsStatement := by
  sorry

/-- Maynard's unconditional theorem: bounded prime gaps of size at most 600
occur arbitrarily far out. -/
theorem unconditional_boundedGapsStatement : boundedGapsStatement := by
  sorry

end BoundedGaps.Comparator
