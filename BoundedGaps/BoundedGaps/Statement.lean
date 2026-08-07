import Mathlib.Data.EReal.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.LiminfLimsup

/-!
# Public statement for Maynard's bounded-gaps theorem

This file is the deliberately small, expert-facing trust surface. The source
form is Maynard2013v3, Theorem 1.3 (`thrm:Unconditional`), which is phrased
using the increasing sequence of primes and a liminf. We use the equivalent
index-free formulation `boundedGapsStatement`. This surface contains the
project-specific definitions and exact proposition, while the proved theorem
is exported from `Proof/MainTheorem.lean`, which imports this file. Analytic
implementation details remain in importing proof modules. `Audit/Statement.lean`
checks this surface, and `Audit/MainTheorem.lean` checks the final export.
-/

namespace BoundedGaps

/-- The fixed numerical constant in Maynard2013v3, Theorem 1.3. -/
def boundedGapConstant : ℕ := 600

theorem boundedGapConstant_eq : boundedGapConstant = 600 := rfl

/-- A prime pair strictly beyond `N` with the required gap bound.

The use of natural subtraction is harmless because `p < q` is an explicit
hypothesis.  This is the public, indexing-independent form of the theorem.
-/
def HasBoundedPrimePair (N : ℕ) : Prop :=
  ∃ p q : ℕ,
    N < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q - p ≤ boundedGapConstant

/-- The exact proposition exported by the final proof module. -/
def boundedGapsStatement : Prop := ∀ N : ℕ, HasBoundedPrimePair N

theorem boundedGapsStatement_contract :
    boundedGapsStatement ↔
      ∀ N : ℕ, ∃ p q : ℕ,
        N < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q - p ≤ 600 := by
  rfl

/-- `p` and `q` are consecutive primes, with no prime strictly between them. -/
def IsConsecutivePrimePair (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬r.Prime

/-- The index-free formulation using arbitrarily large lower endpoints of
consecutive bounded gaps. -/
def infinitelyManyBoundedConsecutiveGaps : Prop :=
  ∀ N : ℕ, ∃ p q : ℕ,
    N < p ∧ IsConsecutivePrimePair p q ∧ q - p ≤ boundedGapConstant

theorem boundedGapsStatement_iff_consecutive :
    boundedGapsStatement ↔ infinitelyManyBoundedConsecutiveGaps := by
  constructor
  · intro h N
    obtain ⟨p, q, hNp, hpq, hpp, hqp, hgap⟩ := h N
    let nextPrimeExists : ∃ r : ℕ, p < r ∧ r.Prime := ⟨q, hpq, hqp⟩
    let r := Nat.find nextPrimeExists
    have hr : p < r ∧ r.Prime := Nat.find_spec nextPrimeExists
    have hrq : r ≤ q := Nat.find_min' nextPrimeExists ⟨hpq, hqp⟩
    have hconsecutive : IsConsecutivePrimePair p r := by
      refine ⟨hpp, hr.2, hr.1, ?_⟩
      intro s hps hsr hsp
      exact (not_lt_of_ge (Nat.find_min' nextPrimeExists ⟨hps, hsp⟩)) hsr
    exact ⟨p, r, hNp, hconsecutive,
      (Nat.sub_le_sub_right hrq p).trans hgap⟩
  · intro h N
    obtain ⟨p, q, hNp, hpq, hgap⟩ := h N
    exact ⟨p, q, hNp, hpq.2.2.1, hpq.1, hpq.2.1, hgap⟩

/-- The paper's liminf formulation, using Mathlib's increasing enumeration
`Nat.nth Nat.Prime` (indexed from zero) and the filter `atTop`. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

def paperLiminfStatement : Prop :=
  Filter.liminf (fun n : ℕ => (primeGap n : EReal)) Filter.atTop ≤
    (boundedGapConstant : EReal)

end BoundedGaps
