import Lean.Elab.Tactic.Omega

import BoundedGaps.Statement
import BoundedGaps.Foundations.Admissible

/-!
# Transfer from prime shifts to bounded gaps

Maynard2013v3, Proposition `prpstn:Explicit` (source lines 217--231), produces
arbitrarily large translates containing several primes.  This file isolates
the elementary finite-set transfer from that output to Theorem 1.3.
-/

namespace BoundedGaps

/-- Number of shifts in `H` that produce a prime after translation by `n`. -/
def primeShiftCount (H : Finset ℕ) (n : ℕ) : ℕ :=
  (H.filter fun h => (n + h).Prime).card

/-- Beyond every threshold, some translate has at least `r` prime shifts. -/
def InfinitelyOftenAtLeastPrimeShifts (H : Finset ℕ) (r : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N < n ∧ r ≤ primeShiftCount H n

theorem boundedGapsStatement_of_two_prime_shifts {H : Finset ℕ}
    (hH : ∀ h ∈ H, h ≤ boundedGapConstant)
    (hprime : InfinitelyOftenAtLeastPrimeShifts H 2) :
    boundedGapsStatement := by
  intro N
  obtain ⟨n, hNn, hcount⟩ := hprime N
  have hcard : 1 < (H.filter fun h => (n + h).Prime).card := by
    unfold primeShiftCount at hcount
    omega
  obtain ⟨h₁, hh₁, h₂, hh₂, hne⟩ := Finset.one_lt_card.mp hcard
  have h₁data := Finset.mem_filter.mp hh₁
  have h₂data := Finset.mem_filter.mp hh₂
  have hpair :
      ∃ a b : ℕ, a ∈ H ∧ b ∈ H ∧ a < b ∧ (n + a).Prime ∧ (n + b).Prime := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨h₁, h₂, h₁data.1, h₂data.1, hlt, h₁data.2, h₂data.2⟩
    · exact ⟨h₂, h₁, h₂data.1, h₁data.1, hlt, h₂data.2, h₁data.2⟩
  obtain ⟨a, b, haH, hbH, hab, hpa, hpb⟩ := hpair
  refine ⟨n + a, n + b, ?_, ?_, hpa, hpb, ?_⟩
  · exact lt_of_lt_of_le hNn (Nat.le_add_right n a)
  · exact Nat.add_lt_add_left hab n
  · have hb := hH b hbH
    simp only [boundedGapConstant] at hb ⊢
    omega

theorem boundedGapsStatement_of_engelsma_two_prime_shifts
    (hprime : InfinitelyOftenAtLeastPrimeShifts engelsmaTuple 2) :
    boundedGapsStatement := by
  apply boundedGapsStatement_of_two_prime_shifts
  · intro h hh
    simpa [boundedGapConstant] using engelsmaTuple_le_six_hundred hh
  · exact hprime

end BoundedGaps
