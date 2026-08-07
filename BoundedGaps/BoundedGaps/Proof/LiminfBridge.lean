import BoundedGaps.Statement

/-!
# Liminf bridge for the prime-gap sequence

The key point is discreteness: a natural-valued sequence has liminf at most a
natural `C` exactly when values at most `C` occur arbitrarily far out.

Source comparison: `Maynard2013v3`, Section 1, Theorem 1.3
(`thrm:Unconditional`), source lines 85--88. The paper uses the increasing
prime sequence; this file checks the zero-based `Nat.nth Nat.Prime` indexing
and both equivalence directions explicitly. Semantic reviews: `SEM-001`,
`SEM-002`, and `SEM-003`.
-/

namespace BoundedGaps

theorem liminf_natCast_le_iff (u : ℕ → ℕ) (C : ℕ) :
    Filter.liminf (fun n => (u n : EReal)) Filter.atTop ≤ (C : EReal) ↔
      ∀ N : ℕ, ∃ n : ℕ, N < n ∧ u n ≤ C := by
  constructor
  · intro hlim
    have hfrequent : ∃ᶠ n in Filter.atTop, (u n : EReal) ≤ (C : EReal) := by
      by_contra hnot
      have heventually : ∀ᶠ n in Filter.atTop,
          ¬(u n : EReal) ≤ (C : EReal) := Filter.not_frequently.mp hnot
      have hlower : ((C + 1 : ℕ) : EReal) ≤
          Filter.liminf (fun n => (u n : EReal)) Filter.atTop := by
        refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
        filter_upwards [heventually] with n hn
        rw [EReal.natCast_le_iff]
        apply Nat.succ_le_of_lt
        exact Nat.lt_of_not_ge (by
          simpa only [EReal.natCast_le_iff] using hn)
      have hfalse : ((C + 1 : ℕ) : EReal) ≤ (C : EReal) := hlower.trans hlim
      have : C + 1 ≤ C := EReal.natCast_le_iff.mp hfalse
      omega
    rw [Filter.frequently_atTop'] at hfrequent
    intro N
    obtain ⟨n, hn, hun⟩ := hfrequent N
    exact ⟨n, hn, EReal.natCast_le_iff.mp hun⟩
  · intro h
    apply Filter.liminf_le_of_frequently_le'
    rw [Filter.frequently_atTop']
    intro N
    obtain ⟨n, hn, hun⟩ := h N
    exact ⟨n, hn, EReal.natCast_le_iff.mpr hun⟩

theorem nthPrime_isConsecutivePrimePair (n : ℕ) :
    IsConsecutivePrimePair (Nat.nth Nat.Prime n)
      (Nat.nth Nat.Prime (n + 1)) := by
  have hmono := Nat.nth_strictMono Nat.infinite_setOf_prime
  refine ⟨Nat.prime_nth_prime n, Nat.prime_nth_prime (n + 1),
    hmono (Nat.lt_succ_self n), ?_⟩
  intro r hleft hright hr
  have hrle : r ≤ Nat.nth Nat.Prime n := by
    apply Nat.le_nth_of_lt_nth_succ hright hr
  exact (not_lt_of_ge hrle) hleft

theorem paperLiminfStatement_infinitelyManyBoundedConsecutiveGaps
    (h : paperLiminfStatement) : infinitelyManyBoundedConsecutiveGaps := by
  have hindices := (liminf_natCast_le_iff primeGap boundedGapConstant).mp h
  intro N
  obtain ⟨n, hNn, hgap⟩ := hindices N
  have hNprimeN : N < Nat.nth Nat.Prime N :=
    (show N < N + 2 by omega).trans_le (Nat.add_two_le_nth_prime N)
  have hprimeNn : Nat.nth Nat.Prime N < Nat.nth Nat.Prime n :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime) hNn
  exact ⟨Nat.nth Nat.Prime n, Nat.nth Nat.Prime (n + 1),
    hNprimeN.trans hprimeNn, nthPrime_isConsecutivePrimePair n, hgap⟩

theorem infinitelyManyBoundedConsecutiveGaps_paperLiminfStatement
    (h : infinitelyManyBoundedConsecutiveGaps) : paperLiminfStatement := by
  apply (liminf_natCast_le_iff primeGap boundedGapConstant).mpr
  intro N
  obtain ⟨p, q, hp_large, hpair, hgap⟩ :=
    h (Nat.nth Nat.Prime (N + 1))
  obtain ⟨hpp, hqp, hpq, hbetween⟩ := hpair
  have hp_range : p ∈ Set.range (Nat.nth Nat.Prime) := by
    rw [Nat.range_nth_of_infinite Nat.infinite_setOf_prime]
    exact hpp
  obtain ⟨m, rfl⟩ := hp_range
  have hq_range : q ∈ Set.range (Nat.nth Nat.Prime) := by
    rw [Nat.range_nth_of_infinite Nat.infinite_setOf_prime]
    exact hqp
  obtain ⟨j, rfl⟩ := hq_range
  have hNm : N < m := by
    have : N + 1 < m :=
      (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp hp_large
    omega
  have hmj : m < j :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp hpq
  have hj : j = m + 1 := by
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro hsuccj
      exact hbetween (Nat.nth Nat.Prime (m + 1))
        ((Nat.nth_strictMono Nat.infinite_setOf_prime) (Nat.lt_succ_self m))
        ((Nat.nth_strictMono Nat.infinite_setOf_prime) hsuccj)
        (Nat.prime_nth_prime (m + 1))
    · omega
  subst j
  exact ⟨m, hNm, by simpa [primeGap] using hgap⟩

theorem paperLiminfStatement_iff_consecutive :
    paperLiminfStatement ↔ infinitelyManyBoundedConsecutiveGaps := by
  exact ⟨paperLiminfStatement_infinitelyManyBoundedConsecutiveGaps,
    infinitelyManyBoundedConsecutiveGaps_paperLiminfStatement⟩

theorem paperLiminfStatement_iff_boundedGapsStatement :
    paperLiminfStatement ↔ boundedGapsStatement := by
  rw [paperLiminfStatement_iff_consecutive,
    ← boundedGapsStatement_iff_consecutive]

end BoundedGaps
