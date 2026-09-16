import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowStrictPath

/-!
# Constructing strict-low paths from ordered primes

A descending chronological list of primes whose complete product remains below the band cutoff
determines a canonical strict-low path. The complete product bound supplies every intermediate
cutoff, so no prefix hypotheses are needed.

This is the implementation bridge implicit in the proof of Proposition 6.1 of
`MAYNARD-PRD-PUBLISHED`, pp. 156--157.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A strict-low path multiplies its initial modulus by the product of its
chronological prime steps. -/
theorem sectionSixLowStrictPath_target_modulus
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat}
    (path : SectionSixLowStrictPath start target steps) :
    target.state.1 = start.state.1 * steps.prod := by
  induction path with
  | nil node => simp
  | @cons node target rest p hp tail ih =>
      rw [ih]
      simp [sectionSixLowActiveChild_state, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm]

/-- A natural below the initial upper endpoint and every chronological step
is below the final upper endpoint. -/
theorem sectionSixLowStrictPath_final_upper
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat}
    (path : SectionSixLowStrictPath start target steps)
    {q : Nat}
    (hroot : (q : Real) <= start.upper)
    (hsteps : forall p, p ∈ steps -> q <= p) :
    (q : Real) <= target.upper := by
  induction path with
  | nil node => exact hroot
  | @cons node target rest p hp tail ih =>
      apply ih
      · change (q : Real) <= (p : Real)
        exact_mod_cast hsteps p (by simp)
      · intro r hr
        exact hsteps r (by simp [hr])

/-- Ordered prime data with one complete-product cutoff produces the exact
strict-low path. Positivity of each unused suffix product gives all earlier
cutoff bounds. -/
theorem exists_sectionSixLowStrictPath_of_sorted_primes
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell)
    (steps : List Nat)
    (hprime : forall p, p ∈ steps -> p.Prime)
    (hrange : forall p, p ∈ steps ->
      y < (p : Real) ∧ (p : Real) <= root.upper)
    (hsorted : steps.SortedGE)
    (hfull : ((root.state.1 * steps.prod : Nat) : Real) <= R) :
    exists target, SectionSixLowStrictPath root target steps := by
  induction steps generalizing root with
  | nil =>
      exact ⟨root, SectionSixLowStrictPath.nil root⟩
  | cons p rest ih =>
      have hpPrime : p.Prime := hprime p (by simp)
      have hpRange := hrange p (by simp)
      have htailPrime : forall q, q ∈ rest -> q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have htailSorted : rest.SortedGE := by
        rw [List.sortedGE_iff_pairwise] at hsorted ⊢
        exact (List.pairwise_cons.mp hsorted).2
      have htailProductPos : 0 < rest.prod := by
        apply List.prod_pos
        intro q hq
        exact (htailPrime q hq).pos
      have hpCutoff : ((root.state.1 * p : Nat) : Real) <= R := by
        apply le_trans ?_ hfull
        rw [List.prod_cons, <- Nat.mul_assoc]
        exact_mod_cast Nat.le_mul_of_pos_right
          (root.state.1 * p) htailProductPos
      have hpMem : p ∈ sectionSixStateLowPrimeInterval
          root.state R y root.upper :=
        mem_sectionSixStateLowPrimeInterval.mpr
          ⟨mem_sievePrimeInterval.mpr ⟨hpPrime, hpRange⟩, hpCutoff⟩
      let child := sectionSixLowActiveChild root p hpMem
      have htailRange : forall q, q ∈ rest ->
          y < (q : Real) ∧ (q : Real) <= child.upper := by
        intro q hq
        have hqRange := hrange q (by simp [hq])
        have hpGe : p >= q := by
          rw [List.sortedGE_iff_pairwise] at hsorted
          exact (List.pairwise_cons.mp hsorted).1 q hq
        exact ⟨hqRange.1, by
          change (q : Real) <= (p : Real)
          exact_mod_cast hpGe⟩
      have htailFull :
          ((child.state.1 * rest.prod : Nat) : Real) <= R := by
        simpa [child, sectionSixLowActiveChild_state, Nat.mul_assoc] using
          hfull
      obtain ⟨target, hpath⟩ :=
        ih child htailPrime htailRange htailSorted htailFull
      exact ⟨target, SectionSixLowStrictPath.cons hpMem hpath⟩

end

end PrimesRestrictedDigits
