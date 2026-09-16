import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowStrictPathConstruction
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowOccurrenceTreeCompleteness
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixSourceTerminalContribution

/-!
# Exact terminal-V states occur in the canonical source tree

An exact recurrence state of kind `V` over one attached source tuple recovers its descending
strict-low path and final strict-high occurrence. This is the finite converse implicit in the
proof of Proposition 6.1 of `MAYNARD-PRD-PUBLISHED`, pp. 156--157.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Every exact terminal-V state over an attached source tuple is represented
by a strict-high occurrence in that source's canonical terminal list. -/
theorem exists_sectionSixSourceMemberStrictHighTerminalOccurrence_of_exactVState
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band})
    (state : SectionSixAnyState band ell)
    (houter : state.2.outer = source.1)
    (hV : state.2.kind = .V)
    (hexact : IsSectionSixRecurrenceState
      ((10 ^ length : Nat) : Real) delta (sectionSixThetaGap epsilon)
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) state.2) :
    exists leaf : SectionSixLowVOccurrence
        (sectionSixSourceBandRootOfMember hepsilon hepsilonSmall hlength
          hdeltaGap band source),
      SectionSixLowTerminalOccurrence.strictHigh leaf ∈
          sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall
            hlength hdeltaGap band source ∧
        leaf.state = state := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let theta : Real := sectionSixThetaGap epsilon
  let R : Real := sectionSixStateBandCutoff band X
    (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
  let y : Real := X ^ delta
  let root := sectionSixSourceBandRootOfMember hepsilon hepsilonSmall
    hlength hdeltaGap band source
  have hcutoff :
      sectionSixStateCutoffPredicate .V R state.1 state.2.inner := by
    simpa only [IsSectionSixRecurrenceState, hV, X, R] using hexact.2
  rcases hcutoff with
    ⟨q, rest, hinner, _hqDvd, hlower, hupper⟩
  have hqPrime : q.Prime := by
    apply state.2.innerPrime q
    rw [hinner]
    simp
  have hstateModulus :
      state.1 = (root.state.1 * rest.reverse.prod) * q := by
    rw [<- state.2.product_eq]
    simp only [houter, hinner, List.prod_cons, List.prod_reverse]
    simp [root, sectionSixSourceBandRootOfMember, sectionSixSourceBandRoot]
    ring
  have hparentCutoff :
      (((root.state.1 * rest.reverse.prod : Nat) : Real) <= R) := by
    apply le_of_mul_le_mul_right ?_ (Nat.cast_pos.mpr hqPrime.pos)
    rw [<- Nat.cast_mul, <- hstateModulus]
    exact hupper
  have hstepsPrime : forall p, p ∈ rest.reverse -> p.Prime := by
    intro p hp
    apply state.2.innerPrime p
    rw [hinner]
    exact List.mem_cons_of_mem q (List.mem_reverse.mp hp)
  have hrestSortedLE : rest.SortedLE := by
    have hsorted := state.2.innerSorted
    rw [hinner, List.sortedLE_iff_pairwise] at hsorted
    rw [List.sortedLE_iff_pairwise]
    exact (List.pairwise_cons.mp hsorted).2
  have hstepsSorted : rest.reverse.SortedGE := hrestSortedLE.reverse
  have hqSteps : forall p, p ∈ rest.reverse -> q <= p := by
    intro p hp
    have hsorted := state.2.innerSorted
    rw [hinner, List.sortedLE_iff_pairwise] at hsorted
    exact (List.pairwise_cons.mp hsorted).1 p (List.mem_reverse.mp hp)
  have hstepsRange : forall p, p ∈ rest.reverse ->
      y < (p : Real) ∧ (p : Real) <= root.upper := by
    intro p hp
    have hpRange := hexact.1 p (by
      rw [hinner]
      exact List.mem_cons_of_mem q (List.mem_reverse.mp hp))
    change X ^ delta < (p : Real) ∧ (p : Real) <= X ^ theta
    simpa only [X, theta] using hpRange
  obtain ⟨parent, path⟩ := exists_sectionSixLowStrictPath_of_sorted_primes
    root rest.reverse hstepsPrime hstepsRange hstepsSorted hparentCutoff
  have hqRange := hexact.1 q (by rw [hinner]; simp)
  have hqUpper : (q : Real) <= parent.upper :=
    sectionSixLowStrictPath_final_upper path (by
      change (q : Real) <= X ^ theta
      simpa only [X, theta] using hqRange.2) hqSteps
  have hcross : R < ((parent.state.1 * q : Nat) : Real) := by
    rw [sectionSixLowStrictPath_target_modulus path, <- hstateModulus]
    exact hlower
  have hqHigh : q ∈ sectionSixStateHighPrimeInterval
      parent.state R y parent.upper := by
    apply mem_sectionSixStateHighPrimeInterval.mpr
    refine ⟨mem_sievePrimeInterval.mpr ⟨hqPrime, ?_, hqUpper⟩, hcross⟩
    change X ^ delta < (q : Real)
    simpa only [X] using hqRange.1
  have hXNat : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    change (1 : Real) < ((10 ^ length : Nat) : Real)
    exact_mod_cast hXNat
  obtain ⟨leaf, hleafParent, _hleafSteps, hleafQ, hleafMem⟩ :=
    exists_sectionSixLowStrictHigh_terminalOccurrence_canonicalFuel
      root hX hdelta path hqHigh
  have hleafMember :
      SectionSixLowTerminalOccurrence.strictHigh leaf ∈
        sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall
          hlength hdeltaGap band source := by
    simpa [sectionSixSourceMemberTerminalOccurrences, root] using hleafMem
  have hmodulus : leaf.state.1 = state.1 := by
    change leaf.parent.target.state.1 * leaf.q = state.1
    rw [hleafParent, hleafQ, sectionSixLowStrictPath_target_modulus path]
    exact hstateModulus.symm
  have hkindLeaf : leaf.state.2.kind = .V := rfl
  have houterLeaf : leaf.state.2.outer = source.1 := by
    change leaf.parent.target.state.2.outer = source.1
    rw [hleafParent, sectionSixLowStrictPath_target_outer path]
    rfl
  have hpair :
      (leaf.state.2.kind, leaf.state.2.outer) =
        (state.2.kind, state.2.outer) :=
    Prod.ext (hkindLeaf.trans hV.symm) (houterLeaf.trans houter.symm)
  have hstateEq : leaf.state = state := by
    cases state with
    | mk D stateData =>
        dsimp only at hmodulus ⊢
        subst D
        apply Sigma.ext (x := leaf.state)
          (y := ⟨leaf.state.1, stateData⟩) rfl
        simp only [heq_eq_eq]
        exact sectionSixRecurrenceState_pair_injective hpair
  exact ⟨leaf, hleafMember, hstateEq⟩

/-- Exact terminal-V states therefore belong to the canonical source-member
terminal-state list. -/
theorem mem_sectionSixSourceMemberTerminalStates_of_exactVState
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band})
    (state : SectionSixAnyState band ell)
    (houter : state.2.outer = source.1)
    (hV : state.2.kind = .V)
    (hexact : IsSectionSixRecurrenceState
      ((10 ^ length : Nat) : Real) delta (sectionSixThetaGap epsilon)
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) state.2) :
    state ∈ sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall
      hlength hdeltaGap band source := by
  obtain ⟨leaf, hleaf, hstate⟩ :=
    exists_sectionSixSourceMemberStrictHighTerminalOccurrence_of_exactVState
      hepsilon hepsilonSmall hlength hdelta hdeltaGap band source state
        houter hV hexact
  rw [<- sectionSixSourceMemberTerminalOccurrences_map_state hepsilon
    hepsilonSmall hlength hdeltaGap band source]
  exact List.mem_map.mpr
    ⟨SectionSixLowTerminalOccurrence.strictHigh leaf, hleaf, hstate⟩

end

end PrimesRestrictedDigits
