import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowTerminalOccurrence

/-!
# Multiplicity-preserving terminal flatten for the Section 6 tree

Only canonical fuel-built trees receive a public signed-sum correctness theorem. The terminal
list is not deduplicated or converted to a Finset.
-/

namespace PrimesRestrictedDigits

noncomputable section

def SectionSixLowTerminalOccurrence.signedValue
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell} :
    SectionSixLowTerminalOccurrence root -> Real
  | .base occurrence =>
      (-1 : Real) ^ occurrence.parent.steps.length *
        sectionSixLowTOccurrenceValue digit length occurrence
  | .strictHigh occurrence =>
      (-1 : Real) ^ (occurrence.parent.steps.length + 1) *
        sectionSixLowVOccurrenceValue digit length occurrence
  | .repeatedLow occurrence =>
      (-1 : Real) ^ (occurrence.parent.steps.length + 1) *
        sectionSixLowRUOccurrenceValue digit length occurrence
  | .repeatedHigh occurrence =>
      (-1 : Real) ^ (occurrence.parent.steps.length + 1) *
        sectionSixLowRVOccurrenceValue digit length occurrence

theorem SectionSixLowVOccurrence.value_eq_stateStrictTerm
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowVOccurrence root) :
    sectionSixLowVOccurrenceValue digit length occurrence =
      sectionSixStateStrictTerm digit length occurrence.state.2
        (occurrence.q : Real) := by
  have h := sectionSixStrictPrimeTerm_eq_stateStrictTerm digit length
    occurrence.parent.target.state.2 SectionSixStateKind.V
    occurrence.prime occurrence.order
  simpa [sectionSixLowVOccurrenceValue, SectionSixLowVOccurrence.state,
    sectionSixStateVStep, sectionSixStateStepChild] using h

theorem SectionSixLowRUOccurrence.value_eq_stateWeakTerm
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRUOccurrence root) :
    sectionSixLowRUOccurrenceValue digit length occurrence =
      sectionSixStateWeakTerm digit length occurrence.state.2
        (occurrence.q : Real) := by
  have h := sectionSixRepeatedPrimeTerm_eq_stateWeakTerm digit length
    occurrence.parent.target.state.2 SectionSixStateKind.RU
    occurrence.prime occurrence.order
  simpa [sectionSixLowRUOccurrenceValue, SectionSixLowRUOccurrence.state,
    sectionSixStateRUStep, sectionSixStateStepChild] using h

theorem SectionSixLowRVOccurrence.value_eq_stateWeakTerm
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRVOccurrence root) :
    sectionSixLowRVOccurrenceValue digit length occurrence =
      sectionSixStateWeakTerm digit length occurrence.state.2
        (occurrence.q : Real) := by
  have h := sectionSixRepeatedPrimeTerm_eq_stateWeakTerm digit length
    occurrence.parent.target.state.2 SectionSixStateKind.RV
    occurrence.prime occurrence.order
  simpa [sectionSixLowRVOccurrenceValue, SectionSixLowRVOccurrence.state,
    sectionSixStateRVStep, sectionSixStateStepChild] using h

def sectionSixLowTerminalOccurrences
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell} :
    SectionSixLowOccurrenceTree root ->
      List (SectionSixLowTerminalOccurrence root)
  | .residualActive _ => []
  | .expanded base branches vLeaves ruLeaves rvLeaves =>
      .base base ::
        (branches.flatMap fun branch =>
          sectionSixLowTerminalOccurrences branch.2) ++
        vLeaves.map .strictHigh ++
        ruLeaves.map .repeatedLow ++
        rvLeaves.map .repeatedHigh
termination_by tree => sizeOf tree
decreasing_by
  have hbranch : sizeOf branch < sizeOf branches :=
    List.sizeOf_lt_of_mem (by assumption)
  rcases branch with ⟨edge, subtree⟩
  have hsnd : sizeOf subtree < sizeOf (edge, subtree) := by
    change sizeOf subtree < 1 + sizeOf edge + sizeOf subtree
    omega
  simp_wf
  omega

private theorem sum_map_flatMap_real
    {alpha beta : Type*} (terms : List alpha)
    (branches : alpha -> List beta) (value : beta -> Real) :
    ((terms.flatMap branches).map value).sum =
      (terms.map fun term => ((branches term).map value).sum).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      simp [ih]

private theorem sectionSixLowVOccurrences_sum_signedValue
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root) :
    ((sectionSixLowVOccurrences parent).map
        (SectionSixLowTerminalOccurrence.signedValue digit length ∘
          SectionSixLowTerminalOccurrence.strictHigh)).sum =
      (-1 : Real) ^ (parent.steps.length + 1) *
        ((sectionSixLowVOccurrences parent).map
          (sectionSixLowVOccurrenceValue digit length)).sum := by
  have hmap :
      (sectionSixLowVOccurrences parent).map
        (SectionSixLowTerminalOccurrence.signedValue digit length ∘
          SectionSixLowTerminalOccurrence.strictHigh) =
      (sectionSixLowVOccurrences parent).map (fun occurrence =>
        (-1 : Real) ^ (parent.steps.length + 1) *
          sectionSixLowVOccurrenceValue digit length occurrence) := by
    apply List.map_congr_left
    intro occurrence hoccurrence
    unfold sectionSixLowVOccurrences at hoccurrence
    rcases List.mem_map.mp hoccurrence with ⟨q, hq, rfl⟩
    rfl
  rw [hmap, List.sum_map_mul_left]

private theorem sectionSixLowRUOccurrences_sum_signedValue
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root) :
    ((sectionSixLowRUOccurrences parent).map
        (SectionSixLowTerminalOccurrence.signedValue digit length ∘
          SectionSixLowTerminalOccurrence.repeatedLow)).sum =
      (-1 : Real) ^ (parent.steps.length + 1) *
        ((sectionSixLowRUOccurrences parent).map
          (sectionSixLowRUOccurrenceValue digit length)).sum := by
  have hmap :
      (sectionSixLowRUOccurrences parent).map
        (SectionSixLowTerminalOccurrence.signedValue digit length ∘
          SectionSixLowTerminalOccurrence.repeatedLow) =
      (sectionSixLowRUOccurrences parent).map (fun occurrence =>
        (-1 : Real) ^ (parent.steps.length + 1) *
          sectionSixLowRUOccurrenceValue digit length occurrence) := by
    apply List.map_congr_left
    intro occurrence hoccurrence
    unfold sectionSixLowRUOccurrences at hoccurrence
    rcases List.mem_map.mp hoccurrence with ⟨q, hq, rfl⟩
    rfl
  rw [hmap, List.sum_map_mul_left]

private theorem sectionSixLowRVOccurrences_sum_signedValue
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root) :
    ((sectionSixLowRVOccurrences parent).map
        (SectionSixLowTerminalOccurrence.signedValue digit length ∘
          SectionSixLowTerminalOccurrence.repeatedHigh)).sum =
      (-1 : Real) ^ (parent.steps.length + 1) *
        ((sectionSixLowRVOccurrences parent).map
          (sectionSixLowRVOccurrenceValue digit length)).sum := by
  have hmap :
      (sectionSixLowRVOccurrences parent).map
        (SectionSixLowTerminalOccurrence.signedValue digit length ∘
          SectionSixLowTerminalOccurrence.repeatedHigh) =
      (sectionSixLowRVOccurrences parent).map (fun occurrence =>
        (-1 : Real) ^ (parent.steps.length + 1) *
          sectionSixLowRVOccurrenceValue digit length occurrence) := by
    apply List.map_congr_left
    intro occurrence hoccurrence
    unfold sectionSixLowRVOccurrences at hoccurrence
    rcases List.mem_map.mp hoccurrence with ⟨q, hq, rfl⟩
    rfl
  rw [hmap, List.sum_map_mul_left]

theorem sectionSixLowTerminalOccurrences_signedValue_ofFuel_eq
    (digit : Fin 10) (length fuel : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root)
    (hfree : (sectionSixLowOccurrenceTreeOfFuel root fuel occurrence).ResidualFree) :
    ((sectionSixLowTerminalOccurrences
      (sectionSixLowOccurrenceTreeOfFuel root fuel occurrence)).map
      (SectionSixLowTerminalOccurrence.signedValue digit length)).sum =
        sectionSixLowOccurrenceTreeSignedValue digit length
          (sectionSixLowOccurrenceTreeOfFuel root fuel occurrence) := by
  induction fuel generalizing occurrence with
  | zero => cases hfree
  | succ fuel ih =>
      rw [sectionSixLowOccurrenceTreeOfFuel,
        sectionSixLowOccurrenceTreeSignedValue]
      simp only [sectionSixLowTerminalOccurrences, List.map_append,
        List.sum_append, List.map_cons, List.sum_cons,
        SectionSixLowTerminalOccurrence.signedValue, List.map_map]
      cases hfree with
      | expanded children =>
      have branchFold : ∀ branches : List
          (SectionSixLowUOccurrence root × SectionSixLowOccurrenceTree root),
          (∀ branch ∈ branches, branch.2.ResidualFree) ->
          (∀ branch ∈ branches,
            ((sectionSixLowTerminalOccurrences branch.2).map
              (SectionSixLowTerminalOccurrence.signedValue digit length)).sum =
                sectionSixLowOccurrenceTreeSignedValue digit length branch.2) ->
          (((branches.flatMap fun branch =>
              sectionSixLowTerminalOccurrences branch.2).map
            (SectionSixLowTerminalOccurrence.signedValue digit length))).sum =
              (branches.map fun branch =>
                sectionSixLowOccurrenceTreeSignedValue digit length branch.2).sum := by
        intro branches hfreeBranches hfoldBranches
        induction branches with
        | nil => simp
        | cons branch rest ihrest =>
            simp only [List.flatMap_cons, List.map_append, List.sum_append,
              List.map_cons, List.sum_cons]
            rw [hfoldBranches branch List.mem_cons_self]
            apply congrArg (fun value : Real =>
              sectionSixLowOccurrenceTreeSignedValue digit length branch.2 + value)
            exact ihrest
              (fun child hchild =>
                hfreeBranches child (List.mem_cons_of_mem branch hchild))
              (fun child hchild =>
                hfoldBranches child (List.mem_cons_of_mem branch hchild))
      have hbranches :
          ((((((sectionSixLowUOccurrences occurrence).map fun branch =>
              (branch, sectionSixLowOccurrenceTreeOfFuel root fuel
                branch.child)).flatMap fun branch =>
                  sectionSixLowTerminalOccurrences branch.2).map
              (SectionSixLowTerminalOccurrence.signedValue digit length))).sum) =
            (((sectionSixLowUOccurrences occurrence).map fun branch =>
              (branch, sectionSixLowOccurrenceTreeOfFuel root fuel
                branch.child)).map fun branch =>
              sectionSixLowOccurrenceTreeSignedValue digit length branch.2).sum := by
        apply branchFold
        · exact children
        · intro branch hbranch
          rcases List.mem_map.mp hbranch with ⟨edge, hedge, rfl⟩
          exact ih edge.child (children _
            (List.mem_map.mpr ⟨edge, hedge, rfl⟩))
      rw [hbranches, sectionSixLowVOccurrences_sum_signedValue,
        sectionSixLowRUOccurrences_sum_signedValue,
        sectionSixLowRVOccurrences_sum_signedValue]
      rw [pow_succ]
      simp only [sectionSixLowTOccurrenceOfActive, List.map_map,
        ]
      ring

theorem sectionSixSourceBandRoot_terminalOccurrences_sum_eq_sourceTerm
    {epsilon : Real} {length ell : Nat}
    (hlength : 1 ≤ length)
    {region : Set (Fin ell → Real)}
    (band : SectionSixStateBand)
    (p : Fin ell → Nat)
    (hp : IsPropositionSixOnePrimeTuple epsilon length region p)
    (delta : Real)
    (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (hband : sectionSixSourceBandMembership band
      ((10 ^ length : Nat) : Real)
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleProduct p : Real))
    (hcutoff_le_X :
      sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ≤
        ((10 ^ length : Nat) : Real))
    (digit : Fin 10) :
    let root := sectionSixSourceBandRoot hlength band p hp delta hdeltaGap
      hband hcutoff_le_X
    let tree := sectionSixLowOccurrenceTreeOfFuel root
      (Nat.ceil (1 / delta) + 1) (sectionSixLowRootOccurrence root)
    ((sectionSixLowTerminalOccurrences tree).map
      (SectionSixLowTerminalOccurrence.signedValue digit length)).sum =
        sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
          (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) := by
  dsimp only
  have hfree := sectionSixSourceBandRoot_occurrenceTree_residualFree
    hlength band p hp delta hdelta hdeltaGap hband hcutoff_le_X
  rw [sectionSixLowTerminalOccurrences_signedValue_ofFuel_eq
    digit length _ _ hfree]
  exact sectionSixSourceBandRoot_occurrenceTreeSignedValue_eq_sourceTerm
    hlength band p hp delta hdeltaGap hband hcutoff_le_X digit _

end

end PrimesRestrictedDigits
