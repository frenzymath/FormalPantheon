import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedSignedContribution

/-!
# Nonrepeated signed Section 6 terminal contributions

The Boolean complement of the corrected repeated selector contains exactly the canonical `T`
and `V` terminals. This file also supplies the generic occurrence-to-state triangle bound used
by the Fundamental branch.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Boolean selector for canonical terminal states of kind `T`. -/
def sectionSixTerminalTPredicate
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Bool :=
  state.2.kind == .T

/-- Boolean selector for canonical terminal states of kind `V`. -/
def sectionSixTerminalVPredicate
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Bool :=
  state.2.kind == .V

private theorem sectionSix_abs_list_sum_le_sum_abs (values : List Real) :
    abs values.sum ≤ (values.map abs).sum := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simpa only [List.sum_cons, List.map_cons] using
        (abs_add_le value values.sum).trans (add_le_add le_rfl ih)

private theorem sectionSix_list_sum_le_sum
    {alpha : Type*} (terms : List alpha) (f g : alpha → Real)
    (hfg : ∀ term ∈ terms, f term ≤ g term) :
    (terms.map f).sum ≤ (terms.map g).sum := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hfg term List.mem_cons_self)
        (ih fun item hitem => hfg item (List.mem_cons_of_mem term hitem))

private theorem sectionSix_sum_map_flatMap_real
    {alpha beta : Type*} (terms : List alpha)
    (branches : alpha → List beta) (value : beta → Real) :
    ((terms.flatMap branches).map value).sum =
      (terms.map fun term => ((branches term).map value).sum).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [ih]

private theorem abs_sectionSixSelectedTerminalOccurrence
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (predicate : SectionSixAnyState band ell → Bool)
    (term : SectionSixLowTerminalOccurrence root) :
    abs (if predicate term.state then term.signedValue digit length else 0) =
      abs (if predicate term.state then
        sectionSixTerminalStateValue digit length y term.state else 0) := by
  by_cases hpredicate : predicate term.state = true
  · simp only [if_pos hpredicate]
    cases term with
    | base occurrence =>
        simp [SectionSixLowTerminalOccurrence.signedValue,
          sectionSixTerminalStateValue, sectionSixLowTOccurrenceValue,
          SectionSixLowTerminalOccurrence.state, SectionSixLowTOccurrence.state]
    | strictHigh occurrence =>
        simp only [SectionSixLowTerminalOccurrence.signedValue]
        rw [SectionSixLowVOccurrence.value_eq_stateStrictTerm]
        simp [sectionSixTerminalStateValue, sectionSixTerminalFirstInnerPrime,
          SectionSixLowTerminalOccurrence.state, SectionSixLowVOccurrence.state,
          sectionSixStateVStep, sectionSixStateStepChild, sectionSixStrictChild]
    | repeatedLow occurrence =>
        simp only [SectionSixLowTerminalOccurrence.signedValue]
        rw [SectionSixLowRUOccurrence.value_eq_stateWeakTerm]
        simp [sectionSixTerminalStateValue, sectionSixTerminalFirstInnerPrime,
          SectionSixLowTerminalOccurrence.state, SectionSixLowRUOccurrence.state,
          sectionSixStateRUStep, sectionSixStateStepChild, sectionSixRepeatedChild]
    | repeatedHigh occurrence =>
        simp only [SectionSixLowTerminalOccurrence.signedValue]
        rw [SectionSixLowRVOccurrence.value_eq_stateWeakTerm]
        simp [sectionSixTerminalStateValue, sectionSixTerminalFirstInnerPrime,
          SectionSixLowTerminalOccurrence.state, SectionSixLowRVOccurrence.state,
          sectionSixStateRVStep, sectionSixStateStepChild, sectionSixRepeatedChild]
  · have hfalse : predicate term.state = false :=
      Bool.eq_false_of_not_eq_true hpredicate
    simp [hfalse]

private theorem abs_sectionSixSourceMemberSelectedSignedContribution_le_states
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band})
    (predicate : SectionSixAnyState band ell → Bool) :
    abs (((sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall
      hlength hdeltaGap band source).map fun term =>
        if predicate term.state then term.signedValue digit length else 0).sum) ≤
      ((sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall hlength
        hdeltaGap band source).map fun state =>
          abs (if predicate state then
            sectionSixTerminalStateValue digit length
              (((10 ^ length : Nat) : Real) ^ delta) state else 0)).sum := by
  let terms := sectionSixSourceMemberTerminalOccurrences hepsilon
    hepsilonSmall hlength hdeltaGap band source
  let selected : SectionSixLowTerminalOccurrence
      (sectionSixSourceBandRootOfMember hepsilon hepsilonSmall hlength
        hdeltaGap band source) → Real := fun term =>
    if predicate term.state then term.signedValue digit length else 0
  let stateValue : SectionSixAnyState band ell → Real := fun state =>
    abs (if predicate state then sectionSixTerminalStateValue digit length
      (((10 ^ length : Nat) : Real) ^ delta) state else 0)
  change abs ((terms.map selected).sum) ≤
    ((sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall hlength
      hdeltaGap band source).map stateValue).sum
  calc
    _ ≤ ((terms.map selected).map abs).sum :=
      sectionSix_abs_list_sum_le_sum_abs (terms.map selected)
    _ = (terms.map fun term => stateValue term.state).sum := by
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro term hterm
      exact abs_sectionSixSelectedTerminalOccurrence digit length predicate term
    _ = ((terms.map SectionSixLowTerminalOccurrence.state).map
        stateValue).sum := by
      simp [List.map_map, Function.comp_def]
    _ = _ := by
      rw [sectionSixSourceMemberTerminalOccurrences_map_state]

/-- On canonical terminal occurrences, the Boolean complement of `RU/RV` is
exactly the disjoint signed contribution of `T` and `V`. -/
theorem sectionSixSourceBandSelectedSignedContribution_nonrepeated_eq_T_add_V
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) :
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
        hepsilonSmall hlength hdeltaGap band
          (fun state => !sectionSixRepeatedTerminalPredicate state) =
      sectionSixSourceBandSelectedSignedContribution digit region hepsilon
          hepsilonSmall hlength hdeltaGap band sectionSixTerminalTPredicate +
        sectionSixSourceBandSelectedSignedContribution digit region hepsilon
          hepsilonSmall hlength hdeltaGap band sectionSixTerminalVPredicate := by
  unfold sectionSixSourceBandSelectedSignedContribution
  let sources :=
    (sectionSixSourceBandPrimeTuples epsilon ell region length band).attach.toList
  change (sources.map fun source =>
      ((sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall hlength
        hdeltaGap band source).map fun term =>
          if !sectionSixRepeatedTerminalPredicate term.state then
            term.signedValue digit length else 0).sum).sum =
    (sources.map fun source =>
      ((sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall hlength
        hdeltaGap band source).map fun term =>
          if sectionSixTerminalTPredicate term.state then
            term.signedValue digit length else 0).sum).sum +
    (sources.map fun source =>
      ((sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall hlength
        hdeltaGap band source).map fun term =>
          if sectionSixTerminalVPredicate term.state then
            term.signedValue digit length else 0).sum).sum
  calc
    _ = (sources.map fun source =>
        ((sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall
          hlength hdeltaGap band source).map fun term =>
            (if sectionSixTerminalTPredicate term.state then
              term.signedValue digit length else 0) +
            (if sectionSixTerminalVPredicate term.state then
              term.signedValue digit length else 0)).sum).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro source hsource
      apply congrArg List.sum
      apply List.map_congr_left
      intro term hterm
      cases term <;>
        simp [sectionSixRepeatedTerminalPredicate, sectionSixTerminalTPredicate,
          sectionSixTerminalVPredicate]
    _ = _ := by
      simp only [List.sum_map_add]

/-- The absolute selected signed occurrence contribution is bounded by the
same selector applied to the sign-free terminal values on the canonical
one-band state Finset. -/
theorem abs_sectionSixSourceBandSelectedSignedContribution_le_terminalStateFinset
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (predicate : SectionSixAnyState band ell → Bool) :
    abs (sectionSixSourceBandSelectedSignedContribution digit region hepsilon
      hepsilonSmall hlength hdeltaGap band predicate) ≤
      ∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
          hepsilonSmall hlength hdeltaGap band,
        abs (if predicate state then
          sectionSixTerminalStateValue digit length
            (((10 ^ length : Nat) : Real) ^ delta) state else 0) := by
  classical
  unfold sectionSixSourceBandSelectedSignedContribution
  let sources :=
    (sectionSixSourceBandPrimeTuples epsilon ell region length band).attach.toList
  let memberValue :
      {p // p ∈ sectionSixSourceBandPrimeTuples
        epsilon ell region length band} → Real := fun source =>
    ((sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall hlength
      hdeltaGap band source).map fun term =>
        if predicate term.state then term.signedValue digit length else 0).sum
  let memberStates :
      {p // p ∈ sectionSixSourceBandPrimeTuples epsilon ell region length band} →
        List (SectionSixAnyState band ell) := fun source =>
    sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall hlength
      hdeltaGap band source
  let stateValue : SectionSixAnyState band ell → Real := fun state =>
    abs (if predicate state then sectionSixTerminalStateValue digit length
      (((10 ^ length : Nat) : Real) ^ delta) state else 0)
  change abs ((sources.map memberValue).sum) ≤ _
  calc
    _ ≤ (sources.map fun source => abs (memberValue source)).sum := by
      simpa [List.map_map, Function.comp_def] using
        sectionSix_abs_list_sum_le_sum_abs (sources.map memberValue)
    _ ≤ (sources.map fun source => ((memberStates source).map
        stateValue).sum).sum := by
      apply sectionSix_list_sum_le_sum
      intro source hsource
      exact abs_sectionSixSourceMemberSelectedSignedContribution_le_states
        digit hepsilon hepsilonSmall hlength hdeltaGap band source predicate
    _ = ((sources.flatMap memberStates).map stateValue).sum :=
      (sectionSix_sum_map_flatMap_real sources memberStates stateValue).symm
    _ = ((sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
        hlength hdeltaGap band).map stateValue).sum := by rfl
    _ = _ := by
      have hnodup := sectionSixSourceBandTerminalStates_nodup region hepsilon
        hepsilonSmall hlength hdeltaGap band
      change ((sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
        hlength hdeltaGap band).map stateValue).sum =
          (sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
            hlength hdeltaGap band).toFinset.sum stateValue
      exact (List.sum_toFinset stateValue hnodup).symm

end

end PrimesRestrictedDigits
