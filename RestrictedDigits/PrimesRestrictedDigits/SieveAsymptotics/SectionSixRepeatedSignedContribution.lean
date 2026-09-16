import PrimesRestrictedDigits.SieveAsymptotics.SectionSixSourceTerminalContribution
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedTerminalValueBound

/-!
# Repeated signed terminal contribution

This file removes the literal occurrence-depth sign only after taking an absolute value, then
uses global one-band `Nodup` theorem to reindex the resulting state magnitudes onto
terminal-state Finset.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSix_sum_map_flatMap_real
    {alpha beta : Type*} (terms : List alpha)
    (branches : alpha → List beta) (value : beta → Real) :
    ((terms.flatMap branches).map value).sum =
      (terms.map fun term => ((branches term).map value).sum).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [ih]

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

private noncomputable def sectionSixSourceMemberRepeatedSignedContribution
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band}) : Real :=
  ((sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall hlength
    hdeltaGap band source).map fun term =>
      if sectionSixRepeatedTerminalPredicate term.state then
        term.signedValue digit length else 0).sum

private theorem abs_sectionSixSelectedRepeatedOccurrence
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (term : SectionSixLowTerminalOccurrence root) :
    abs (if sectionSixRepeatedTerminalPredicate term.state then
      term.signedValue digit length else 0) =
      abs (sectionSixRepeatedTerminalStateValue digit length y term.state) := by
  cases term with
  | base occurrence =>
      simp [sectionSixRepeatedTerminalStateValue,
        sectionSixRepeatedTerminalPredicate]
  | strictHigh occurrence =>
      simp [sectionSixRepeatedTerminalStateValue,
        sectionSixRepeatedTerminalPredicate]
  | repeatedLow occurrence =>
      simp only [SectionSixLowTerminalOccurrence.signedValue]
      rw [SectionSixLowRUOccurrence.value_eq_stateWeakTerm]
      simp [sectionSixRepeatedTerminalStateValue, sectionSixTerminalStateValue,
        sectionSixRepeatedTerminalPredicate, sectionSixTerminalFirstInnerPrime,
        SectionSixLowTerminalOccurrence.state, SectionSixLowRUOccurrence.state,
        sectionSixStateRUStep, sectionSixStateStepChild, sectionSixRepeatedChild]
  | repeatedHigh occurrence =>
      simp only [SectionSixLowTerminalOccurrence.signedValue]
      rw [SectionSixLowRVOccurrence.value_eq_stateWeakTerm]
      simp [sectionSixRepeatedTerminalStateValue, sectionSixTerminalStateValue,
        sectionSixRepeatedTerminalPredicate, sectionSixTerminalFirstInnerPrime,
        SectionSixLowTerminalOccurrence.state, SectionSixLowRVOccurrence.state,
        sectionSixStateRVStep, sectionSixStateStepChild, sectionSixRepeatedChild]

private theorem abs_sectionSixSourceMemberRepeatedSignedContribution_le_states
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band}) :
    abs (sectionSixSourceMemberRepeatedSignedContribution digit hepsilon
      hepsilonSmall hlength hdeltaGap band source) ≤
      ((sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall hlength
        hdeltaGap band source).map fun state =>
          abs (sectionSixRepeatedTerminalStateValue digit length
            (((10 ^ length : Nat) : Real) ^ delta) state)).sum := by
  unfold sectionSixSourceMemberRepeatedSignedContribution
  let terms := sectionSixSourceMemberTerminalOccurrences hepsilon
    hepsilonSmall hlength hdeltaGap band source
  let selected : SectionSixLowTerminalOccurrence
      (sectionSixSourceBandRootOfMember hepsilon hepsilonSmall hlength
        hdeltaGap band source) → Real := fun term =>
    if sectionSixRepeatedTerminalPredicate term.state then
      term.signedValue digit length else 0
  let stateValue : SectionSixAnyState band ell → Real := fun state =>
    abs (sectionSixRepeatedTerminalStateValue digit length
      (((10 ^ length : Nat) : Real) ^ delta) state)
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
      exact abs_sectionSixSelectedRepeatedOccurrence digit length term
    _ = ((terms.map SectionSixLowTerminalOccurrence.state).map stateValue).sum := by
      simp [List.map_map, Function.comp_def]
    _ = _ := by
      rw [sectionSixSourceMemberTerminalOccurrences_map_state]

/--
The absolute signed contribution of the corrected repeated terminal occurrences is bounded by
the corresponding state-Finset magnitude sum. Only signed cancellation is discarded.
-/
theorem abs_sectionSixSourceBandRepeatedSignedContribution_le_stateFinset
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) :
    abs (sectionSixSourceBandSelectedSignedContribution digit region hepsilon
      hepsilonSmall hlength hdeltaGap band
        sectionSixRepeatedTerminalPredicate) ≤
      ∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
          hepsilonSmall hlength hdeltaGap band,
        abs (sectionSixRepeatedTerminalStateValue digit length
          (((10 ^ length : Nat) : Real) ^ delta) state) := by
  classical
  unfold sectionSixSourceBandSelectedSignedContribution
  let sources :=
    (sectionSixSourceBandPrimeTuples epsilon ell region length band).attach.toList
  let memberValue :
      {p // p ∈ sectionSixSourceBandPrimeTuples
        epsilon ell region length band} → Real := fun source =>
    sectionSixSourceMemberRepeatedSignedContribution digit hepsilon
      hepsilonSmall hlength hdeltaGap band source
  let memberStates :
      {p // p ∈ sectionSixSourceBandPrimeTuples epsilon ell region length band} →
        List (SectionSixAnyState band ell) := fun source =>
    sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall hlength
      hdeltaGap band source
  let stateValue : SectionSixAnyState band ell → Real := fun state =>
    abs (sectionSixRepeatedTerminalStateValue digit length
      (((10 ^ length : Nat) : Real) ^ delta) state)
  change abs ((sources.map memberValue).sum) ≤ _
  calc
    _ ≤ (sources.map fun source => abs (memberValue source)).sum := by
      simpa [List.map_map, Function.comp_def] using
        sectionSix_abs_list_sum_le_sum_abs (sources.map memberValue)
    _ ≤ (sources.map fun source => ((memberStates source).map stateValue).sum).sum := by
      apply sectionSix_list_sum_le_sum
      intro source hsource
      exact abs_sectionSixSourceMemberRepeatedSignedContribution_le_states
        digit hepsilon hepsilonSmall hlength hdeltaGap band source
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
