import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVCandidates

/-!
# Signed terminal V candidate contribution

The canonical recurrence sign is transported from terminal occurrences to their projected
states. The selected source contribution then becomes the exact signed sum over labeled
terminal-V cofactors and splits into arbitrary near and outside filters.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A terminal V state value is its exact ambient cofactor weight sum. -/
theorem sectionSixTerminalStateValue_eq_cofactorWeightSum_of_kind_eq_V
    (digit : Fin 10) (length : Nat) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) (hV : state.2.kind = .V) :
    sectionSixTerminalStateValue digit length y state =
      ∑ m ∈ sectionSixTerminalCofactorCarrier
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) y state,
        sectionSixWeight (paddedRestrictedNumbers digit length)
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
          ((restrictedDigitDensity digit : Real) *
            (((paddedRestrictedNumbers digit length).card : Real) /
              ((10 ^ length : Nat) : Real))) (m * state.1) := by
  simp [sectionSixTerminalStateValue, hV, sectionSixStateStrictTerm,
    sectionSixSiftedSum, sectionSixTerminalCofactorCarrier,
    sectionSixTerminalThreshold, sectionSixStateModulusPNat]

/-- The occurrence exponent equals the state-inner length on the canonical
source root, so V-selection preserves the exact signed value. -/
theorem sectionSixSelectedTerminalVOccurrence_eq_stateValue
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band})
    (term : SectionSixLowTerminalOccurrence
      (sectionSixSourceBandRootOfMember hepsilon hepsilonSmall hlength
        hdeltaGap band source)) :
    (if sectionSixTerminalVPredicate term.state then
        term.signedValue digit length else 0) =
      if sectionSixTerminalVPredicate term.state then
        sectionSixTerminalVStateSign term.state *
          sectionSixTerminalStateValue digit length
            (((10 ^ length : Nat) : Real) ^ delta) term.state
      else 0 := by
  cases term with
  | base occurrence =>
      simp [sectionSixTerminalVPredicate]
  | strictHigh occurrence =>
      have hinner :=
        sectionSixLowStrictPath_target_inner occurrence.parent.path
      have hrootInner :
          (sectionSixSourceBandRootOfMember hepsilon hepsilonSmall hlength
            hdeltaGap band source).state.2.inner = [] := by
        rfl
      rw [hrootInner] at hinner
      have hparentLength :
          occurrence.parent.target.state.2.inner.length =
            occurrence.parent.steps.length := by
        rw [hinner]
        simp
      have hstateLength :
          occurrence.state.2.inner.length =
            occurrence.parent.steps.length + 1 := by
        change
          (occurrence.q :: occurrence.parent.target.state.2.inner).length = _
        simp [hparentLength]
      have hvalue :
          sectionSixLowVOccurrenceValue digit length occurrence =
            sectionSixTerminalStateValue digit length
              (((10 ^ length : Nat) : Real) ^ delta) occurrence.state := by
        rw [SectionSixLowVOccurrence.value_eq_stateStrictTerm]
        simp [sectionSixTerminalStateValue, sectionSixTerminalFirstInnerPrime,
          SectionSixLowVOccurrence.state, sectionSixStateVStep,
          sectionSixStateStepChild, sectionSixStrictChild]
      have hV : sectionSixTerminalVPredicate occurrence.state = true := by
        simp [sectionSixTerminalVPredicate, SectionSixLowVOccurrence.state,
          sectionSixStateVStep, sectionSixStateStepChild, sectionSixStrictChild]
      change
        (if sectionSixTerminalVPredicate occurrence.state then
            (-1 : Real) ^ (occurrence.parent.steps.length + 1) *
              sectionSixLowVOccurrenceValue digit length occurrence
          else 0) =
          if sectionSixTerminalVPredicate occurrence.state then
            sectionSixTerminalVStateSign occurrence.state *
              sectionSixTerminalStateValue digit length
                (((10 ^ length : Nat) : Real) ^ delta) occurrence.state
          else 0
      rw [if_pos hV, if_pos hV, hvalue]
      simp only [sectionSixTerminalVStateSign, hstateLength]
  | repeatedLow occurrence =>
      simp [sectionSixTerminalVPredicate]
  | repeatedHigh occurrence =>
      simp [sectionSixTerminalVPredicate]

private theorem sectionSixTerminalV_sum_map_flatMap
    {alpha beta : Type*} (terms : List alpha)
    (branches : alpha -> List beta) (value : beta -> Real) :
    ((terms.flatMap branches).map value).sum =
      (terms.map fun term => ((branches term).map value).sum).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [ih]

/-- The selected occurrence sum is exactly the signed canonical state sum. -/
theorem sectionSixSourceBandSelectedSignedContribution_V_eq_stateSum
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) :
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
        hepsilonSmall hlength hdeltaGap band sectionSixTerminalVPredicate =
      ∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
          hepsilonSmall hlength hdeltaGap band,
        if sectionSixTerminalVPredicate state then
          sectionSixTerminalVStateSign state *
            sectionSixTerminalStateValue digit length
              (((10 ^ length : Nat) : Real) ^ delta) state
        else 0 := by
  classical
  let sources :=
    (sectionSixSourceBandPrimeTuples epsilon ell region length band).attach.toList
  let memberStates :
      {p // p ∈ sectionSixSourceBandPrimeTuples
        epsilon ell region length band} ->
        List (SectionSixAnyState band ell) := fun source =>
    sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall hlength
      hdeltaGap band source
  let stateValue : SectionSixAnyState band ell -> Real := fun state =>
    if sectionSixTerminalVPredicate state then
      sectionSixTerminalVStateSign state *
        sectionSixTerminalStateValue digit length
          (((10 ^ length : Nat) : Real) ^ delta) state
    else 0
  unfold sectionSixSourceBandSelectedSignedContribution
  change
    (sources.map fun source =>
      ((sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall
        hlength hdeltaGap band source).map fun term =>
          if sectionSixTerminalVPredicate term.state then
            term.signedValue digit length else 0).sum).sum = _
  calc
    _ = (sources.map fun source =>
        ((sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall
          hlength hdeltaGap band source).map fun term =>
            stateValue term.state).sum).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro source hsource
      apply congrArg List.sum
      apply List.map_congr_left
      intro term hterm
      exact sectionSixSelectedTerminalVOccurrence_eq_stateValue digit
        hepsilon hepsilonSmall hlength hdeltaGap band source term
    _ = (sources.map fun source =>
        ((memberStates source).map stateValue).sum).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro source hsource
      dsimp only [memberStates]
      rw [<- sectionSixSourceMemberTerminalOccurrences_map_state]
      simp [List.map_map, Function.comp_def]
    _ = ((sources.flatMap memberStates).map stateValue).sum :=
      (sectionSixTerminalV_sum_map_flatMap sources memberStates stateValue).symm
    _ = ((sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
        hlength hdeltaGap band).map stateValue).sum := by
      rfl
    _ = (sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
        hlength hdeltaGap band).toFinset.sum stateValue := by
      exact (List.sum_toFinset stateValue
        (sectionSixSourceBandTerminalStates_nodup region hepsilon
          hepsilonSmall hlength hdeltaGap band)).symm
    _ = _ := by
      rfl

/-- The exact full signed cofactor sum for one source band. -/
noncomputable def sectionSixSourceBandTerminalVFullSignedCandidateSum
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let A := paddedRestrictedNumbers digit length
  let B := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  ∑ candidate ∈ sectionSixSourceBandTerminalVFullCandidates region hepsilon
      hepsilonSmall hlength hdeltaGap band B y,
    candidate.signedWeight A B lambda

/-- The exact signed cofactor sum inside an arbitrary near carrier. -/
noncomputable def sectionSixSourceBandTerminalVNearSignedCandidateSum
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) (nearSet : Finset Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let A := paddedRestrictedNumbers digit length
  let B := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  ∑ candidate ∈ sectionSixSourceBandTerminalVNearCandidates region hepsilon
      hepsilonSmall hlength hdeltaGap band B y nearSet,
    candidate.signedWeight A B lambda

/-- The exact signed cofactor sum outside an arbitrary near carrier. -/
noncomputable def sectionSixSourceBandTerminalVOutsideSignedCandidateSum
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) (nearSet : Finset Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let A := paddedRestrictedNumbers digit length
  let B := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  ∑ candidate ∈ sectionSixSourceBandTerminalVOutsideCandidates region hepsilon
      hepsilonSmall hlength hdeltaGap band B y nearSet,
    candidate.signedWeight A B lambda

/-- The full signed candidate sum is the corresponding signed state sum. -/
theorem sectionSixSourceBandTerminalVFullSignedCandidateSum_eq_stateSum
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) :
    sectionSixSourceBandTerminalVFullSignedCandidateSum digit region hepsilon
        hepsilonSmall hlength hdeltaGap band y =
      ∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
          hepsilonSmall hlength hdeltaGap band,
        if sectionSixTerminalVPredicate state then
          sectionSixTerminalVStateSign state *
            sectionSixTerminalStateValue digit length y state
        else 0 := by
  classical
  simp only [sectionSixSourceBandTerminalVFullSignedCandidateSum,
    sectionSixSourceBandTerminalVFullCandidates]
  rw [Finset.sum_sigma, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro state hstate
  by_cases hV : sectionSixTerminalVPredicate state = true
  · have hkind : state.2.kind = .V := by
      simpa [sectionSixTerminalVPredicate] using hV
    rw [if_pos hV,
      sectionSixTerminalStateValue_eq_cofactorWeightSum_of_kind_eq_V
        digit length y state hkind]
    simp [hV, SectionSixTerminalVCandidate.signedWeight,
      SectionSixTerminalVCandidate.sign,
      SectionSixTerminalVCandidate.represented, Finset.mul_sum]
  · have hfalse : sectionSixTerminalVPredicate state = false :=
      Bool.eq_false_of_not_eq_true hV
    simp [hfalse]

/-- The selected recurrence contribution is the full signed candidate sum. -/
theorem sectionSixSourceBandSelectedSignedContribution_V_eq_fullSignedCandidateSum
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) :
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
        hepsilonSmall hlength hdeltaGap band sectionSixTerminalVPredicate =
      sectionSixSourceBandTerminalVFullSignedCandidateSum digit region
        hepsilon hepsilonSmall hlength hdeltaGap band
          (((10 ^ length : Nat) : Real) ^ delta) := by
  rw [sectionSixSourceBandSelectedSignedContribution_V_eq_stateSum]
  exact (sectionSixSourceBandTerminalVFullSignedCandidateSum_eq_stateSum
    digit region hepsilon hepsilonSmall hlength hdeltaGap band
      (((10 ^ length : Nat) : Real) ^ delta)).symm

/-- Complementary candidate filters split the exact full signed sum. -/
theorem sectionSixSourceBandTerminalVFullSignedCandidateSum_eq_near_add_outside
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) (nearSet : Finset Nat) :
    sectionSixSourceBandTerminalVFullSignedCandidateSum digit region hepsilon
        hepsilonSmall hlength hdeltaGap band y =
      sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGap band y nearSet +
        sectionSixSourceBandTerminalVOutsideSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGap band y nearSet := by
  classical
  let X : Real := ((10 ^ length : Nat) : Real)
  let A := paddedRestrictedNumbers digit length
  let B := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  let candidates := sectionSixSourceBandTerminalVFullCandidates region
    hepsilon hepsilonSmall hlength hdeltaGap band B y
  let value : SectionSixTerminalVCandidate band ell -> Real := fun candidate =>
    candidate.signedWeight A B lambda
  change candidates.sum value =
    (candidates.filter fun candidate => candidate.represented ∈ nearSet).sum
        value +
      (candidates.filter fun candidate => candidate.represented ∉ nearSet).sum
        value
  exact (Finset.sum_filter_add_sum_filter_not candidates
    (fun candidate => candidate.represented ∈ nearSet) value).symm

/-- The selected recurrence contribution is exactly near plus outside. -/
theorem sectionSixSourceBandSelectedSignedContribution_V_eq_near_add_outside
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (nearSet : Finset Nat) :
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
        hepsilonSmall hlength hdeltaGap band sectionSixTerminalVPredicate =
      sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGap band
          (((10 ^ length : Nat) : Real) ^ delta) nearSet +
        sectionSixSourceBandTerminalVOutsideSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGap band
          (((10 ^ length : Nat) : Real) ^ delta) nearSet := by
  rw [sectionSixSourceBandSelectedSignedContribution_V_eq_fullSignedCandidateSum]
  exact sectionSixSourceBandTerminalVFullSignedCandidateSum_eq_near_add_outside
    digit region hepsilon hepsilonSmall hlength hdeltaGap band
      (((10 ^ length : Nat) : Real) ^ delta) nearSet

end

end PrimesRestrictedDigits
