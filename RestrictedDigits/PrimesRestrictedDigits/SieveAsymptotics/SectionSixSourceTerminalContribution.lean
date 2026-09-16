import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalCarrier

/-!
# Signed source-band terminal contributions

Canonical terminal occurrence types depend on their source root. This file therefore converts
each member occurrence list to a real selected sum before summing those scalars across the
attached source tuples.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The canonical terminal occurrence list at one attached source's exact
dependent root. -/
noncomputable def sectionSixSourceMemberTerminalOccurrences
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band}) :
    List (SectionSixLowTerminalOccurrence
      (sectionSixSourceBandRootOfMember hepsilon hepsilonSmall hlength
        hdeltaGap band source)) :=
  let root := sectionSixSourceBandRootOfMember hepsilon hepsilonSmall
    hlength hdeltaGap band source
  let tree := sectionSixLowOccurrenceTreeOfFuel root
    (Nat.ceil (1 / delta) + 1) (sectionSixLowRootOccurrence root)
  sectionSixLowTerminalOccurrences tree

/--
Projecting the canonical occurrence list to states gives exactly existing source-member state
list.
-/
theorem sectionSixSourceMemberTerminalOccurrences_map_state
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band}) :
    (sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall hlength
      hdeltaGap band source).map SectionSixLowTerminalOccurrence.state =
      sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall hlength
        hdeltaGap band source := by
  rfl

private noncomputable def sectionSixSourceMemberSelectedSignedContribution
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band})
    (predicate : SectionSixAnyState band ell → Bool) : Real :=
  ((sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall hlength
    hdeltaGap band source).map fun term =>
      if predicate term.state then term.signedValue digit length else 0).sum

/-- The selected signed terminal contribution of one source band. Each
dependent member list is scalarized before the outer attached-source sum. -/
noncomputable def sectionSixSourceBandSelectedSignedContribution
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (predicate : SectionSixAnyState band ell → Bool) : Real :=
  (((sectionSixSourceBandPrimeTuples epsilon ell region length band).attach.toList).map
    fun source => sectionSixSourceMemberSelectedSignedContribution digit hepsilon
      hepsilonSmall hlength hdeltaGap band source predicate).sum

private theorem sectionSixSourceMemberSelectedSignedContribution_true_eq
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band}) :
    sectionSixSourceMemberSelectedSignedContribution digit hepsilon
        hepsilonSmall hlength hdeltaGap band source (fun _ => true) =
      sectionSixSiftedSum digit length (primeTupleProduct source.1).toPNat'
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) := by
  have hsource := (mem_propositionSixOnePrimeTuples_iff_source
    hepsilon hlength).mp (mem_sectionSixSourceBandPrimeTuples.mp source.property).1
  have hband := (mem_sectionSixSourceBandPrimeTuples.mp source.property).2
  have h := sectionSixSourceBandRoot_terminalOccurrences_sum_eq_sourceTerm
    hlength band source.1 hsource delta hdelta hdeltaGap hband
      (sectionSixSourceBandCutoff_le_decimalScale
        hepsilon hepsilonSmall hlength band) digit
  simpa [sectionSixSourceMemberSelectedSignedContribution,
    sectionSixSourceMemberTerminalOccurrences,
    sectionSixSourceBandRootOfMember] using h

/-- Selecting every canonical terminal recovers the literal plain Finset sum
of source terms in the band. Positivity of `delta` is used only to discharge
the residual-free fuel certificate. -/
theorem sectionSixSourceBandSelectedSignedContribution_true_eq_sourceTerms
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) :
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
        hepsilonSmall hlength hdeltaGap band (fun _ => true) =
      ∑ p ∈ sectionSixSourceBandPrimeTuples epsilon ell region length band,
        sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
          (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) := by
  unfold sectionSixSourceBandSelectedSignedContribution
  calc
    _ = (((sectionSixSourceBandPrimeTuples epsilon ell region length band).attach.toList).map
        fun source => sectionSixSiftedSum digit length
          (primeTupleProduct source.1).toPNat'
          (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro source hsource
      exact sectionSixSourceMemberSelectedSignedContribution_true_eq digit
        hepsilon hepsilonSmall hlength hdelta hdeltaGap band source
    _ = ∑ source ∈
        (sectionSixSourceBandPrimeTuples epsilon ell region length band).attach,
        sectionSixSiftedSum digit length (primeTupleProduct source.1).toPNat'
          (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) := by
      rw [Finset.sum_map_toList]
    _ = _ := by
      exact Finset.sum_attach
        (sectionSixSourceBandPrimeTuples epsilon ell region length band)
        (fun p => sectionSixSiftedSum digit length
          (primeTupleProduct p).toPNat'
          (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon))

private theorem sectionSixSourceMemberSelectedSignedContribution_partition
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
    sectionSixSourceMemberSelectedSignedContribution digit hepsilon
        hepsilonSmall hlength hdeltaGap band source (fun _ => true) =
      sectionSixSourceMemberSelectedSignedContribution digit hepsilon
          hepsilonSmall hlength hdeltaGap band source predicate +
        sectionSixSourceMemberSelectedSignedContribution digit hepsilon
          hepsilonSmall hlength hdeltaGap band source
            (fun state => !predicate state) := by
  unfold sectionSixSourceMemberSelectedSignedContribution
  let terms := sectionSixSourceMemberTerminalOccurrences hepsilon hepsilonSmall
    hlength hdeltaGap band source
  change ((terms.map fun term =>
      if (fun _ => true) term.state then term.signedValue digit length else 0).sum) = _
  calc
    _ = (terms.map fun term =>
        (if predicate term.state then term.signedValue digit length else 0) +
          (if !predicate term.state then term.signedValue digit length else 0)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro term hterm
      cases hpredicate : predicate term.state <;> simp
    _ = _ := by rw [List.sum_map_add]

/-- The complete signed contribution is exactly the repeated contribution
plus the contribution selected by the syntactic Boolean complement. -/
theorem sectionSixSourceBandSelectedSignedContribution_repeated_partition
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) :
    sectionSixSourceBandSelectedSignedContribution digit region hepsilon
        hepsilonSmall hlength hdeltaGap band (fun _ => true) =
      sectionSixSourceBandSelectedSignedContribution digit region hepsilon
          hepsilonSmall hlength hdeltaGap band sectionSixRepeatedTerminalPredicate +
        sectionSixSourceBandSelectedSignedContribution digit region hepsilon
          hepsilonSmall hlength hdeltaGap band
            (fun state => !sectionSixRepeatedTerminalPredicate state) := by
  unfold sectionSixSourceBandSelectedSignedContribution
  let sources :=
    (sectionSixSourceBandPrimeTuples epsilon ell region length band).attach.toList
  change (sources.map fun source =>
      sectionSixSourceMemberSelectedSignedContribution digit hepsilon
        hepsilonSmall hlength hdeltaGap band source (fun _ => true)).sum = _
  calc
    _ = (sources.map fun source =>
        sectionSixSourceMemberSelectedSignedContribution digit hepsilon
            hepsilonSmall hlength hdeltaGap band source
              sectionSixRepeatedTerminalPredicate +
          sectionSixSourceMemberSelectedSignedContribution digit hepsilon
            hepsilonSmall hlength hdeltaGap band source
              (fun state => !sectionSixRepeatedTerminalPredicate state)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro source hsource
      exact sectionSixSourceMemberSelectedSignedContribution_partition digit
        hepsilon hepsilonSmall hlength hdeltaGap band source
          sectionSixRepeatedTerminalPredicate
    _ = _ := by rw [List.sum_map_add]

end

end PrimesRestrictedDigits
