import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDivisorIncidence
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalCarrier
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixIncidenceAggregation

/-!
# Repeated-terminal element incidence

Exact `RU/RV` represented carriers lie in one positive large-prime-square ambient. The
variable-modulus divisor bound supplies per-integer fiber.
-/

namespace PrimesRestrictedDigits

noncomputable section

open scoped BigOperators

/-- The positive members of `C` divisible by a prime square from the Section 6
terminal interval. -/
noncomputable def sectionSixRepeatedSquarefulCarrier
    (C : Finset Nat) (X delta theta : Real) : Finset Nat := by
  classical
  exact C.filter fun n => 0 < n ∧
    ∃ q ∈ sievePrimeInterval (X ^ delta) (X ^ theta), q * q ∣ n

@[simp] theorem mem_sectionSixRepeatedSquarefulCarrier
    {C : Finset Nat} {X delta theta : Real} {n : Nat} :
    n ∈ sectionSixRepeatedSquarefulCarrier C X delta theta ↔
      n ∈ C ∧ 0 < n ∧
        ∃ q ∈ sievePrimeInterval (X ^ delta) (X ^ theta), q * q ∣ n := by
  simp [sectionSixRepeatedSquarefulCarrier]

/-- The represented carrier of a repeated terminal; all other state kinds are
assigned the empty carrier. -/
noncomputable def sectionSixRepeatedRepresentedCarrier
    (C : Finset Nat) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Finset Nat :=
  if sectionSixRepeatedTerminalPredicate state then
    sectionSixTerminalRepresentedCarrier C y state
  else ∅

@[simp] theorem mem_sectionSixRepeatedRepresentedCarrier
    {C : Finset Nat} {y : Real}
    {band : SectionSixStateBand} {ell n : Nat}
    {state : SectionSixAnyState band ell} :
    n ∈ sectionSixRepeatedRepresentedCarrier C y state ↔
      sectionSixRepeatedTerminalPredicate state = true ∧
        n ∈ sectionSixTerminalRepresentedCarrier C y state := by
  by_cases hrepeated : sectionSixRepeatedTerminalPredicate state = true
  · simp [sectionSixRepeatedRepresentedCarrier, hrepeated]
  · have hfalse : sectionSixRepeatedTerminalPredicate state = false :=
      Bool.eq_false_of_not_eq_true hrepeated
    simp [sectionSixRepeatedRepresentedCarrier, hfalse]

/-- Finset form duplicate-free source-band state list. -/
noncomputable def sectionSixSourceBandTerminalStateFinset
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) : Finset (SectionSixAnyState band ell) := by
  classical
  exact (sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
    hlength hdeltaGap band).toFinset

@[simp] theorem mem_sectionSixSourceBandTerminalStateFinset
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell} :
    state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band ↔
      state ∈ sectionSixSourceBandTerminalStates region hepsilon
        hepsilonSmall hlength hdeltaGap band := by
  classical
  simp [sectionSixSourceBandTerminalStateFinset]

/--
Every exact repeated carrier lies in the common positive squareful ambient. Canonical
source-list membership supplies the repeated-square coherence absent from a bare record.
-/
theorem sectionSixRepeatedRepresentedCarrier_subset_squareful
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    {C : Finset Nat}
    (hy : 5 ≤ ((10 ^ length : Nat) : Real) ^ delta)
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    sectionSixRepeatedRepresentedCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state ⊆
      sectionSixRepeatedSquarefulCarrier C
        ((10 ^ length : Nat) : Real) delta (sectionSixThetaGap epsilon) := by
  intro n hn
  have hnData := mem_sectionSixRepeatedRepresentedCarrier.mp hn
  have hrepeated :=
    (sectionSixRepeatedTerminalPredicate_eq_true state).mp hnData.1
  have hcarrier :=
    sectionSixSourceBandTerminalRepresentedCarrier_mem_data
      hy hstate hnData.2
  have hsquare :=
    sectionSixSourceBandTerminalRepresentedCarrier_repeatedSquare
      hy hstate hrepeated hnData.2
  exact mem_sectionSixRepeatedSquarefulCarrier.mpr
    ⟨hcarrier.1, hcarrier.2.1, hsquare⟩

/--
At one represented integer, the exact repeated carriers from one source band have the
variable-modulus incidence bound.
-/
theorem card_sectionSixSourceBandRepeatedRepresentedCarrier_fiber_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 ≤ ((10 ^ length : Nat) : Real) ^ delta)
    (n : Nat) :
    ((sectionSixSourceBandTerminalStateFinset region hepsilon hepsilonSmall
      hlength hdeltaGap band).filter (fun state =>
        n ∈ sectionSixRepeatedRepresentedCarrier C
          (((10 ^ length : Nat) : Real) ^ delta) state)).card ≤
      (5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta) := by
  classical
  let states := sectionSixSourceBandTerminalStates region hepsilon
    hepsilonSmall hlength hdeltaGap band
  let stateSet := sectionSixSourceBandTerminalStateFinset region hepsilon
    hepsilonSmall hlength hdeltaGap band
  let selected := stateSet.filter fun state =>
    n ∈ sectionSixRepeatedRepresentedCarrier C
      (((10 ^ length : Nat) : Real) ^ delta) state
  change selected.card ≤ _
  by_cases hselected : selected = ∅
  · simp [hselected]
  · obtain ⟨state, hstateSelected⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hselected
    have hstateData := Finset.mem_filter.mp hstateSelected
    have hstate : state ∈ states := by
      apply mem_sectionSixSourceBandTerminalStateFinset.mp
      simpa only [stateSet] using hstateData.1
    have hcarrier :=
      (mem_sectionSixRepeatedRepresentedCarrier.mp hstateData.2).2
    have hnData :=
      sectionSixSourceBandTerminalRepresentedCarrier_mem_data
        hy hstate hcarrier
    have hnXlt : (n : Real) < ((10 ^ length : Nat) : Real) :=
      mem_maynardAmbientCarrier.mp (hC hnData.1)
    have hbound :=
      length_sectionSixSourceBandTerminalStates_divisorFiber_le
        region hepsilon hepsilonSmall hlength hdelta hdeltaGap band n
        hnData.2.1.ne' hnXlt.le hnData.2.2.2
        sectionSixRepeatedTerminalPredicate
    have hsubset : selected ⊆
        (states.filter fun source =>
          sectionSixRepeatedTerminalPredicate source &&
            decide (source.1 ∣ n)).toFinset := by
      intro source hsource
      have hsourceData := Finset.mem_filter.mp hsource
      have hsourceList : source ∈ states :=
        List.mem_toFinset.mp hsourceData.1
      have hrepresented :=
        mem_sectionSixRepeatedRepresentedCarrier.mp hsourceData.2
      have hsourceCarrier :=
        sectionSixSourceBandTerminalRepresentedCarrier_mem_data
          hy hsourceList hrepresented.2
      apply List.mem_toFinset.mpr
      exact List.mem_filter.mpr
        ⟨hsourceList, Bool.and_eq_true_iff.mpr
          ⟨hrepresented.1, decide_eq_true hsourceCarrier.2.2.1⟩⟩
    calc
      selected.card ≤
          ((states.filter fun source =>
            sectionSixRepeatedTerminalPredicate source &&
              decide (source.1 ∣ n)).toFinset).card :=
        Finset.card_le_card hsubset
      _ ≤ (states.filter fun source =>
            sectionSixRepeatedTerminalPredicate source &&
              decide (source.1 ∣ n)).length :=
        List.toFinset_card_le _
      _ ≤ (5 * (Nat.ceil (1 / delta)) ^ ell) *
          2 ^ Nat.ceil (1 / delta) := by
        simpa only [states] using hbound

/-- Cardinality bound for the repeated terminal carriers in one source band. -/
theorem sum_card_sectionSixSourceBandRepeatedRepresentedCarrier_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 ≤ ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      (sectionSixRepeatedRepresentedCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state).card) ≤
      ((5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta)) *
        (sectionSixRepeatedSquarefulCarrier C
          ((10 ^ length : Nat) : Real) delta
          (sectionSixThetaGap epsilon)).card := by
  classical
  apply sum_card_le_of_element_fiber_card
  · intro state hstate
    exact sectionSixRepeatedRepresentedCarrier_subset_squareful hy
      (mem_sectionSixSourceBandTerminalStateFinset.mp hstate)
  · intro n hn
    exact card_sectionSixSourceBandRepeatedRepresentedCarrier_fiber_le
      region hepsilon hepsilonSmall hlength hdelta hdeltaGap band C hC hy n

/-- Real-cardinality form of the preceding aggregate. -/
theorem sum_card_sectionSixSourceBandRepeatedRepresentedCarrier_real_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 ≤ ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      ((sectionSixRepeatedRepresentedCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state).card : Real)) ≤
      (((5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
        ((sectionSixRepeatedSquarefulCarrier C
          ((10 ^ length : Nat) : Real) delta
          (sectionSixThetaGap epsilon)).card : Real) := by
  classical
  apply sum_card_le_of_element_fiber_card_real
  · intro state hstate
    exact sectionSixRepeatedRepresentedCarrier_subset_squareful hy
      (mem_sectionSixSourceBandTerminalStateFinset.mp hstate)
  · intro n hn
    exact card_sectionSixSourceBandRepeatedRepresentedCarrier_fiber_le
      region hepsilon hepsilonSmall hlength hdelta hdeltaGap band C hC hy n

end

end PrimesRestrictedDigits
