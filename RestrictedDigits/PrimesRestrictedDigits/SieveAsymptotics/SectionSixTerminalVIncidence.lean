import PrimesRestrictedDigits.SieveAsymptotics.SectionSixNonrepeatedSignedContribution
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDivisorIncidence
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixIncidenceAggregation

/-!
# Canonical terminal `V` incidence

This module keeps the concrete represented carrier attached to the canonical source-band
terminal states. The selector is deliberately applied before any forgetful reindexing: one
represented natural can support several terminal states and several divisor moduli.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The represented carrier selected by the canonical terminal `V` predicate.
All non-`V` states receive the empty carrier. -/
noncomputable def sectionSixTerminalVRepresentedCarrier
    (C : Finset Nat) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Finset Nat :=
  if sectionSixTerminalVPredicate state then
    sectionSixTerminalRepresentedCarrier C y state
  else ∅

@[simp] theorem mem_sectionSixTerminalVRepresentedCarrier
    {C : Finset Nat} {y : Real}
    {band : SectionSixStateBand} {ell n : Nat}
    {state : SectionSixAnyState band ell} :
    n ∈ sectionSixTerminalVRepresentedCarrier C y state ↔
      sectionSixTerminalVPredicate state = true ∧
        n ∈ sectionSixTerminalRepresentedCarrier C y state := by
  by_cases hV : sectionSixTerminalVPredicate state = true
  · simp [sectionSixTerminalVRepresentedCarrier, hV]
  · have hfalse : sectionSixTerminalVPredicate state = false :=
      Bool.eq_false_of_not_eq_true hV
    simp [sectionSixTerminalVRepresentedCarrier, hfalse]

/-- Canonical `V` members retain the source carrier, positivity, complete
modulus divisibility, and source-scale weak roughness. -/
theorem sectionSixSourceBandTerminalVRepresentedCarrier_mem_data
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    {C : Finset Nat} {n : Nat}
    (hy : 5 ≤ ((10 ^ length : Nat) : Real) ^ delta)
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band)
    (hn : n ∈ sectionSixTerminalVRepresentedCarrier C
      (((10 ^ length : Nat) : Real) ^ delta) state) :
    n ∈ C ∧ 0 < n ∧ state.1 ∣ n ∧
      weakRoughPredicate (((10 ^ length : Nat) : Real) ^ delta) n := by
  exact sectionSixSourceBandTerminalRepresentedCarrier_mem_data hy hstate
    (mem_sectionSixTerminalVRepresentedCarrier.mp hn).2

/-- The selected represented carrier is contained in the common source
carrier. -/
theorem sectionSixSourceBandTerminalVRepresentedCarrier_subset
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
    sectionSixTerminalVRepresentedCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state ⊆ C := by
  intro n hn
  exact (sectionSixSourceBandTerminalVRepresentedCarrier_mem_data hy hstate hn).1

/-- Removing an arbitrary near finite set preserves the common-carrier
inclusion. -/
theorem sectionSixSourceBandTerminalVRepresentedCarrier_sub_near_subset
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    {C near : Finset Nat}
    (hy : 5 ≤ ((10 ^ length : Nat) : Real) ^ delta)
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    (sectionSixTerminalVRepresentedCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state \ near) ⊆ C \ near := by
  intro n hn
  rcases Finset.mem_sdiff.mp hn with ⟨hnV, hnNear⟩
  exact Finset.mem_sdiff.mpr ⟨
    sectionSixSourceBandTerminalVRepresentedCarrier_subset hy hstate hnV,
    hnNear⟩

/--
At one represented natural, canonical `V` states have the exact variable-modulus incidence
coefficient.
-/
theorem card_sectionSixSourceBandTerminalVRepresentedCarrier_fiber_le
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
        n ∈ sectionSixTerminalVRepresentedCarrier C
          (((10 ^ length : Nat) : Real) ^ delta) state)).card ≤
      (5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta) := by
  classical
  let states := sectionSixSourceBandTerminalStates region hepsilon
    hepsilonSmall hlength hdeltaGap band
  let stateSet := sectionSixSourceBandTerminalStateFinset region hepsilon
    hepsilonSmall hlength hdeltaGap band
  let selected := stateSet.filter fun state =>
    n ∈ sectionSixTerminalVRepresentedCarrier C
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
      (mem_sectionSixTerminalVRepresentedCarrier.mp hstateData.2).2
    have hnData := sectionSixSourceBandTerminalRepresentedCarrier_mem_data
      hy hstate hcarrier
    have hnXlt : (n : Real) < ((10 ^ length : Nat) : Real) :=
      mem_maynardAmbientCarrier.mp (hC hnData.1)
    have hbound :=
      length_sectionSixSourceBandTerminalStates_divisorFiber_le
        region hepsilon hepsilonSmall hlength hdelta hdeltaGap band n
        hnData.2.1.ne' hnXlt.le hnData.2.2.2
        sectionSixTerminalVPredicate
    have hsubset : selected ⊆
        (states.filter fun source =>
          sectionSixTerminalVPredicate source &&
            decide (source.1 ∣ n)).toFinset := by
      intro source hsource
      have hsourceData := Finset.mem_filter.mp hsource
      have hsourceList : source ∈ states :=
        List.mem_toFinset.mp hsourceData.1
      have hrepresented :=
        mem_sectionSixTerminalVRepresentedCarrier.mp hsourceData.2
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
            sectionSixTerminalVPredicate source &&
              decide (source.1 ∣ n)).toFinset).card :=
        Finset.card_le_card hsubset
      _ ≤ (states.filter fun source =>
            sectionSixTerminalVPredicate source &&
              decide (source.1 ∣ n)).length :=
        List.toFinset_card_le _
      _ ≤ (5 * (Nat.ceil (1 / delta)) ^ ell) *
          2 ^ Nat.ceil (1 / delta) := by
        simpa only [states] using hbound

/-- Removing any finite near carrier gives the natural-cardinality tail
aggregate, with the same fixed canonical coefficient. -/
theorem sum_card_sectionSixSourceBandTerminalVRepresentedCarrier_sub_near_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C near : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 ≤ ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      (sectionSixTerminalVRepresentedCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state \ near).card) ≤
      ((5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta)) * (C \ near).card := by
  classical
  apply sum_card_le_of_element_fiber_card
  · intro state hstate
    exact sectionSixSourceBandTerminalVRepresentedCarrier_sub_near_subset hy
      (mem_sectionSixSourceBandTerminalStateFinset.mp hstate)
  · intro n hn
    have hfilter :
        (sectionSixSourceBandTerminalStateFinset region hepsilon hepsilonSmall
          hlength hdeltaGap band).filter (fun state =>
            n ∈ sectionSixTerminalVRepresentedCarrier C
              (((10 ^ length : Nat) : Real) ^ delta) state \ near) ⊆
        (sectionSixSourceBandTerminalStateFinset region hepsilon hepsilonSmall
          hlength hdeltaGap band).filter (fun state =>
            n ∈ sectionSixTerminalVRepresentedCarrier C
              (((10 ^ length : Nat) : Real) ^ delta) state) := by
      intro state hstate
      have hdata := Finset.mem_filter.mp hstate
      apply Finset.mem_filter.mpr
      exact ⟨hdata.1, (Finset.mem_sdiff.mp hdata.2).1⟩
    exact (Finset.card_le_card hfilter).trans
      (card_sectionSixSourceBandTerminalVRepresentedCarrier_fiber_le
        region hepsilon hepsilonSmall hlength hdelta hdeltaGap band C hC hy n)

/-- Removing any finite near carrier gives the real-cardinality tail
aggregate, with the same fixed canonical coefficient. -/
theorem sum_card_sectionSixSourceBandTerminalVRepresentedCarrier_sub_near_real_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C near : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 ≤ ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      ((sectionSixTerminalVRepresentedCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state \ near).card : Real)) ≤
      (((5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
        ((C \ near).card : Real) := by
  classical
  apply sum_card_le_of_element_fiber_card_real
  · intro state hstate
    exact sectionSixSourceBandTerminalVRepresentedCarrier_sub_near_subset hy
      (mem_sectionSixSourceBandTerminalStateFinset.mp hstate)
  · intro n hn
    have hfilter :
        (sectionSixSourceBandTerminalStateFinset region hepsilon hepsilonSmall
          hlength hdeltaGap band).filter (fun state =>
            n ∈ sectionSixTerminalVRepresentedCarrier C
              (((10 ^ length : Nat) : Real) ^ delta) state \ near) ⊆
        (sectionSixSourceBandTerminalStateFinset region hepsilon hepsilonSmall
          hlength hdeltaGap band).filter (fun state =>
            n ∈ sectionSixTerminalVRepresentedCarrier C
              (((10 ^ length : Nat) : Real) ^ delta) state) := by
      intro state hstate
      have hdata := Finset.mem_filter.mp hstate
      apply Finset.mem_filter.mpr
      exact ⟨hdata.1, (Finset.mem_sdiff.mp hdata.2).1⟩
    exact (Finset.card_le_card hfilter).trans
      (card_sectionSixSourceBandTerminalVRepresentedCarrier_fiber_le
        region hepsilon hepsilonSmall hlength hdelta hdeltaGap band C hC hy n)

end

end PrimesRestrictedDigits
