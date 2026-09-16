import PrimesRestrictedDigits.SieveAsymptotics.SectionSixNonrepeatedSignedContribution
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedStateMultiplicity
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLemma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fundamental-Lemma bound for Section 6 `T` terminals

Canonical `T` terminal moduli from either source band lie in the strict rough carrier of the
corrected Fundamental Lemma. Fixed-modulus state multiplicity then gives the exact finite
aggregate used downstream.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixSourceBandTerminalStates_exists_source_term
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    ∃ source : {p // p ∈ sectionSixSourceBandPrimeTuples
        epsilon ell region length band},
      state ∈ sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall
          hlength hdeltaGap band source ∧
        ∃ term : SectionSixLowTerminalOccurrence
            (sectionSixSourceBandRootOfMember hepsilon hepsilonSmall hlength
              hdeltaGap band source),
          term ∈ sectionSixSourceMemberTerminalOccurrences hepsilon
            hepsilonSmall hlength hdeltaGap band source ∧ term.state = state := by
  unfold sectionSixSourceBandTerminalStates at hstate
  rcases List.mem_flatMap.mp hstate with ⟨source, hsource, hstate⟩
  refine ⟨source, hstate, ?_⟩
  rw [← sectionSixSourceMemberTerminalOccurrences_map_state hepsilon
    hepsilonSmall hlength hdeltaGap band source] at hstate
  rcases List.mem_map.mp hstate with ⟨term, hterm, htermState⟩
  exact ⟨term, hterm, htermState⟩

private theorem sectionSixRecurrenceState_modulus_strictRough
    {band : SectionSixStateBand} {ell n : Nat} {y : Real}
    (state : SectionSixRecurrenceState band ell n)
    (houter : ∀ i, y < (state.outer i : Real))
    (hinner : ∀ q, q ∈ state.inner → y < (q : Real)) :
    strictRoughPredicate y n := by
  intro p hp hpn
  rw [← state.product_eq] at hpn
  rcases hp.dvd_mul.mp hpn with hpOuter | hpInner
  · rw [primeTupleProduct] at hpOuter
    rcases (Prime.dvd_finsetProd_iff hp.prime state.outer).mp hpOuter with
      ⟨i, hi, hpi⟩
    have hpEq : p = state.outer i :=
      (Nat.prime_dvd_prime_iff_eq hp (state.outerPrime i)).mp hpi
    simpa only [hpEq] using houter i
  · rcases (Prime.dvd_prod_iff hp.prime).mp hpInner with ⟨q, hq, hpq⟩
    have hpEq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp (state.innerPrime q hq)).mp hpq
    simpa only [hpEq] using hinner q hq

private theorem sectionSixTerminalTStateValue_eq_siftedSum
    (digit : Fin 10) (length : Nat) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell)
    (hT : sectionSixTerminalTPredicate state = true) :
    sectionSixTerminalStateValue digit length y state =
      sectionSixSiftedSum digit length state.1.toPNat' y := by
  have hkind : state.2.kind = .T := by
    simpa [sectionSixTerminalTPredicate] using hT
  rw [sectionSixTerminalStateValue, hkind]
  unfold sectionSixStateStrictTerm
  apply congrArg (fun d : PNat => sectionSixSiftedSum digit length d y)
  apply PNat.eq
  rw [sectionSixStateModulusPNat_coe, Nat.toPNat'_coe,
    if_pos (sectionSixRecurrenceState_modulus_pos state.2)]

/-- A canonical `T` state from either source band has a complete modulus in
the exact strict rough carrier used by the corrected Fundamental Lemma. -/
theorem sectionSixSourceBandTState_mem_fundamentalCarrier
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
      hepsilonSmall hlength hdeltaGap band)
    (hT : sectionSixTerminalTPredicate state = true) :
    state.1 ∈ maynardStrictRoughCarrier
      (((10 ^ length : Nat) : Real) ^ (50 / 77 - epsilon))
      (((10 ^ length : Nat) : Real) ^ delta) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hstateList :=
    (mem_sectionSixSourceBandTerminalStateFinset.mp hstate)
  rcases sectionSixSourceBandTerminalStates_exists_source_term hstateList with
    ⟨source, hsourceState, term, hterm, htermState⟩
  have hkind : state.2.kind = .T := by
    simpa [sectionSixTerminalTPredicate] using hT
  have hsourceData := (mem_sectionSixSourceBandPrimeTuples.mp source.property).1
  have hp : IsPropositionSixOnePrimeTuple epsilon length region source.1 :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).mp hsourceData
  have houterEq : state.2.outer = source.1 :=
    sectionSixSourceMemberTerminalStates_outer hepsilon hepsilonSmall hlength
      hdeltaGap band source hsourceState
  have houter : ∀ i, X ^ delta < (state.2.outer i : Real) := by
    intro i
    rw [houterEq]
    exact (Real.rpow_lt_rpow_of_exponent_lt hX hdeltaGapStrict).trans_le
      (hp.2.2.1 i)
  have hinner : ∀ q, q ∈ state.2.inner → X ^ delta < (q : Real) := by
    intro q hq
    exact (sectionSixSourceBandTerminalStates_innerRange hstateList q hq).1
  have hrough : strictRoughPredicate (X ^ delta) state.1 :=
    sectionSixRecurrenceState_modulus_strictRough state.2 houter hinner
  have htermKind : term.state.2.kind = .T :=
    (congrArg (fun source : SectionSixAnyState band ell => source.2.kind)
      htermState).trans hkind
  have hcutoff : (state.1 : Real) ≤
      sectionSixStateBandCutoff band X (sectionSixThetaOne epsilon)
        (sectionSixThetaTwo epsilon) := by
    cases term with
    | base occurrence =>
        have hmodulus := congrArg
          (fun source : SectionSixAnyState band ell => (source.1 : Real))
          htermState
        rw [← hmodulus]
        exact occurrence.state_cutoff
    | strictHigh occurrence => simp at htermKind
    | repeatedLow occurrence => simp at htermKind
    | repeatedHigh occurrence => simp at htermKind
  have hlevel : sectionSixStateBandCutoff band X
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) <
        X ^ (50 / 77 - epsilon) := by
    cases band with
    | low =>
        apply Real.rpow_lt_rpow_of_exponent_lt hX
        simp only [sectionSixThetaOne]
        linarith
    | high =>
        apply Real.rpow_lt_rpow_of_exponent_lt hX
        exact (sectionSix_parameter_bounds hepsilon hepsilonSmall).2.2.2.2
  rw [mem_maynardStrictRoughCarrier]
  exact ⟨sectionSixRecurrenceState_modulus_pos state.2,
    hcutoff.trans_lt hlevel, hrough⟩

/-- At kind `T`, the sign-free terminal value is propositionally normalized
to the exact cardinality discrepancy appearing in the Fundamental Lemma. -/
theorem sectionSixTerminalTStateValue_eq_fundamentalResidual
    (digit : Fin 10) (length : Nat) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell)
    (hT : sectionSixTerminalTPredicate state = true) :
    sectionSixTerminalStateValue digit length y state =
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length)
          state.1.toPNat') y).card : Real) -
        (restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real) *
          ((strictSiftedCarrier
            (sieveDilation
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
                state.1.toPNat') y).card : Real) := by
  rw [sectionSixTerminalTStateValue_eq_siftedSum digit length y state hT,
    sectionSixSiftedSum_eq_card_sub_density_mul_card]
  ring

/--
Filtering the canonical one-band state Finset to kind `T` preserves the fixed-complete-modulus
multiplicity bound.
-/
theorem card_sectionSixSourceBandTState_modulusFiber_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (D : Nat) :
    (((sectionSixSourceBandTerminalStateFinset region hepsilon hepsilonSmall
      hlength hdeltaGap band).filter
        (fun state => sectionSixTerminalTPredicate state = true)).filter
        (fun state => state.1 = D)).card ≤
      5 * (Nat.ceil (1 / delta)) ^ ell := by
  classical
  let states := sectionSixSourceBandTerminalStates region hepsilon
    hepsilonSmall hlength hdeltaGap band
  have hsubset :
      (((sectionSixSourceBandTerminalStateFinset region hepsilon hepsilonSmall
        hlength hdeltaGap band).filter
          (fun state => sectionSixTerminalTPredicate state = true)).filter
          (fun state => state.1 = D)) ⊆
        (states.filter fun state => state.1 = D).toFinset := by
    intro state hstate
    have hstateData := Finset.mem_filter.mp hstate
    have hterminalData := Finset.mem_filter.mp hstateData.1
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    exact ⟨by
      exact mem_sectionSixSourceBandTerminalStateFinset.mp hterminalData.1,
      decide_eq_true hstateData.2⟩
  calc
    _ ≤ ((states.filter fun state => state.1 = D).toFinset).card :=
      Finset.card_le_card hsubset
    _ ≤ (states.filter fun state => state.1 = D).length :=
      List.toFinset_card_le _
    _ ≤ 5 * (Nat.ceil (1 / delta)) ^ ell := by
      simpa only [states] using
        length_sectionSixSourceBandTerminalStates_modulusFiber_le region
          hepsilon hepsilonSmall hlength hdelta hdeltaGap band D

/-- The unsigned canonical `T` state sum is bounded by fixed-modulus
multiplicity times the exact Fundamental-Lemma residual sum. -/
theorem sum_abs_sectionSixSourceBandTStateValue_le_fundamentalResidual
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      abs (if sectionSixTerminalTPredicate state then
        sectionSixTerminalStateValue digit length
          (((10 ^ length : Nat) : Real) ^ delta) state else 0)) ≤
      ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real) *
        ∑ D ∈ maynardStrictRoughCarrier
            (((10 ^ length : Nat) : Real) ^ (50 / 77 - epsilon))
            (((10 ^ length : Nat) : Real) ^ delta),
          abs (((strictSiftedCarrier
              (sieveDilation (paddedRestrictedNumbers digit length)
                D.toPNat')
              (((10 ^ length : Nat) : Real) ^ delta)).card : Real) -
            (restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                ((10 ^ length : Nat) : Real) *
              ((strictSiftedCarrier
                (sieveDilation
                  (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
                    D.toPNat')
                (((10 ^ length : Nat) : Real) ^ delta)).card : Real)) := by
  classical
  let stateSet := sectionSixSourceBandTerminalStateFinset region hepsilon
    hepsilonSmall hlength hdeltaGap band
  let tStates := stateSet.filter fun state =>
    sectionSixTerminalTPredicate state = true
  let carrier := maynardStrictRoughCarrier
    (((10 ^ length : Nat) : Real) ^ (50 / 77 - epsilon))
    (((10 ^ length : Nat) : Real) ^ delta)
  let value : SectionSixAnyState band ell → Real := fun state =>
    sectionSixTerminalStateValue digit length
      (((10 ^ length : Nat) : Real) ^ delta) state
  let charge : Nat → Real := fun D =>
    abs (((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) D.toPNat')
        (((10 ^ length : Nat) : Real) ^ delta)).card : Real) -
      (restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real) *
        ((strictSiftedCarrier
          (sieveDilation
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) D.toPNat')
          (((10 ^ length : Nat) : Real) ^ delta)).card : Real))
  have hbound := sum_abs_value_le_cardinality_charge_of_fiber_card
    tStates carrier (fun state => state.1) value charge
      (5 * (Nat.ceil (1 / delta)) ^ ell)
  have hmap : ∀ state, state ∈ tStates → state.1 ∈ carrier := by
    intro state hstate
    have hdata := Finset.mem_filter.mp hstate
    exact sectionSixSourceBandTState_mem_fundamentalCarrier hepsilon
      hepsilonSmall hlength hdeltaGap hdeltaGapStrict band hdata.1 hdata.2
  have hfiber : ∀ D, D ∈ carrier →
      (tStates.filter fun state => state.1 = D).card ≤
        5 * (Nat.ceil (1 / delta)) ^ ell := by
    intro D hD
    simpa only [tStates, stateSet] using
      card_sectionSixSourceBandTState_modulusFiber_le region hepsilon
        hepsilonSmall hlength hdelta hdeltaGap band D
  have hpoint : ∀ state, state ∈ tStates →
      abs (value state) ≤ charge state.1 := by
    intro state hstate
    have hT := (Finset.mem_filter.mp hstate).2
    dsimp only [value, charge]
    rw [sectionSixTerminalTStateValue_eq_fundamentalResidual digit length
      (((10 ^ length : Nat) : Real) ^ delta) state hT]
  have hcharge : ∀ D, D ∈ carrier → 0 ≤ charge D := by
    intro D hD
    exact abs_nonneg _
  have hfiltered := hbound hmap hfiber hpoint hcharge
  change (∑ state ∈ stateSet,
      abs (if sectionSixTerminalTPredicate state then value state else 0)) ≤ _
  calc
    _ = ∑ state ∈ tStates, abs (value state) := by
      dsimp only [tStates]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro state hstate
      by_cases hT : sectionSixTerminalTPredicate state = true <;> simp [hT]
    _ ≤ ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real) *
        ∑ D ∈ carrier, charge D := hfiltered
    _ = _ := by rfl

/-- The absolute signed canonical `T` contribution has the same finite
Fundamental-residual bound. -/
theorem abs_sectionSixSourceBandTSignedContribution_le_fundamentalResidual
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) :
    abs (sectionSixSourceBandSelectedSignedContribution digit region hepsilon
      hepsilonSmall hlength hdeltaGap band sectionSixTerminalTPredicate) ≤
      ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real) *
        ∑ D ∈ maynardStrictRoughCarrier
            (((10 ^ length : Nat) : Real) ^ (50 / 77 - epsilon))
            (((10 ^ length : Nat) : Real) ^ delta),
          abs (((strictSiftedCarrier
              (sieveDilation (paddedRestrictedNumbers digit length)
                D.toPNat')
              (((10 ^ length : Nat) : Real) ^ delta)).card : Real) -
            (restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                ((10 ^ length : Nat) : Real) *
              ((strictSiftedCarrier
                (sieveDilation
                  (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
                    D.toPNat')
                (((10 ^ length : Nat) : Real) ^ delta)).card : Real)) := by
  exact (abs_sectionSixSourceBandSelectedSignedContribution_le_terminalStateFinset
    digit region hepsilon hepsilonSmall hlength hdeltaGap band
      sectionSixTerminalTPredicate).trans
    (sum_abs_sectionSixSourceBandTStateValue_le_fundamentalResidual digit region
      hepsilon hepsilonSmall hlength hdelta hdeltaGap hdeltaGapStrict band)

end

end PrimesRestrictedDigits
