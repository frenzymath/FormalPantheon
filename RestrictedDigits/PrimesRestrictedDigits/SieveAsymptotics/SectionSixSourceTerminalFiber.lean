import PrimesRestrictedDigits.SieveAsymptotics.SectionSixSourceTerminalStates
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFactorLengthBound

/-!
# Fixed-modulus source terminal fibers

Sigma states whose complete modulus equals `D` are transported to the state type indexed by
`D`. Duplicate-freedom preserves the exact list cardinality before is applied.
-/

namespace PrimesRestrictedDigits

noncomputable section

abbrev SectionSixAnyStateAtModulus
    (band : SectionSixStateBand) (ell D : Nat) :=
  {state : SectionSixAnyState band ell // state.1 = D}

def SectionSixAnyStateAtModulus.state
    {band : SectionSixStateBand} {ell D : Nat}
    (source : SectionSixAnyStateAtModulus band ell D) :
    SectionSixRecurrenceState band ell D := by
  rcases source with ⟨⟨n, state⟩, hn⟩
  dsimp only at hn
  subst n
  exact state

theorem SectionSixAnyStateAtModulus.state_injective
    {band : SectionSixStateBand} {ell D : Nat} :
    Function.Injective
      (SectionSixAnyStateAtModulus.state
        (band := band) (ell := ell) (D := D)) := by
  intro sourceOne sourceTwo hstate
  rcases sourceOne with ⟨⟨nOne, stateOne⟩, hnOne⟩
  rcases sourceTwo with ⟨⟨nTwo, stateTwo⟩, hnTwo⟩
  dsimp only at hnOne hnTwo
  subst nOne
  subst nTwo
  change stateOne = stateTwo at hstate
  subst stateTwo
  rfl

@[simp] theorem SectionSixAnyStateAtModulus.state_outer
    {band : SectionSixStateBand} {ell D : Nat}
    (source : SectionSixAnyStateAtModulus band ell D) :
    source.state.outer = source.1.2.outer := by
  rcases source with ⟨⟨n, state⟩, hn⟩
  dsimp only at hn
  subst n
  rfl

@[simp] theorem SectionSixAnyStateAtModulus.state_inner
    {band : SectionSixStateBand} {ell D : Nat}
    (source : SectionSixAnyStateAtModulus band ell D) :
    source.state.inner = source.1.2.inner := by
  rcases source with ⟨⟨n, state⟩, hn⟩
  dsimp only at hn
  subst n
  rfl

noncomputable def sectionSixAnyStateModulusFiber
    {band : SectionSixStateBand} {ell : Nat}
    (states : List (SectionSixAnyState band ell)) (D : Nat) :
    List (SectionSixAnyStateAtModulus band ell D) := by
  classical
  exact ((states.filter fun state => state.1 = D).attach.map fun source =>
    ⟨source.1, by
      have hmem := source.property
      simp only [List.mem_filter] at hmem
      exact of_decide_eq_true hmem.2⟩)

@[simp] theorem sectionSixAnyStateModulusFiber_length
    {band : SectionSixStateBand} {ell : Nat}
    (states : List (SectionSixAnyState band ell)) (D : Nat) :
    (sectionSixAnyStateModulusFiber states D).length =
      (states.filter fun state => state.1 = D).length := by
  simp [sectionSixAnyStateModulusFiber]

@[simp] theorem mem_sectionSixAnyStateModulusFiber
    {band : SectionSixStateBand} {ell : Nat}
    {states : List (SectionSixAnyState band ell)} {D : Nat}
    {source : SectionSixAnyStateAtModulus band ell D} :
    source ∈ sectionSixAnyStateModulusFiber states D ↔ source.1 ∈ states := by
  classical
  constructor
  · intro hsource
    unfold sectionSixAnyStateModulusFiber at hsource
    rcases List.mem_map.mp hsource with ⟨item, hitem, hvalue⟩
    have hfiltered := item.property
    simp only [List.mem_filter] at hfiltered
    have hval : item.1 = source.1 := congrArg Subtype.val hvalue
    simpa [← hval] using hfiltered.1
  · intro hsource
    unfold sectionSixAnyStateModulusFiber
    apply List.mem_map.mpr
    let item : {state // state ∈ states.filter fun state => state.1 = D} :=
      ⟨source.1, by
        simp only [List.mem_filter]
        exact ⟨hsource, decide_eq_true source.property⟩⟩
    refine ⟨item, by simp [item], ?_⟩
    apply Subtype.ext
    rfl

theorem sectionSixAnyStateModulusFiber_nodup
    {band : SectionSixStateBand} {ell : Nat}
    {states : List (SectionSixAnyState band ell)} (D : Nat)
    (hstates : states.Nodup) :
    (sectionSixAnyStateModulusFiber states D).Nodup := by
  classical
  unfold sectionSixAnyStateModulusFiber
  apply (hstates.filter _).attach.map
  intro sourceOne sourceTwo hsource
  apply Subtype.ext
  exact congrArg
    (fun source : SectionSixAnyStateAtModulus band ell D => source.1)
    hsource

noncomputable def sectionSixFixedModulusStates
    {band : SectionSixStateBand} {ell : Nat}
    (states : List (SectionSixAnyState band ell)) (D : Nat) :
    Finset (SectionSixRecurrenceState band ell D) := by
  classical
  exact ((sectionSixAnyStateModulusFiber states D).map
    SectionSixAnyStateAtModulus.state).toFinset

theorem card_sectionSixFixedModulusStates_eq
    {band : SectionSixStateBand} {ell : Nat}
    {states : List (SectionSixAnyState band ell)} {D : Nat}
    (hstates : states.Nodup) :
    (sectionSixFixedModulusStates states D).card =
      (states.filter fun state => state.1 = D).length := by
  classical
  rw [sectionSixFixedModulusStates, List.toFinset_card_of_nodup]
  · simp
  · exact (sectionSixAnyStateModulusFiber_nodup D hstates).map
      SectionSixAnyStateAtModulus.state_injective

theorem mem_sectionSixFixedModulusStates
    {band : SectionSixStateBand} {ell : Nat}
    {states : List (SectionSixAnyState band ell)} {D : Nat}
    {state : SectionSixRecurrenceState band ell D}
    (hstate : state ∈ sectionSixFixedModulusStates states D) :
    ∃ source : SectionSixAnyStateAtModulus band ell D,
      source.1 ∈ states ∧ source.state = state := by
  classical
  unfold sectionSixFixedModulusStates at hstate
  rw [List.mem_toFinset] at hstate
  rcases List.mem_map.mp hstate with ⟨source, hsource, rfl⟩
  exact ⟨source, (mem_sectionSixAnyStateModulusFiber.mp hsource), rfl⟩

theorem length_sectionSixAnyState_modulusFiber_le
    {band : SectionSixStateBand} {ell : Nat}
    {X delta theta : Real}
    (hX : 1 < X) (hdelta : 0 < delta)
    (states : List (SectionSixAnyState band ell))
    (hstates : states.Nodup)
    (hmodulus : ∀ state ∈ states, (state.1 : Real) ≤ X)
    (houter : ∀ state ∈ states, ∀ i,
      X ^ delta ≤ (state.2.outer i : Real))
    (hinner : ∀ state ∈ states,
      sectionSixStateInnerRange X delta theta state.2.inner)
    (D : Nat) :
    (states.filter fun state => state.1 = D).length ≤
      5 * (Nat.ceil (1 / delta)) ^ ell := by
  classical
  let fiber := states.filter fun state => state.1 = D
  by_cases hfiber : fiber = []
  · simp [fiber, hfiber]
  · obtain ⟨sourceState, hsourceState⟩ :=
      List.exists_mem_of_ne_nil fiber hfiber
    have hsourceMem : sourceState ∈ states :=
      (List.mem_filter.mp hsourceState).1
    have hsourceEq : sourceState.1 = D :=
      of_decide_eq_true (List.mem_filter.mp hsourceState).2
    have hDX : (D : Real) ≤ X := by
      simpa only [hsourceEq] using hmodulus sourceState hsourceMem
    let fixedStates : Finset (SectionSixRecurrenceState band ell D) :=
      sectionSixFixedModulusStates states D
    have hfixedOuter : ∀ state ∈ fixedStates, ∀ i,
        X ^ delta ≤ (state.outer i : Real) := by
      intro state hstate i
      rcases mem_sectionSixFixedModulusStates hstate with
        ⟨source, hsource, rfl⟩
      simpa only [SectionSixAnyStateAtModulus.state_outer] using
        houter source.1 hsource i
    have hfixedInner : ∀ state ∈ fixedStates,
        sectionSixStateInnerRange X delta theta state.inner := by
      intro state hstate
      rcases mem_sectionSixFixedModulusStates hstate with
        ⟨source, hsource, rfl⟩
      simpa only [SectionSixAnyStateAtModulus.state_inner] using
        hinner source.1 hsource
    have hcard := card_sectionSixRecurrenceState_le_five_ceil_inv_delta_pow
      hX hdelta hDX fixedStates hfixedOuter hfixedInner
    rw [show fixedStates.card = fiber.length by
      exact card_sectionSixFixedModulusStates_eq hstates] at hcard
    exact hcard

theorem length_sectionSixSourceBandTerminalStates_modulusFiber_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (D : Nat) :
    ((sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
      hlength hdeltaGap band).filter fun state => state.1 = D).length ≤
        5 * (Nat.ceil (1 / delta)) ^ ell := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hXNat : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  apply length_sectionSixAnyState_modulusFiber_le hX hdelta
  · exact sectionSixSourceBandTerminalStates_nodup region hepsilon
      hepsilonSmall hlength hdeltaGap band
  · intro state hstate
    exact sectionSixSourceBandTerminalStates_modulus_le hstate
  · intro state hstate i
    exact sectionSixSourceBandTerminalStates_outerLower hstate i
  · intro state hstate
    exact sectionSixSourceBandTerminalStates_innerRange hstate

theorem length_sectionSixSourceBandTerminalStates_incidenceFiber_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (D : Nat)
    (predicate : SectionSixAnyState band ell → Bool) :
    ((((sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
      hlength hdeltaGap band).filter fun state => state.1 = D).filter
        predicate).length) ≤ 5 * (Nat.ceil (1 / delta)) ^ ell := by
  exact (List.length_filter_le predicate _).trans
    (length_sectionSixSourceBandTerminalStates_modulusFiber_le region
      hepsilon hepsilonSmall hlength hdelta hdeltaGap band D)

end

end PrimesRestrictedDigits
