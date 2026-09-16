import PrimesRestrictedDigits.SieveAsymptotics.SectionSixSourceTerminalStates
import Mathlib.Tactic.Linarith

/-!
# Exact represented carriers for Section 6 terminal states

The cofactor carrier follows the canonical terminal kind. Its represented carrier is the
injective image under multiplication by the complete modulus. Correctness statements are
restricted to canonical source-band list.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The total first-inner-prime projection. Canonical non-`T` terminals prove
that the fallback value is never used. -/
def sectionSixTerminalFirstInnerPrime
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Nat :=
  state.2.inner.headD 0

/-- The sieve threshold attached to a projected terminal state. The `U` value
is irrelevant because its carrier is empty. -/
def sectionSixTerminalThreshold
    (y : Real) {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Real :=
  match state.2.kind with
  | .T => y
  | .U => y
  | .V => sectionSixTerminalFirstInnerPrime state
  | .RU => sectionSixTerminalFirstInnerPrime state
  | .RV => sectionSixTerminalFirstInnerPrime state

/-- The exact strict or weak cofactor carrier of a projected terminal state. -/
noncomputable def sectionSixTerminalCofactorCarrier
    (C : Finset Nat) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Finset Nat :=
  let dilation := sieveDilation C (sectionSixStateModulusPNat state.2)
  match state.2.kind with
  | .T => strictSiftedCarrier dilation y
  | .U => ∅
  | .V => strictSiftedCarrier dilation (sectionSixTerminalThreshold y state)
  | .RU => weakSiftedCarrier dilation (sectionSixTerminalThreshold y state)
  | .RV => weakSiftedCarrier dilation (sectionSixTerminalThreshold y state)

/-- Multiplication by the positive complete modulus. -/
def sectionSixTerminalRepresentedEmbedding
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Nat ↪ Nat :=
  { toFun := fun m => m * state.1
    inj' := mul_left_injective₀
      (Nat.ne_of_gt (sectionSixRecurrenceState_modulus_pos state.2)) }

/-- The exact carrier of represented integers `m*D`. -/
noncomputable def sectionSixTerminalRepresentedCarrier
    (C : Finset Nat) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Finset Nat :=
  (sectionSixTerminalCofactorCarrier C y state).map
    (sectionSixTerminalRepresentedEmbedding state)

/-- Boolean selector for the two corrected repeated terminal kinds. -/
def sectionSixRepeatedTerminalPredicate
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Bool :=
  state.2.kind == .RU || state.2.kind == .RV

@[simp] theorem sectionSixRepeatedTerminalPredicate_eq_true
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) :
    sectionSixRepeatedTerminalPredicate state = true ↔
      state.2.kind = .RU ∨ state.2.kind = .RV := by
  simp [sectionSixRepeatedTerminalPredicate]

@[simp] theorem mem_sectionSixTerminalRepresentedCarrier
    {C : Finset Nat} {y : Real}
    {band : SectionSixStateBand} {ell n : Nat}
    {state : SectionSixAnyState band ell} :
    n ∈ sectionSixTerminalRepresentedCarrier C y state ↔
      ∃ m ∈ sectionSixTerminalCofactorCarrier C y state,
        m * state.1 = n := by
  simp [sectionSixTerminalRepresentedCarrier,
    sectionSixTerminalRepresentedEmbedding]

private theorem sectionSixSourceBandTerminalStates_exists_term
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
      ∃ term : SectionSixLowTerminalOccurrence
          (sectionSixSourceBandRootOfMember hepsilon hepsilonSmall hlength
            hdeltaGap band source),
        term ∈ sectionSixLowTerminalOccurrences
          (sectionSixLowOccurrenceTreeOfFuel
            (sectionSixSourceBandRootOfMember hepsilon hepsilonSmall hlength
              hdeltaGap band source)
            (Nat.ceil (1 / delta) + 1)
            (sectionSixLowRootOccurrence
              (sectionSixSourceBandRootOfMember hepsilon hepsilonSmall hlength
                hdeltaGap band source))) ∧
          term.state = state := by
  unfold sectionSixSourceBandTerminalStates at hstate
  rcases List.mem_flatMap.mp hstate with ⟨source, hsource, hstate⟩
  unfold sectionSixSourceMemberTerminalStates at hstate
  rcases List.mem_map.mp hstate with ⟨term, hterm, htermState⟩
  exact ⟨source, term, hterm, htermState⟩

/-- Canonical terminal source lists never contain the recursive `U` kind. -/
theorem sectionSixSourceBandTerminalStates_kind_ne_U
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    state.2.kind ≠ .U := by
  rcases sectionSixSourceBandTerminalStates_exists_term hstate with
    ⟨source, term, hterm, htermState⟩
  subst state
  cases term <;> simp

/-- On a canonical terminal state, the total projected threshold is at least
the source lower threshold. -/
theorem sectionSixSourceBandTerminalStates_threshold_lower
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    ((10 ^ length : Nat) : Real) ^ delta ≤
      sectionSixTerminalThreshold (((10 ^ length : Nat) : Real) ^ delta)
        state := by
  rcases sectionSixSourceBandTerminalStates_exists_term hstate with
    ⟨source, term, hterm, htermState⟩
  subst state
  cases term with
  | base occurrence => simp [sectionSixTerminalThreshold]
  | strictHigh occurrence =>
      have hq := (SectionSixLowTerminalOccurrence.state_innerRange
        (SectionSixLowTerminalOccurrence.strictHigh occurrence))
        occurrence.q (by simp)
      simpa [sectionSixTerminalThreshold,
        sectionSixTerminalFirstInnerPrime] using hq.1.le
  | repeatedLow occurrence =>
      have hq := (SectionSixLowTerminalOccurrence.state_innerRange
        (SectionSixLowTerminalOccurrence.repeatedLow occurrence))
        occurrence.q (by simp)
      simpa [sectionSixTerminalThreshold,
        sectionSixTerminalFirstInnerPrime] using hq.1.le
  | repeatedHigh occurrence =>
      have hq := (SectionSixLowTerminalOccurrence.state_innerRange
        (SectionSixLowTerminalOccurrence.repeatedHigh occurrence))
        occurrence.q (by simp)
      simpa [sectionSixTerminalThreshold,
        sectionSixTerminalFirstInnerPrime] using hq.1.le

private theorem sectionSixRecurrenceState_modulus_weakRough
    {band : SectionSixStateBand} {ell n : Nat} {y : Real}
    (state : SectionSixRecurrenceState band ell n)
    (houter : ∀ i, y ≤ (state.outer i : Real))
    (hinner : ∀ q, q ∈ state.inner → y ≤ (q : Real)) :
    weakRoughPredicate y n := by
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

/-- Every prime factor of a canonical complete modulus is at least the source
lower threshold. -/
theorem sectionSixSourceBandTerminalStates_modulus_weakRough
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    weakRoughPredicate (((10 ^ length : Nat) : Real) ^ delta) state.1 := by
  apply sectionSixRecurrenceState_modulus_weakRough state.2
  · exact sectionSixSourceBandTerminalStates_outerLower hstate
  · intro q hq
    exact (sectionSixSourceBandTerminalStates_innerRange hstate q hq).1.le

private theorem weakRoughPredicate_mono_threshold
    {y z : Real} {n : Nat} (hyz : y ≤ z)
    (hrough : weakRoughPredicate z n) : weakRoughPredicate y n := by
  intro p hp hpn
  exact hyz.trans (hrough p hp hpn)

private theorem strictRoughPredicate_to_weak
    {y z : Real} {n : Nat} (hyz : y ≤ z)
    (hrough : strictRoughPredicate z n) : weakRoughPredicate y n := by
  intro p hp hpn
  exact hyz.trans (hrough p hp hpn).le

private theorem ne_zero_of_five_le_of_weakRough
    {y : Real} {n : Nat} (hy : 5 ≤ y)
    (hrough : weakRoughPredicate y n) : n ≠ 0 := by
  intro hn
  subst n
  have htwo := hrough 2 Nat.prime_two (dvd_zero 2)
  have hfalse : ¬(5 : Real) ≤ 2 := by norm_num
  exact hfalse (hy.trans htwo)

/-- Exact represented carrier membership preserves the underlying carrier,
positivity, complete-modulus divisibility, and source-scale roughness. -/
theorem sectionSixSourceBandTerminalRepresentedCarrier_mem_data
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
    (hn : n ∈ sectionSixTerminalRepresentedCarrier C
      (((10 ^ length : Nat) : Real) ^ delta) state) :
    n ∈ C ∧ 0 < n ∧ state.1 ∣ n ∧
      weakRoughPredicate (((10 ^ length : Nat) : Real) ^ delta) n := by
  let y : Real := ((10 ^ length : Nat) : Real) ^ delta
  change 5 ≤ y at hy
  change n ∈ sectionSixTerminalRepresentedCarrier C y state at hn
  rcases mem_sectionSixTerminalRepresentedCarrier.mp hn with
    ⟨m, hm, hmn⟩
  have hthreshold : y ≤ sectionSixTerminalThreshold y state := by
    exact sectionSixSourceBandTerminalStates_threshold_lower hstate
  have hmCarrier : m * state.1 ∈ C := by
    cases hkind : state.2.kind with
    | T =>
        have hmData : m ∈ strictSiftedCarrier
            (sieveDilation C (sectionSixStateModulusPNat state.2)) y := by
          simpa [sectionSixTerminalCofactorCarrier, hkind] using hm
        exact mem_sieveDilation.mp (mem_strictSiftedCarrier.mp hmData).1
    | U =>
        have : m ∈ (∅ : Finset Nat) := by
          simp [sectionSixTerminalCofactorCarrier, hkind] at hm
        simp at this
    | V =>
        have hmData : m ∈ strictSiftedCarrier
            (sieveDilation C (sectionSixStateModulusPNat state.2))
              (sectionSixTerminalThreshold y state) := by
          simpa [sectionSixTerminalCofactorCarrier, hkind] using hm
        exact mem_sieveDilation.mp (mem_strictSiftedCarrier.mp hmData).1
    | RU =>
        have hmData : m ∈ weakSiftedCarrier
            (sieveDilation C (sectionSixStateModulusPNat state.2))
              (sectionSixTerminalThreshold y state) := by
          simpa [sectionSixTerminalCofactorCarrier, hkind] using hm
        exact mem_sieveDilation.mp (mem_weakSiftedCarrier.mp hmData).1
    | RV =>
        have hmData : m ∈ weakSiftedCarrier
            (sieveDilation C (sectionSixStateModulusPNat state.2))
              (sectionSixTerminalThreshold y state) := by
          simpa [sectionSixTerminalCofactorCarrier, hkind] using hm
        exact mem_sieveDilation.mp (mem_weakSiftedCarrier.mp hmData).1
  have hmRough : weakRoughPredicate y m := by
    cases hkind : state.2.kind with
    | T =>
        have hmData : m ∈ strictSiftedCarrier
            (sieveDilation C (sectionSixStateModulusPNat state.2)) y := by
          simpa [sectionSixTerminalCofactorCarrier, hkind] using hm
        exact strictRoughPredicate_to_weak le_rfl
          (mem_strictSiftedCarrier.mp hmData).2
    | U =>
        have : m ∈ (∅ : Finset Nat) := by
          simp [sectionSixTerminalCofactorCarrier, hkind] at hm
        simp at this
    | V =>
        have hmData : m ∈ strictSiftedCarrier
            (sieveDilation C (sectionSixStateModulusPNat state.2))
              (sectionSixTerminalThreshold y state) := by
          simpa [sectionSixTerminalCofactorCarrier, hkind] using hm
        exact strictRoughPredicate_to_weak hthreshold
          (mem_strictSiftedCarrier.mp hmData).2
    | RU =>
        have hmData : m ∈ weakSiftedCarrier
            (sieveDilation C (sectionSixStateModulusPNat state.2))
              (sectionSixTerminalThreshold y state) := by
          simpa [sectionSixTerminalCofactorCarrier, hkind] using hm
        exact weakRoughPredicate_mono_threshold hthreshold
          (mem_weakSiftedCarrier.mp hmData).2
    | RV =>
        have hmData : m ∈ weakSiftedCarrier
            (sieveDilation C (sectionSixStateModulusPNat state.2))
              (sectionSixTerminalThreshold y state) := by
          simpa [sectionSixTerminalCofactorCarrier, hkind] using hm
        exact weakRoughPredicate_mono_threshold hthreshold
          (mem_weakSiftedCarrier.mp hmData).2
  have hmPos : 0 < m := Nat.pos_of_ne_zero
    (ne_zero_of_five_le_of_weakRough hy hmRough)
  have hDPos : 0 < state.1 := sectionSixRecurrenceState_modulus_pos state.2
  have hDrough : weakRoughPredicate y state.1 :=
    sectionSixSourceBandTerminalStates_modulus_weakRough hstate
  have hnRough : weakRoughPredicate y n := by
    intro p hp hpn
    rw [← hmn] at hpn
    rcases hp.dvd_mul.mp hpn with hpm | hpD
    · exact hmRough p hp hpm
    · exact hDrough p hp hpD
  refine ⟨?_, ?_, ?_, hnRough⟩
  · simpa only [hmn] using hmCarrier
  · rw [← hmn]
    exact Nat.mul_pos hmPos hDPos
  · refine ⟨m, ?_⟩
    simpa [Nat.mul_comm] using hmn.symm

/-- Canonical repeated terminals retain their terminal prime twice in the
complete modulus. -/
theorem sectionSixSourceBandTerminalStates_repeatedSquare
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band)
    (hrepeated : state.2.kind = .RU ∨ state.2.kind = .RV) :
    ∃ q, q ∈ sievePrimeInterval
        (((10 ^ length : Nat) : Real) ^ delta)
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) ∧
      q * q ∣ state.1 := by
  rcases sectionSixSourceBandTerminalStates_exists_term hstate with
    ⟨source, term, hterm, htermState⟩
  subst state
  cases term with
  | base occurrence => simp at hrepeated
  | strictHigh occurrence => simp at hrepeated
  | repeatedLow occurrence =>
      refine ⟨occurrence.q, ?_, ?_⟩
      · have hq := (SectionSixLowTerminalOccurrence.state_innerRange
          (SectionSixLowTerminalOccurrence.repeatedLow occurrence))
          occurrence.q (by simp)
        exact mem_sievePrimeInterval.mpr ⟨occurrence.prime, hq.1, hq.2⟩
      · refine ⟨occurrence.parent.target.state.1, ?_⟩
        simp [ Nat.mul_left_comm, Nat.mul_comm]
  | repeatedHigh occurrence =>
      refine ⟨occurrence.q, ?_, ?_⟩
      · have hq := (SectionSixLowTerminalOccurrence.state_innerRange
          (SectionSixLowTerminalOccurrence.repeatedHigh occurrence))
          occurrence.q (by simp)
        exact mem_sievePrimeInterval.mpr ⟨occurrence.prime, hq.1, hq.2⟩
      · refine ⟨occurrence.parent.target.state.1, ?_⟩
        simp [ Nat.mul_left_comm, Nat.mul_comm]

/-- A represented member of a canonical repeated carrier has the same large
prime square divisor. -/
theorem sectionSixSourceBandTerminalRepresentedCarrier_repeatedSquare
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
    (hrepeated : state.2.kind = .RU ∨ state.2.kind = .RV)
    (hn : n ∈ sectionSixTerminalRepresentedCarrier C
      (((10 ^ length : Nat) : Real) ^ delta) state) :
    ∃ q, q ∈ sievePrimeInterval
        (((10 ^ length : Nat) : Real) ^ delta)
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) ∧
      q * q ∣ n := by
  rcases sectionSixSourceBandTerminalStates_repeatedSquare hstate hrepeated with
    ⟨q, hq, hqD⟩
  have hDn :=
    (sectionSixSourceBandTerminalRepresentedCarrier_mem_data hy hstate hn).2.2.1
  exact ⟨q, hq, hqD.trans hDn⟩

end

end PrimesRestrictedDigits
