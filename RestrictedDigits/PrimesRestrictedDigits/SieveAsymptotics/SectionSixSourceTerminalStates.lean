import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowTerminalNodup
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalModulusBound

/-!
# Source-band terminal-state enumeration

This module concatenates the canonical terminal-state lists over the attached Proposition 6.1
source tuples in one fixed band. Equality of projected outer tuples separates different source
roots.
-/

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def sectionSixSourceBandPrimeTuples
    (epsilon : Real) (ell : Nat) (region : Set (Fin ell → Real))
    (length : Nat) (band : SectionSixStateBand) :
    Finset (Fin ell → Nat) := by
  classical
  exact (propositionSixOnePrimeTuples epsilon ell region length).filter fun p =>
    sectionSixSourceBandMembership band
      ((10 ^ length : Nat) : Real)
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleProduct p : Real)

@[simp] theorem mem_sectionSixSourceBandPrimeTuples
    {epsilon : Real} {ell : Nat} {region : Set (Fin ell → Real)}
    {length : Nat} {band : SectionSixStateBand} {p : Fin ell → Nat} :
    p ∈ sectionSixSourceBandPrimeTuples epsilon ell region length band ↔
      p ∈ propositionSixOnePrimeTuples epsilon ell region length ∧
        sectionSixSourceBandMembership band
          ((10 ^ length : Nat) : Real)
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
          (primeTupleProduct p : Real) := by
  simp [sectionSixSourceBandPrimeTuples]

theorem sectionSixSourceBandCutoff_le_decimalScale
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    {length : Nat} (hlength : 1 ≤ length)
    (band : SectionSixStateBand) :
    sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
        (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ≤
      ((10 ^ length : Nat) : Real) := by
  have hXNat : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
    exact_mod_cast hXNat
  cases band with
  | low =>
      exact (Real.rpow_le_rpow_of_exponent_le hX.le
        (sectionSix_parameter_bounds hepsilon hepsilonSmall).2.2.1.le).trans_eq
          (Real.rpow_one _)
  | high =>
      exact (Real.rpow_le_rpow_of_exponent_le hX.le
        (by linarith [sectionSix_parameter_bounds hepsilon hepsilonSmall])).trans_eq
          (Real.rpow_one _)

noncomputable def sectionSixSourceBandRootOfMember
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band}) :=
  sectionSixSourceBandRoot hlength band source.1
    ((mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).mp
      (mem_sectionSixSourceBandPrimeTuples.mp source.property).1)
    delta hdeltaGap
    (mem_sectionSixSourceBandPrimeTuples.mp source.property).2
    (sectionSixSourceBandCutoff_le_decimalScale
      hepsilon hepsilonSmall hlength band)

noncomputable def sectionSixSourceMemberTerminalStates
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band}) :
    List (SectionSixAnyState band ell) :=
  let root := sectionSixSourceBandRootOfMember hepsilon hepsilonSmall
    hlength hdeltaGap band source
  let tree := sectionSixLowOccurrenceTreeOfFuel root
    (Nat.ceil (1 / delta) + 1) (sectionSixLowRootOccurrence root)
  (sectionSixLowTerminalOccurrences tree).map
    SectionSixLowTerminalOccurrence.state

theorem sectionSixSourceMemberTerminalStates_nodup
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band}) :
    (sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall hlength
      hdeltaGap band source).Nodup := by
  unfold sectionSixSourceMemberTerminalStates
  exact sectionSixLowTerminalOccurrences_state_nodup
    (Nat.ceil (1 / delta) + 1) _

theorem sectionSixSourceMemberTerminalStates_outer
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band})
    {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceMemberTerminalStates hepsilon
      hepsilonSmall hlength hdeltaGap band source) :
    state.2.outer = source.1 := by
  unfold sectionSixSourceMemberTerminalStates at hstate
  rcases List.mem_map.mp hstate with ⟨term, hterm, rfl⟩
  rw [SectionSixLowTerminalOccurrence.state_outer,
    sectionSixLowStrictPath_target_outer term.parent.path]
  rfl

theorem sectionSixSourceMemberTerminalStates_outerLower
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band})
    {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceMemberTerminalStates hepsilon
      hepsilonSmall hlength hdeltaGap band source) :
    ∀ i, ((10 ^ length : Nat) : Real) ^ delta ≤
      (state.2.outer i : Real) := by
  unfold sectionSixSourceMemberTerminalStates at hstate
  rcases List.mem_map.mp hstate with ⟨term, hterm, rfl⟩
  exact term.state_outerLower

theorem sectionSixSourceMemberTerminalStates_innerRange
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band})
    {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceMemberTerminalStates hepsilon
      hepsilonSmall hlength hdeltaGap band source) :
    sectionSixStateInnerRange ((10 ^ length : Nat) : Real) delta
      (sectionSixThetaGap epsilon) state.2.inner := by
  unfold sectionSixSourceMemberTerminalStates at hstate
  rcases List.mem_map.mp hstate with ⟨term, hterm, rfl⟩
  exact term.state_innerRange

theorem sectionSixSourceMemberTerminalStates_modulus_le
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band})
    {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceMemberTerminalStates hepsilon
      hepsilonSmall hlength hdeltaGap band source) :
    (state.1 : Real) ≤ ((10 ^ length : Nat) : Real) := by
  unfold sectionSixSourceMemberTerminalStates at hstate
  rcases List.mem_map.mp hstate with ⟨term, hterm, rfl⟩
  apply term.source_state_modulus_le hepsilon hepsilonSmall hlength

noncomputable def sectionSixSourceBandTerminalStates
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) : List (SectionSixAnyState band ell) :=
  (sectionSixSourceBandPrimeTuples epsilon ell region length band).attach.toList.flatMap
    fun source => sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall
      hlength hdeltaGap band source

theorem sectionSixSourceBandTerminalStates_nodup
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) :
    (sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
      hlength hdeltaGap band).Nodup := by
  unfold sectionSixSourceBandTerminalStates
  rw [List.nodup_flatMap]
  constructor
  · intro source hsource
    exact sectionSixSourceMemberTerminalStates_nodup hepsilon hepsilonSmall
      hlength hdeltaGap band source
  · have hsources := Finset.nodup_toList
      (sectionSixSourceBandPrimeTuples epsilon ell region length band).attach
    apply hsources.imp
    intro sourceOne sourceTwo hne
    change List.Disjoint
      (sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall hlength
        hdeltaGap band sourceOne)
      (sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall hlength
        hdeltaGap band sourceTwo)
    rw [List.disjoint_left]
    intro state hstateOne hstateTwo
    apply hne
    apply Subtype.ext
    exact (sectionSixSourceMemberTerminalStates_outer hepsilon hepsilonSmall
      hlength hdeltaGap band sourceOne hstateOne).symm.trans
        (sectionSixSourceMemberTerminalStates_outer hepsilon hepsilonSmall
          hlength hdeltaGap band sourceTwo hstateTwo)

private theorem sectionSixSourceBandTerminalStates_mem
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
      state ∈ sectionSixSourceMemberTerminalStates hepsilon
        hepsilonSmall hlength hdeltaGap band source := by
  unfold sectionSixSourceBandTerminalStates at hstate
  rcases List.mem_flatMap.mp hstate with ⟨source, hsource, hstate⟩
  exact ⟨source, hstate⟩

theorem sectionSixSourceBandTerminalStates_outerLower
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    ∀ i, ((10 ^ length : Nat) : Real) ^ delta ≤
      (state.2.outer i : Real) := by
  rcases sectionSixSourceBandTerminalStates_mem hstate with
    ⟨source, hsource⟩
  exact sectionSixSourceMemberTerminalStates_outerLower hepsilon
    hepsilonSmall hlength hdeltaGap band source hsource

theorem sectionSixSourceBandTerminalStates_innerRange
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    sectionSixStateInnerRange ((10 ^ length : Nat) : Real) delta
      (sectionSixThetaGap epsilon) state.2.inner := by
  rcases sectionSixSourceBandTerminalStates_mem hstate with
    ⟨source, hsource⟩
  exact sectionSixSourceMemberTerminalStates_innerRange hepsilon
    hepsilonSmall hlength hdeltaGap band source hsource

theorem sectionSixSourceBandTerminalStates_modulus_le
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon ≤ 1 / 64}
    {hlength : 1 ≤ length}
    {hdeltaGap : delta ≤ sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    (state.1 : Real) ≤ ((10 ^ length : Nat) : Real) := by
  rcases sectionSixSourceBandTerminalStates_mem hstate with
    ⟨source, hsource⟩
  exact sectionSixSourceMemberTerminalStates_modulus_le hepsilon
    hepsilonSmall hlength hdeltaGap band source hsource

end

end PrimesRestrictedDigits
