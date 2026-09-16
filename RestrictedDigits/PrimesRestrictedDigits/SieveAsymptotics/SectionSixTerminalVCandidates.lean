import PrimesRestrictedDigits.SieveAsymptotics.SectionSixNonrepeatedSignedContribution
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Terminal V candidates

Canonical terminal `V` states are paired with their exact cofactors. The dependent carrier
retains state labels even when represented naturals collide.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A terminal-V occurrence retains its canonical state and cofactor. -/
abbrev SectionSixTerminalVCandidate
    (band : SectionSixStateBand) (ell : Nat) :=
  Sigma fun _ : SectionSixAnyState band ell => Nat

/-- The recurrence sign attached to a terminal-V state. -/
def sectionSixTerminalVStateSign
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Real :=
  (-1 : Real) ^ state.2.inner.length

namespace SectionSixTerminalVCandidate

/-- The natural represented by a state-cofactor occurrence. -/
def represented
    {band : SectionSixStateBand} {ell : Nat}
    (candidate : SectionSixTerminalVCandidate band ell) : Nat :=
  candidate.2 * candidate.1.1

/-- The recurrence sign of the candidate's state. -/
def sign
    {band : SectionSixStateBand} {ell : Nat}
    (candidate : SectionSixTerminalVCandidate band ell) : Real :=
  sectionSixTerminalVStateSign candidate.1

/-- The signed Section 6 weight of one candidate occurrence. -/
def signedWeight
    {band : SectionSixStateBand} {ell : Nat}
    (A B : Finset Nat) (lambda : Real)
    (candidate : SectionSixTerminalVCandidate band ell) : Real :=
  candidate.sign *
    sectionSixWeight A B lambda candidate.represented

end SectionSixTerminalVCandidate

/-- All canonical terminal-V occurrences over the carrier `C`. -/
noncomputable def sectionSixSourceBandTerminalVFullCandidates
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat) (y : Real) :
    Finset (SectionSixTerminalVCandidate band ell) := by
  classical
  exact
    ((sectionSixSourceBandTerminalStateFinset region hepsilon
      hepsilonSmall hlength hdeltaGap band).filter
        (fun state => sectionSixTerminalVPredicate state)).sigma
      fun state => sectionSixTerminalCofactorCarrier C y state

/-- Terminal-V occurrences whose represented natural lies in `nearSet`. -/
noncomputable def sectionSixSourceBandTerminalVNearCandidates
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat) (y : Real)
    (nearSet : Finset Nat) :
    Finset (SectionSixTerminalVCandidate band ell) :=
  (sectionSixSourceBandTerminalVFullCandidates region hepsilon
    hepsilonSmall hlength hdeltaGap band C y).filter
      fun candidate => candidate.represented ∈ nearSet

/-- Terminal-V occurrences whose represented natural lies outside `nearSet`. -/
noncomputable def sectionSixSourceBandTerminalVOutsideCandidates
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat) (y : Real)
    (nearSet : Finset Nat) :
    Finset (SectionSixTerminalVCandidate band ell) :=
  (sectionSixSourceBandTerminalVFullCandidates region hepsilon
    hepsilonSmall hlength hdeltaGap band C y).filter
      fun candidate => candidate.represented ∉ nearSet

@[simp] theorem mem_sectionSixSourceBandTerminalVFullCandidates
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {C : Finset Nat} {y : Real}
    {candidate : SectionSixTerminalVCandidate band ell} :
    candidate ∈ sectionSixSourceBandTerminalVFullCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band C y <->
      candidate.1 ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
          hepsilonSmall hlength hdeltaGap band ∧
      sectionSixTerminalVPredicate candidate.1 = true ∧
      candidate.2 ∈ sectionSixTerminalCofactorCarrier C y candidate.1 := by
  simp [sectionSixSourceBandTerminalVFullCandidates, and_assoc]

@[simp] theorem mem_sectionSixSourceBandTerminalVNearCandidates
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {C nearSet : Finset Nat} {y : Real}
    {candidate : SectionSixTerminalVCandidate band ell} :
    candidate ∈ sectionSixSourceBandTerminalVNearCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band C y nearSet <->
      candidate ∈ sectionSixSourceBandTerminalVFullCandidates region hepsilon
          hepsilonSmall hlength hdeltaGap band C y ∧
      candidate.represented ∈ nearSet := by
  simp [sectionSixSourceBandTerminalVNearCandidates]

@[simp] theorem mem_sectionSixSourceBandTerminalVOutsideCandidates
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {C nearSet : Finset Nat} {y : Real}
    {candidate : SectionSixTerminalVCandidate band ell} :
    candidate ∈ sectionSixSourceBandTerminalVOutsideCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band C y nearSet <->
      candidate ∈ sectionSixSourceBandTerminalVFullCandidates region hepsilon
          hepsilonSmall hlength hdeltaGap band C y ∧
      candidate.represented ∉ nearSet := by
  simp [sectionSixSourceBandTerminalVOutsideCandidates]

/-- For a `V` state, restriction changes only represented membership. -/
theorem mem_sectionSixTerminalCofactorCarrier_iff_of_subset_of_kind_eq_V
    {A B : Finset Nat} (hAB : A ⊆ B) {y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) (hV : state.2.kind = .V)
    {m : Nat} :
    m ∈ sectionSixTerminalCofactorCarrier A y state <->
      m ∈ sectionSixTerminalCofactorCarrier B y state ∧
      m * state.1 ∈ A := by
  simp only [sectionSixTerminalCofactorCarrier, hV,
    mem_strictSiftedCarrier, mem_sieveDilation,
    sectionSixStateModulusPNat_coe]
  constructor
  · rintro ⟨hmA, hmRough⟩
    exact ⟨⟨hAB hmA, hmRough⟩, hmA⟩
  · rintro ⟨⟨_hmB, hmRough⟩, hmA⟩
    exact ⟨hmA, hmRough⟩

/-- Finset form of the V-specific cofactor restriction identity. -/
theorem sectionSixTerminalCofactorCarrier_eq_filter_of_subset_of_kind_eq_V
    {A B : Finset Nat} (hAB : A ⊆ B) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) (hV : state.2.kind = .V) :
    sectionSixTerminalCofactorCarrier A y state =
      (sectionSixTerminalCofactorCarrier B y state).filter
        (fun m => m * state.1 ∈ A) := by
  ext m
  simp only [Finset.mem_filter]
  exact mem_sectionSixTerminalCofactorCarrier_iff_of_subset_of_kind_eq_V
    hAB state hV

/-- Restricted full occurrences are ambient occurrences with value in `A`. -/
theorem mem_sectionSixSourceBandTerminalVFullCandidates_iff_of_subset
    {A B : Finset Nat} (hAB : A ⊆ B)
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {y : Real}
    {candidate : SectionSixTerminalVCandidate band ell} :
    candidate ∈ sectionSixSourceBandTerminalVFullCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band A y <->
      candidate ∈ sectionSixSourceBandTerminalVFullCandidates region hepsilon
          hepsilonSmall hlength hdeltaGap band B y ∧
      candidate.represented ∈ A := by
  constructor
  · intro hcA
    have hdata := mem_sectionSixSourceBandTerminalVFullCandidates.mp hcA
    have hV : candidate.1.2.kind = .V := by
      simpa [sectionSixTerminalVPredicate] using hdata.2.1
    have hmData :=
      (mem_sectionSixTerminalCofactorCarrier_iff_of_subset_of_kind_eq_V
        hAB candidate.1 hV).mp hdata.2.2
    exact ⟨mem_sectionSixSourceBandTerminalVFullCandidates.mpr
      ⟨hdata.1, hdata.2.1, hmData.1⟩, hmData.2⟩
  · rintro ⟨hcB, hrepresented⟩
    have hdata := mem_sectionSixSourceBandTerminalVFullCandidates.mp hcB
    have hV : candidate.1.2.kind = .V := by
      simpa [sectionSixTerminalVPredicate] using hdata.2.1
    apply mem_sectionSixSourceBandTerminalVFullCandidates.mpr
    refine ⟨hdata.1, hdata.2.1, ?_⟩
    exact
      (mem_sectionSixTerminalCofactorCarrier_iff_of_subset_of_kind_eq_V
        hAB candidate.1 hV).mpr ⟨hdata.2.2, hrepresented⟩

/-- Finset form of the full terminal-V restriction identity. -/
theorem sectionSixSourceBandTerminalVFullCandidates_eq_filter_of_subset
    {A B : Finset Nat} (hAB : A ⊆ B)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) :
    sectionSixSourceBandTerminalVFullCandidates region hepsilon hepsilonSmall
        hlength hdeltaGap band A y =
      (sectionSixSourceBandTerminalVFullCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band B y).filter
          (fun candidate => candidate.represented ∈ A) := by
  ext candidate
  simp only [Finset.mem_filter]
  exact mem_sectionSixSourceBandTerminalVFullCandidates_iff_of_subset hAB

/-- Restricted near occurrences are ambient near occurrences with value in A. -/
theorem mem_sectionSixSourceBandTerminalVNearCandidates_iff_of_subset
    {A B : Finset Nat} (hAB : A ⊆ B)
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {y : Real} {nearSet : Finset Nat}
    {candidate : SectionSixTerminalVCandidate band ell} :
    candidate ∈ sectionSixSourceBandTerminalVNearCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band A y nearSet <->
      candidate ∈ sectionSixSourceBandTerminalVNearCandidates region hepsilon
          hepsilonSmall hlength hdeltaGap band B y nearSet ∧
      candidate.represented ∈ A := by
  constructor
  · intro hcA
    have hdata := mem_sectionSixSourceBandTerminalVNearCandidates.mp hcA
    have hfull :=
      (mem_sectionSixSourceBandTerminalVFullCandidates_iff_of_subset hAB).mp
        hdata.1
    exact ⟨mem_sectionSixSourceBandTerminalVNearCandidates.mpr
      ⟨hfull.1, hdata.2⟩, hfull.2⟩
  · rintro ⟨hcB, hrepresented⟩
    have hdata := mem_sectionSixSourceBandTerminalVNearCandidates.mp hcB
    apply mem_sectionSixSourceBandTerminalVNearCandidates.mpr
    exact ⟨
      (mem_sectionSixSourceBandTerminalVFullCandidates_iff_of_subset hAB).mpr
        ⟨hdata.1, hrepresented⟩,
      hdata.2⟩

/-- Finset form of the near terminal-V restriction identity. -/
theorem sectionSixSourceBandTerminalVNearCandidates_eq_filter_of_subset
    {A B : Finset Nat} (hAB : A ⊆ B)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) (nearSet : Finset Nat) :
    sectionSixSourceBandTerminalVNearCandidates region hepsilon hepsilonSmall
        hlength hdeltaGap band A y nearSet =
      (sectionSixSourceBandTerminalVNearCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band B y nearSet).filter
          (fun candidate => candidate.represented ∈ A) := by
  ext candidate
  simp only [Finset.mem_filter]
  exact mem_sectionSixSourceBandTerminalVNearCandidates_iff_of_subset hAB

/-- Restricted outside occurrences are ambient outside occurrences in `A`. -/
theorem mem_sectionSixSourceBandTerminalVOutsideCandidates_iff_of_subset
    {A B : Finset Nat} (hAB : A ⊆ B)
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {y : Real} {nearSet : Finset Nat}
    {candidate : SectionSixTerminalVCandidate band ell} :
    candidate ∈ sectionSixSourceBandTerminalVOutsideCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band A y nearSet <->
      candidate ∈ sectionSixSourceBandTerminalVOutsideCandidates region
          hepsilon hepsilonSmall hlength hdeltaGap band B y nearSet ∧
      candidate.represented ∈ A := by
  constructor
  · intro hcA
    have hdata := mem_sectionSixSourceBandTerminalVOutsideCandidates.mp hcA
    have hfull :=
      (mem_sectionSixSourceBandTerminalVFullCandidates_iff_of_subset hAB).mp
        hdata.1
    exact ⟨mem_sectionSixSourceBandTerminalVOutsideCandidates.mpr
      ⟨hfull.1, hdata.2⟩, hfull.2⟩
  · rintro ⟨hcB, hrepresented⟩
    have hdata := mem_sectionSixSourceBandTerminalVOutsideCandidates.mp hcB
    apply mem_sectionSixSourceBandTerminalVOutsideCandidates.mpr
    exact ⟨
      (mem_sectionSixSourceBandTerminalVFullCandidates_iff_of_subset hAB).mpr
        ⟨hdata.1, hrepresented⟩,
      hdata.2⟩

/-- Finset form of the outside terminal-V restriction identity. -/
theorem sectionSixSourceBandTerminalVOutsideCandidates_eq_filter_of_subset
    {A B : Finset Nat} (hAB : A ⊆ B)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) (nearSet : Finset Nat) :
    sectionSixSourceBandTerminalVOutsideCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band A y nearSet =
      (sectionSixSourceBandTerminalVOutsideCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band B y nearSet).filter
          (fun candidate => candidate.represented ∈ A) := by
  ext candidate
  simp only [Finset.mem_filter]
  exact mem_sectionSixSourceBandTerminalVOutsideCandidates_iff_of_subset hAB

end

end PrimesRestrictedDigits
