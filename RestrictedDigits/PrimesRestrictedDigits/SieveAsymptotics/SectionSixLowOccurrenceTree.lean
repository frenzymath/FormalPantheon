import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowNormalForm

/-!
# Occurrence-preserving tree for the corrected Section 6 recurrence

Every branch retains its root-relative low path. Local Finsets are converted to lists only to
preserve distinct occurrences under different parents; list order has no mathematical meaning.
-/

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixStateWithKind
    {band : SectionSixStateBand} {ell n : Nat}
    (kind : SectionSixStateKind)
    (state : SectionSixRecurrenceState band ell n) :
    SectionSixRecurrenceState band ell n :=
  { toSectionSixPrimeFactorSplit := state.toSectionSixPrimeFactorSplit
    kind := kind }

@[simp] theorem sectionSixStateWithKind_kind
    {band : SectionSixStateBand} {ell n : Nat}
    (kind : SectionSixStateKind)
    (state : SectionSixRecurrenceState band ell n) :
    (sectionSixStateWithKind kind state).kind = kind :=
  rfl

@[simp] theorem sectionSixStateWithKind_inner
    {band : SectionSixStateBand} {ell n : Nat}
    (kind : SectionSixStateKind)
    (state : SectionSixRecurrenceState band ell n) :
    (sectionSixStateWithKind kind state).inner = state.inner :=
  rfl

structure SectionSixLowActiveOccurrence
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) where
  target : SectionSixLowActiveNode X delta theta R y band ell
  steps : List Nat
  path : SectionSixLowStrictPath root target steps

def sectionSixLowRootOccurrence
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) :
    SectionSixLowActiveOccurrence root :=
  { target := root
    steps := []
    path := SectionSixLowStrictPath.nil root }

structure SectionSixLowTOccurrence
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) where
  parent : SectionSixLowActiveOccurrence root

def sectionSixLowTOccurrenceOfActive
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    SectionSixLowTOccurrence root :=
  ⟨occurrence⟩

def SectionSixLowTOccurrence.state
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowTOccurrence root) :
    SectionSixAnyState band ell :=
  ⟨occurrence.parent.target.state.1,
    sectionSixStateWithKind SectionSixStateKind.T
      occurrence.parent.target.state.2⟩

@[simp] theorem SectionSixLowTOccurrence.state_kind
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowTOccurrence root) :
    occurrence.state.2.kind = SectionSixStateKind.T :=
  rfl

theorem SectionSixLowTOccurrence.state_cutoff
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowTOccurrence root) :
    sectionSixStateCutoffPredicate SectionSixStateKind.T R
      occurrence.state.1 occurrence.state.2.inner := by
  exact occurrence.parent.target.modulus_le

structure SectionSixLowUOccurrence
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) where
  parent : SectionSixLowActiveOccurrence root
  q : Nat
  primeMem : q ∈ sectionSixStateLowPrimeInterval
    parent.target.state R y parent.target.upper

noncomputable def SectionSixLowUOccurrence.child
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowUOccurrence root) :
    SectionSixLowActiveOccurrence root :=
  { target := sectionSixLowActiveChild occurrence.parent.target
      occurrence.q occurrence.primeMem
    steps := occurrence.parent.steps ++ [occurrence.q]
    path := sectionSixLowStrictPath_append occurrence.parent.path
      (SectionSixLowStrictPath.cons occurrence.primeMem
        (SectionSixLowStrictPath.nil _)) }

@[simp] theorem SectionSixLowUOccurrence.child_steps_length
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowUOccurrence root) :
    occurrence.child.steps.length = occurrence.parent.steps.length + 1 := by
  simp [SectionSixLowUOccurrence.child]

structure SectionSixLowVOccurrence
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) where
  parent : SectionSixLowActiveOccurrence root
  q : Nat
  primeMem : q ∈ sectionSixStateHighPrimeInterval
    parent.target.state R y parent.target.upper

structure SectionSixLowRUOccurrence
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) where
  parent : SectionSixLowActiveOccurrence root
  q : Nat
  primeMem : q ∈ sectionSixStateLowPrimeInterval
    parent.target.state R y parent.target.upper

structure SectionSixLowRVOccurrence
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) where
  parent : SectionSixLowActiveOccurrence root
  q : Nat
  primeMem : q ∈ sectionSixStateHighPrimeInterval
    parent.target.state R y parent.target.upper

noncomputable def sectionSixLowUOccurrences
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    List (SectionSixLowUOccurrence root) :=
  (sectionSixStateLowPrimeInterval occurrence.target.state R y
      occurrence.target.upper).attach.toList.map fun
        q : {q // q ∈ sectionSixStateLowPrimeInterval
          occurrence.target.state R y occurrence.target.upper} =>
    { parent := occurrence
      q := q.1
      primeMem := q.property }

noncomputable def sectionSixLowVOccurrences
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    List (SectionSixLowVOccurrence root) :=
  (sectionSixStateHighPrimeInterval occurrence.target.state R y
      occurrence.target.upper).attach.toList.map fun
        q : {q // q ∈ sectionSixStateHighPrimeInterval
          occurrence.target.state R y occurrence.target.upper} =>
    { parent := occurrence
      q := q.1
      primeMem := q.property }

noncomputable def sectionSixLowRUOccurrences
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    List (SectionSixLowRUOccurrence root) :=
  (sectionSixStateLowPrimeInterval occurrence.target.state R y
      occurrence.target.upper).attach.toList.map fun
        q : {q // q ∈ sectionSixStateLowPrimeInterval
          occurrence.target.state R y occurrence.target.upper} =>
    { parent := occurrence
      q := q.1
      primeMem := q.property }

noncomputable def sectionSixLowRVOccurrences
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    List (SectionSixLowRVOccurrence root) :=
  (sectionSixStateHighPrimeInterval occurrence.target.state R y
      occurrence.target.upper).attach.toList.map fun
        q : {q // q ∈ sectionSixStateHighPrimeInterval
          occurrence.target.state R y occurrence.target.upper} =>
    { parent := occurrence
      q := q.1
      primeMem := q.property }

@[simp] theorem sectionSixLowUOccurrences_length
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    (sectionSixLowUOccurrences occurrence).length =
      (sectionSixStateLowPrimeInterval occurrence.target.state R y
        occurrence.target.upper).card := by
  simp [sectionSixLowUOccurrences]

@[simp] theorem sectionSixLowVOccurrences_length
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    (sectionSixLowVOccurrences occurrence).length =
      (sectionSixStateHighPrimeInterval occurrence.target.state R y
        occurrence.target.upper).card := by
  simp [sectionSixLowVOccurrences]

@[simp] theorem sectionSixLowRUOccurrences_length
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    (sectionSixLowRUOccurrences occurrence).length =
      (sectionSixStateLowPrimeInterval occurrence.target.state R y
        occurrence.target.upper).card := by
  simp [sectionSixLowRUOccurrences]

@[simp] theorem sectionSixLowRVOccurrences_length
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    (sectionSixLowRVOccurrences occurrence).length =
      (sectionSixStateHighPrimeInterval occurrence.target.state R y
        occurrence.target.upper).card := by
  simp [sectionSixLowRVOccurrences]

theorem SectionSixLowUOccurrence.stateOccurrence
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowUOccurrence root) :
    SectionSixStatePrimeOccurrence digit length
      occurrence.parent.target.state R y occurrence.parent.target.upper
      (sectionSixStateUStep occurrence.q) :=
  sectionSixStateLowPrime_U_occurrence digit length
    occurrence.parent.target.state occurrence.primeMem
    occurrence.parent.target.ordered

theorem SectionSixLowVOccurrence.stateOccurrence
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowVOccurrence root) :
    SectionSixStatePrimeOccurrence digit length
      occurrence.parent.target.state R y occurrence.parent.target.upper
      (sectionSixStateVStep occurrence.q) :=
  sectionSixStateHighPrime_V_occurrence digit length
    occurrence.parent.target.state occurrence.primeMem
    occurrence.parent.target.modulus_le occurrence.parent.target.ordered

theorem SectionSixLowRUOccurrence.stateOccurrence
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRUOccurrence root) :
    SectionSixStatePrimeOccurrence digit length
      occurrence.parent.target.state R y occurrence.parent.target.upper
      (sectionSixStateRUStep occurrence.q) :=
  sectionSixStateLowPrime_RU_occurrence digit length
    occurrence.parent.target.state occurrence.primeMem
    occurrence.parent.target.ordered

theorem SectionSixLowRVOccurrence.stateOccurrence
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRVOccurrence root) :
    SectionSixStatePrimeOccurrence digit length
      occurrence.parent.target.state R y occurrence.parent.target.upper
      (sectionSixStateRVStep occurrence.q) :=
  sectionSixStateHighPrime_RV_occurrence digit length
    occurrence.parent.target.state occurrence.primeMem
    occurrence.parent.target.modulus_le occurrence.parent.target.ordered

theorem sectionSixLowActiveOccurrence_append_stateOccurrence
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root)
    (step : SectionSixStateStep)
    (occurrence : SectionSixStatePrimeOccurrence digit length
      parent.target.state R y parent.target.upper step) :
    SectionSixStatePath root.state
      (sectionSixStateStepChild parent.target.state step
        occurrence.prime occurrence.order)
      (parent.steps.map sectionSixStateUStep ++ [step]) := by
  exact sectionSixStatePath_append
    (sectionSixLowStrictPath_to_statePath parent.path) occurrence.path

inductive SectionSixLowOccurrenceTree
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) where
  | residualActive (occurrence : SectionSixLowActiveOccurrence root)
  | expanded (base : SectionSixLowTOccurrence root)
      (uBranches : List
        (SectionSixLowUOccurrence root × SectionSixLowOccurrenceTree root))
      (vLeaves : List (SectionSixLowVOccurrence root))
      (ruLeaves : List (SectionSixLowRUOccurrence root))
      (rvLeaves : List (SectionSixLowRVOccurrence root))

noncomputable def sectionSixLowOccurrenceTreeOfFuel
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) :
    Nat → SectionSixLowActiveOccurrence root →
      SectionSixLowOccurrenceTree root
  | 0, occurrence => .residualActive occurrence
  | fuel + 1, occurrence =>
      .expanded (sectionSixLowTOccurrenceOfActive occurrence)
        ((sectionSixLowUOccurrences occurrence).map fun branch =>
          (branch, sectionSixLowOccurrenceTreeOfFuel root fuel branch.child))
        (sectionSixLowVOccurrences occurrence)
        (sectionSixLowRUOccurrences occurrence)
        (sectionSixLowRVOccurrences occurrence)

inductive SectionSixLowOccurrenceTree.ResidualFree
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell} :
    SectionSixLowOccurrenceTree root → Prop
  | expanded {base uBranches vLeaves ruLeaves rvLeaves}
      (children : ∀ branch ∈ uBranches, ResidualFree branch.2) :
      ResidualFree (.expanded base uBranches vLeaves ruLeaves rvLeaves)

/- `ResidualFree` records only the absence of residual constructors. Parent
coherence and canonical child subtrees are supplied by
`sectionSixLowOccurrenceTreeOfFuel`, not by this predicate on arbitrary trees. -/

theorem sectionSixLowOccurrenceTreeOfFuel_residualFree
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (hX : 1 < X) (hdelta : 0 < delta)
    (fuel : Nat) (occurrence : SectionSixLowActiveOccurrence root)
    (hbudget : Nat.ceil (1 / delta) < occurrence.steps.length + fuel) :
    (sectionSixLowOccurrenceTreeOfFuel root fuel occurrence).ResidualFree := by
  induction fuel generalizing occurrence with
  | zero =>
      have hlength := sectionSixLowStrictPath_length_le_ceil_inv_delta
        hX hdelta occurrence.path
      simp only [Nat.add_zero] at hbudget
      omega
  | succ fuel ih =>
      apply SectionSixLowOccurrenceTree.ResidualFree.expanded
      intro branch hbranch
      rcases List.mem_map.mp hbranch with ⟨edge, hedge, rfl⟩
      rcases List.mem_map.mp hedge with ⟨q, hq, rfl⟩
      apply ih
      simp only [SectionSixLowUOccurrence.child_steps_length]
      omega

theorem sectionSixLowOccurrenceTreeOfFuel_root_residualFree
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell)
    (hX : 1 < X) (hdelta : 0 < delta) :
    (sectionSixLowOccurrenceTreeOfFuel root
      (Nat.ceil (1 / delta) + 1)
      (sectionSixLowRootOccurrence root)).ResidualFree := by
  apply sectionSixLowOccurrenceTreeOfFuel_residualFree hX hdelta
  simp [sectionSixLowRootOccurrence]

end

end PrimesRestrictedDigits
