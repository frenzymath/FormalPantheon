import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowOccurrenceTreeValue

/-!
# Terminal occurrences for the corrected Section 6 recurrence

The four terminal families project injectively to indexed recurrence states for one fixed
active root. Chronological low-path primes are recovered from the reversed prefix of the
target inner list.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixLowStrictPath_target_inner
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat}
    (path : SectionSixLowStrictPath start target steps) :
    target.state.2.inner = steps.reverse ++ start.state.2.inner := by
  induction path with
  | nil node => simp
  | @cons node target rest q hq tail ih =>
      rw [ih]
      simp [sectionSixLowActiveChild, sectionSixStrictChild, List.append_assoc]

theorem sectionSixLowStrictPath_target_unique
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {start targetOne targetTwo :
      SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat}
    (pathOne : SectionSixLowStrictPath start targetOne steps)
    (pathTwo : SectionSixLowStrictPath start targetTwo steps) :
    targetOne = targetTwo := by
  induction pathOne generalizing targetTwo with
  | nil node =>
      cases pathTwo
      rfl
  | @cons node targetOne rest q hqOne tailOne ih =>
      cases pathTwo with
      | cons hqTwo tailTwo =>
          have hhq : hqOne = hqTwo := Subsingleton.elim _ _
          subst hqTwo
          exact ih tailTwo

theorem sectionSixLowActiveOccurrence_inner_injective
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell} :
    Function.Injective (fun occurrence : SectionSixLowActiveOccurrence root =>
      occurrence.target.state.2.inner) := by
  intro occurrenceOne occurrenceTwo hinner
  have hreverse : occurrenceOne.steps.reverse =
      occurrenceTwo.steps.reverse := by
    apply List.append_left_injective root.state.2.inner
    calc
      occurrenceOne.steps.reverse ++ root.state.2.inner =
          occurrenceOne.target.state.2.inner :=
        (sectionSixLowStrictPath_target_inner occurrenceOne.path).symm
      _ = occurrenceTwo.target.state.2.inner := hinner
      _ = occurrenceTwo.steps.reverse ++ root.state.2.inner :=
        sectionSixLowStrictPath_target_inner occurrenceTwo.path
  have hsteps : occurrenceOne.steps = occurrenceTwo.steps :=
    List.reverse_injective hreverse
  cases occurrenceOne with
  | mk targetOne stepsOne pathOne =>
      cases occurrenceTwo with
      | mk targetTwo stepsTwo pathTwo =>
          dsimp only at hsteps
          subst stepsTwo
          have htarget : targetOne = targetTwo :=
            sectionSixLowStrictPath_target_unique pathOne pathTwo
          subst targetTwo
          rfl

theorem sectionSixLowActiveOccurrence_state_injective
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell} :
    Function.Injective (fun occurrence : SectionSixLowActiveOccurrence root =>
      occurrence.target.state) := by
  intro occurrenceOne occurrenceTwo hstate
  apply sectionSixLowActiveOccurrence_inner_injective
  exact congrArg (fun state => state.2.inner) hstate

theorem SectionSixLowVOccurrence.parent_eq_of_mem
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root)
    (occurrence : SectionSixLowVOccurrence root)
    (hoccurrence : occurrence ∈ sectionSixLowVOccurrences parent) :
    occurrence.parent = parent := by
  unfold sectionSixLowVOccurrences at hoccurrence
  rcases List.mem_map.mp hoccurrence with ⟨q, hq, rfl⟩
  rfl

theorem SectionSixLowRUOccurrence.parent_eq_of_mem
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root)
    (occurrence : SectionSixLowRUOccurrence root)
    (hoccurrence : occurrence ∈ sectionSixLowRUOccurrences parent) :
    occurrence.parent = parent := by
  unfold sectionSixLowRUOccurrences at hoccurrence
  rcases List.mem_map.mp hoccurrence with ⟨q, hq, rfl⟩
  rfl

theorem SectionSixLowRVOccurrence.parent_eq_of_mem
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root)
    (occurrence : SectionSixLowRVOccurrence root)
    (hoccurrence : occurrence ∈ sectionSixLowRVOccurrences parent) :
    occurrence.parent = parent := by
  unfold sectionSixLowRVOccurrences at hoccurrence
  rcases List.mem_map.mp hoccurrence with ⟨q, hq, rfl⟩
  rfl

theorem SectionSixLowVOccurrence.prime
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowVOccurrence root) : occurrence.q.Prime := by
  exact (mem_sievePrimeInterval.mp
    (mem_sectionSixStateHighPrimeInterval.mp occurrence.primeMem).1).1

theorem SectionSixLowVOccurrence.order
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowVOccurrence root) :
    ∀ r, r ∈ occurrence.parent.target.state.2.inner → occurrence.q ≤ r := by
  exact sectionSixStateNextPrime_order
    (mem_sectionSixStateHighPrimeInterval.mp occurrence.primeMem).1
    occurrence.parent.target.ordered

theorem SectionSixLowRUOccurrence.prime
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRUOccurrence root) : occurrence.q.Prime :=
  sectionSixLowActivePrime occurrence.parent.target occurrence.primeMem

theorem SectionSixLowRUOccurrence.order
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRUOccurrence root) :
    ∀ r, r ∈ occurrence.parent.target.state.2.inner → occurrence.q ≤ r :=
  sectionSixLowActiveOrder occurrence.parent.target occurrence.primeMem

theorem SectionSixLowRVOccurrence.prime
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRVOccurrence root) : occurrence.q.Prime := by
  exact (mem_sievePrimeInterval.mp
    (mem_sectionSixStateHighPrimeInterval.mp occurrence.primeMem).1).1

theorem SectionSixLowRVOccurrence.order
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRVOccurrence root) :
    ∀ r, r ∈ occurrence.parent.target.state.2.inner → occurrence.q ≤ r := by
  exact sectionSixStateNextPrime_order
    (mem_sectionSixStateHighPrimeInterval.mp occurrence.primeMem).1
    occurrence.parent.target.ordered

noncomputable def SectionSixLowVOccurrence.state
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowVOccurrence root) :
    SectionSixAnyState band ell :=
  sectionSixStateStepChild occurrence.parent.target.state
    (sectionSixStateVStep occurrence.q)
    occurrence.prime occurrence.order

noncomputable def SectionSixLowRUOccurrence.state
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRUOccurrence root) :
    SectionSixAnyState band ell :=
  sectionSixStateStepChild occurrence.parent.target.state
    (sectionSixStateRUStep occurrence.q)
    occurrence.prime occurrence.order

noncomputable def SectionSixLowRVOccurrence.state
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRVOccurrence root) :
    SectionSixAnyState band ell :=
  sectionSixStateStepChild occurrence.parent.target.state
    (sectionSixStateRVStep occurrence.q)
    occurrence.prime occurrence.order

inductive SectionSixLowTerminalOccurrence
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) where
  | base (occurrence : SectionSixLowTOccurrence root)
  | strictHigh (occurrence : SectionSixLowVOccurrence root)
  | repeatedLow (occurrence : SectionSixLowRUOccurrence root)
  | repeatedHigh (occurrence : SectionSixLowRVOccurrence root)

def SectionSixLowTerminalOccurrence.parent
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell} :
    SectionSixLowTerminalOccurrence root -> SectionSixLowActiveOccurrence root
  | .base occurrence => occurrence.parent
  | .strictHigh occurrence => occurrence.parent
  | .repeatedLow occurrence => occurrence.parent
  | .repeatedHigh occurrence => occurrence.parent

noncomputable def SectionSixLowTerminalOccurrence.state
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell} :
    SectionSixLowTerminalOccurrence root -> SectionSixAnyState band ell
  | .base occurrence => occurrence.state
  | .strictHigh occurrence => occurrence.state
  | .repeatedLow occurrence => occurrence.state
  | .repeatedHigh occurrence => occurrence.state

@[simp] theorem SectionSixLowTerminalOccurrence.state_kind
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (term : SectionSixLowTerminalOccurrence root) :
    term.state.2.kind = match term with
      | .base _ => SectionSixStateKind.T
      | .strictHigh _ => SectionSixStateKind.V
      | .repeatedLow _ => SectionSixStateKind.RU
      | .repeatedHigh _ => SectionSixStateKind.RV := by
  cases term <;> rfl

@[simp] theorem SectionSixLowTerminalOccurrence.state_outer
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (term : SectionSixLowTerminalOccurrence root) :
    term.state.2.outer = term.parent.target.state.2.outer := by
  cases term <;> rfl

@[simp] theorem SectionSixLowTerminalOccurrence.state_inner
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (term : SectionSixLowTerminalOccurrence root) :
    term.state.2.inner = match term with
      | .base occurrence => occurrence.parent.target.state.2.inner
      | .strictHigh occurrence =>
          occurrence.q :: occurrence.parent.target.state.2.inner
      | .repeatedLow occurrence =>
          occurrence.q :: occurrence.q ::
            occurrence.parent.target.state.2.inner
      | .repeatedHigh occurrence =>
          occurrence.q :: occurrence.q ::
            occurrence.parent.target.state.2.inner := by
  cases term <;> rfl

@[simp] theorem SectionSixLowTerminalOccurrence.state_modulus
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (term : SectionSixLowTerminalOccurrence root) :
    term.state.1 = match term with
      | .base occurrence => occurrence.parent.target.state.1
      | .strictHigh occurrence =>
          occurrence.parent.target.state.1 * occurrence.q
      | .repeatedLow occurrence =>
          occurrence.parent.target.state.1 * occurrence.q * occurrence.q
      | .repeatedHigh occurrence =>
          occurrence.parent.target.state.1 * occurrence.q * occurrence.q := by
  cases term <;> rfl

theorem sectionSixLowTerminalOccurrence_state_injective
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell} :
    Function.Injective
      (SectionSixLowTerminalOccurrence.state (root := root)) := by
  intro termOne termTwo hstate
  cases termOne with
  | base occurrenceOne =>
      cases termTwo with
      | base occurrenceTwo =>
          have hinner : occurrenceOne.parent.target.state.2.inner =
              occurrenceTwo.parent.target.state.2.inner :=
            congrArg (fun state => state.2.inner) hstate
          have hparent := sectionSixLowActiveOccurrence_inner_injective hinner
          cases occurrenceOne
          cases occurrenceTwo
          simp_all
      | strictHigh occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
      | repeatedLow occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
      | repeatedHigh occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
  | strictHigh occurrenceOne =>
      cases termTwo with
      | base occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
      | strictHigh occurrenceTwo =>
          have hinner := congrArg (fun state => state.2.inner) hstate
          have hq : occurrenceOne.q = occurrenceTwo.q :=
            (List.cons.inj hinner).1
          have hparentInner : occurrenceOne.parent.target.state.2.inner =
              occurrenceTwo.parent.target.state.2.inner :=
            (List.cons.inj hinner).2
          have hparent :=
            sectionSixLowActiveOccurrence_inner_injective hparentInner
          cases occurrenceOne
          cases occurrenceTwo
          simp_all
      | repeatedLow occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
      | repeatedHigh occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
  | repeatedLow occurrenceOne =>
      cases termTwo with
      | base occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
      | strictHigh occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
      | repeatedLow occurrenceTwo =>
          have hinner := congrArg (fun state => state.2.inner) hstate
          have hq : occurrenceOne.q = occurrenceTwo.q :=
            (List.cons.inj hinner).1
          have htail := (List.cons.inj hinner).2
          have hparentInner : occurrenceOne.parent.target.state.2.inner =
              occurrenceTwo.parent.target.state.2.inner :=
            (List.cons.inj htail).2
          have hparent :=
            sectionSixLowActiveOccurrence_inner_injective hparentInner
          cases occurrenceOne
          cases occurrenceTwo
          simp_all
      | repeatedHigh occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
  | repeatedHigh occurrenceOne =>
      cases termTwo with
      | base occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
      | strictHigh occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
      | repeatedLow occurrenceTwo =>
          have hkind := congrArg (fun state => state.2.kind) hstate
          contradiction
      | repeatedHigh occurrenceTwo =>
          have hinner := congrArg (fun state => state.2.inner) hstate
          have hq : occurrenceOne.q = occurrenceTwo.q :=
            (List.cons.inj hinner).1
          have htail := (List.cons.inj hinner).2
          have hparentInner : occurrenceOne.parent.target.state.2.inner =
              occurrenceTwo.parent.target.state.2.inner :=
            (List.cons.inj htail).2
          have hparent :=
            sectionSixLowActiveOccurrence_inner_injective hparentInner
          cases occurrenceOne
          cases occurrenceTwo
          simp_all

private theorem sectionSixLowTerminalPrime_range
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root) {q : Nat}
    (hq : q ∈ sievePrimeInterval y parent.target.upper) :
    X ^ delta < (q : Real) ∧ (q : Real) ≤ X ^ theta := by
  have hinterval := mem_sievePrimeInterval.mp hq
  constructor
  · rw [← parent.target.y_eq]
    exact hinterval.2.1
  · exact hinterval.2.2.trans parent.target.upper_le_range

theorem SectionSixLowTerminalOccurrence.state_outerLower
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (term : SectionSixLowTerminalOccurrence root) :
    ∀ i, X ^ delta ≤ (term.state.2.outer i : Real) := by
  intro i
  rw [term.state_outer]
  exact term.parent.target.outerLower i

theorem SectionSixLowTerminalOccurrence.state_innerRange
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (term : SectionSixLowTerminalOccurrence root) :
    sectionSixStateInnerRange X delta theta term.state.2.inner := by
  cases term with
  | base occurrence =>
      exact occurrence.parent.target.innerRange
  | strictHigh occurrence =>
      have data := occurrence.stateOccurrence (0 : Fin 10) 0
      exact sectionSixStateStepChild_inner_range occurrence.parent.target.state
        (sectionSixStateVStep occurrence.q) data.prime data.order
        (sectionSixLowTerminalPrime_range occurrence.parent data.primeMem)
        occurrence.parent.target.innerRange
  | repeatedLow occurrence =>
      have data := occurrence.stateOccurrence (0 : Fin 10) 0
      exact sectionSixStateStepChild_inner_range occurrence.parent.target.state
        (sectionSixStateRUStep occurrence.q) data.prime data.order
        (sectionSixLowTerminalPrime_range occurrence.parent data.primeMem)
        occurrence.parent.target.innerRange
  | repeatedHigh occurrence =>
      have data := occurrence.stateOccurrence (0 : Fin 10) 0
      exact sectionSixStateStepChild_inner_range occurrence.parent.target.state
        (sectionSixStateRVStep occurrence.q) data.prime data.order
        (sectionSixLowTerminalPrime_range occurrence.parent data.primeMem)
        occurrence.parent.target.innerRange

theorem SectionSixLowTerminalOccurrence.state_cutoff
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (term : SectionSixLowTerminalOccurrence root) :
    sectionSixStateCutoffPredicate term.state.2.kind R
      term.state.1 term.state.2.inner := by
  cases term with
  | base occurrence =>
      exact occurrence.state_cutoff
  | strictHigh occurrence =>
      exact (occurrence.stateOccurrence (0 : Fin 10) 0).cutoff
  | repeatedLow occurrence =>
      exact (occurrence.stateOccurrence (0 : Fin 10) 0).cutoff
  | repeatedHigh occurrence =>
      exact (occurrence.stateOccurrence (0 : Fin 10) 0).cutoff

theorem SectionSixLowTerminalOccurrence.isRecurrenceState
    {X delta theta R y thetaOne thetaTwo : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (term : SectionSixLowTerminalOccurrence root)
    (hR : R = sectionSixStateBandCutoff band X thetaOne thetaTwo) :
    IsSectionSixRecurrenceState X delta theta thetaOne thetaTwo term.state.2 := by
  exact ⟨term.state_innerRange, by simpa [← hR] using term.state_cutoff⟩

end

end PrimesRestrictedDigits
