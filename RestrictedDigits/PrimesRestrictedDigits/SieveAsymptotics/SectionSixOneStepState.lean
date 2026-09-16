import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRecurrenceRanges

/-!
# One-step strict and repeated corrected Section 6 states

Prepending the next ordered prime once gives the strict child; prepending it twice gives the
weak equality-fiber child. Branch range certificates remain explicit inputs.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem sortedLE_cons_of_forall_le
    {q : Nat} {inner : List Nat}
    (hq : ∀ r, r ∈ inner → q ≤ r) (hsorted : inner.SortedLE) :
    (q :: inner).SortedLE := by
  rw [List.sortedLE_iff_pairwise] at hsorted ⊢
  simp only [List.pairwise_cons]
  exact ⟨hq, hsorted⟩

private theorem sortedLE_double_cons_of_forall_le
    {q : Nat} {inner : List Nat}
    (hq : ∀ r, r ∈ inner → q ≤ r) (hsorted : inner.SortedLE) :
    (q :: q :: inner).SortedLE := by
  have htail : (q :: inner).SortedLE :=
    sortedLE_cons_of_forall_le hq hsorted
  apply sortedLE_cons_of_forall_le
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_rfl
    · exact hq r hr
  · exact htail

def sectionSixStrictChild
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n)
    (kind : SectionSixStateKind) (q : Nat) (hq : q.Prime)
    (horder : ∀ r, r ∈ s.inner → q ≤ r) :
    SectionSixRecurrenceState band ell (n * q) :=
  { toSectionSixPrimeFactorSplit :=
      { outer := s.outer
        inner := q :: s.inner
        outerPrime := s.outerPrime
        innerPrime := by
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hq
          · exact s.innerPrime r hr
        outerMonotone := s.outerMonotone
        innerSorted := sortedLE_cons_of_forall_le horder s.innerSorted
        product_eq := by
          simp only [List.prod_cons]
          calc
            primeTupleProduct s.outer * (q * s.inner.prod) =
                (primeTupleProduct s.outer * s.inner.prod) * q := by ring
            _ = n * q := by rw [s.product_eq] }
    kind := kind }

def sectionSixRepeatedChild
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n)
    (kind : SectionSixStateKind) (q : Nat) (hq : q.Prime)
    (horder : ∀ r, r ∈ s.inner → q ≤ r) :
    SectionSixRecurrenceState band ell (n * q * q) :=
  { toSectionSixPrimeFactorSplit :=
      { outer := s.outer
        inner := q :: q :: s.inner
        outerPrime := s.outerPrime
        innerPrime := by
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hq
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hq
          · exact s.innerPrime r hr
        outerMonotone := s.outerMonotone
        innerSorted := sortedLE_double_cons_of_forall_le horder s.innerSorted
        product_eq := by
          simp only [List.prod_cons]
          calc
            primeTupleProduct s.outer * (q * (q * s.inner.prod)) =
                (primeTupleProduct s.outer * s.inner.prod) * q * q := by ring
            _ = n * q * q := by rw [s.product_eq] }
    kind := kind }

theorem sectionSixStrictChild_cutoff_U
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n)
    (q : Nat) (hq : q.Prime)
    (horder : ∀ r, r ∈ s.inner → q ≤ r)
    {R : Real} (hcutoff : ((n * q : Nat) : Real) ≤ R) :
    sectionSixStateCutoffPredicate SectionSixStateKind.U R
      (n * q) (sectionSixStrictChild s SectionSixStateKind.U q hq horder).inner := by
  change ((n * q : Nat) : Real) ≤ R
  exact hcutoff

theorem sectionSixStrictChild_cutoff_V
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n)
    (q : Nat) (hq : q.Prime)
    (horder : ∀ r, r ∈ s.inner → q ≤ r)
    {R : Real} (hlower : R < ((n * q : Nat) : Real))
    (hupper : ((n * q : Nat) : Real) ≤ R * (q : Real)) :
    sectionSixStateCutoffPredicate SectionSixStateKind.V R
      (n * q) (sectionSixStrictChild s SectionSixStateKind.V q hq horder).inner := by
  refine ⟨q, s.inner, rfl, ?_, hlower, hupper⟩
  exact ⟨n, by ring⟩

theorem sectionSixRepeatedChild_cutoff_RU
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n)
    (q : Nat) (hq : q.Prime)
    (horder : ∀ r, r ∈ s.inner → q ≤ r)
    {R : Real} (hcutoff : ((n * q : Nat) : Real) ≤ R) :
    sectionSixStateCutoffPredicate SectionSixStateKind.RU R
      (n * q * q)
      (sectionSixRepeatedChild s SectionSixStateKind.RU q hq horder).inner := by
  refine ⟨q, s.inner, rfl, ⟨n * q, by ring⟩, ?_⟩
  have hdiv : (n * q * q) / q = n * q := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_div_cancel_left (n * q) hq.pos
  rw [hdiv]
  exact hcutoff

theorem sectionSixRepeatedChild_cutoff_RV
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n)
    (q : Nat) (hq : q.Prime)
    (horder : ∀ r, r ∈ s.inner → q ≤ r)
    {R : Real} (hlower : R < ((n * q : Nat) : Real))
    (hupper : ((n * q : Nat) : Real) ≤ R * (q : Real)) :
    sectionSixStateCutoffPredicate SectionSixStateKind.RV R
      (n * q * q)
      (sectionSixRepeatedChild s SectionSixStateKind.RV q hq horder).inner := by
  have hdiv : (n * q * q) / q = n * q := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_div_cancel_left (n * q) hq.pos
  refine ⟨q, s.inner, rfl, ⟨n * q, by ring⟩, ?_, ?_⟩
  · rw [hdiv]
    exact hlower
  · rw [hdiv]
    exact hupper

theorem sectionSixStrictChild_innerRange
    {band : SectionSixStateBand} {ell n : Nat}
    {X delta theta : Real}
    (s : SectionSixRecurrenceState band ell n)
    (q : Nat) (hqRange : X ^ delta < (q : Real) ∧
      (q : Real) ≤ X ^ theta)
    (hinner : sectionSixStateInnerRange X delta theta s.inner) :
    sectionSixStateInnerRange X delta theta (q :: s.inner) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hqRange
  · exact hinner r hr

theorem sectionSixRepeatedChild_innerRange
    {band : SectionSixStateBand} {ell n : Nat}
    {X delta theta : Real}
    (s : SectionSixRecurrenceState band ell n)
    (q : Nat) (hqRange : X ^ delta < (q : Real) ∧
      (q : Real) ≤ X ^ theta)
    (hinner : sectionSixStateInnerRange X delta theta s.inner) :
    sectionSixStateInnerRange X delta theta (q :: q :: s.inner) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hqRange
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hqRange
  · exact hinner r hr

end

end PrimesRestrictedDigits
