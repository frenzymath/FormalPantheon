import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRecurrenceRanges
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract

/-!
# Source-tuple constructors for corrected Section 6 states

This is the finite bridge from a Proposition 6.1 outer tuple and a sorted inner prime list to
the indexed complete-modulus state record.
-/

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixRecurrenceStateOfSourceTuple
    {epsilon : Real} {length ell : Nat}
    {region : Set (Fin ell → Real)}
    (band : SectionSixStateBand) (kind : SectionSixStateKind)
    (p : Fin ell → Nat) (inner : List Nat)
    (hp : IsPropositionSixOnePrimeTuple epsilon length region p)
    (hinnerPrime : ∀ q, q ∈ inner → q.Prime)
    (hinnerSorted : inner.SortedLE) :
    SectionSixRecurrenceState band ell
      (primeTupleProduct p * inner.prod) :=
  { toSectionSixPrimeFactorSplit :=
      { outer := p
        inner := inner
        outerPrime := hp.1
        innerPrime := hinnerPrime
        outerMonotone := hp.2.1
        innerSorted := hinnerSorted
        product_eq := rfl }
    kind := kind }

theorem sectionSixSourceTuple_outerProduct_pos
    {epsilon : Real} {length ell : Nat}
    {region : Set (Fin ell → Real)} {p : Fin ell → Nat}
    (hp : IsPropositionSixOnePrimeTuple epsilon length region p) :
    0 < primeTupleProduct p := by
  rw [primeTupleProduct]
  exact Finset.prod_pos fun i hi => (hp.1 i).pos

theorem sectionSixSourceTuple_innerProduct_pos
    {inner : List Nat} (hinnerPrime : ∀ q, q ∈ inner → q.Prime) :
    0 < inner.prod := by
  apply List.prod_pos
  intro q hq
  exact (hinnerPrime q hq).pos

theorem sectionSixRecurrenceStateOfSourceTuple_modulus_ne_zero
    {epsilon : Real} {length ell : Nat}
    {region : Set (Fin ell → Real)} {p : Fin ell → Nat}
    {inner : List Nat}
    (hp : IsPropositionSixOnePrimeTuple epsilon length region p)
    (hinnerPrime : ∀ q, q ∈ inner → q.Prime) :
    primeTupleProduct p * inner.prod ≠ 0 := by
  exact Nat.mul_ne_zero
    (Nat.ne_of_gt (sectionSixSourceTuple_outerProduct_pos hp))
    (Nat.ne_of_gt (sectionSixSourceTuple_innerProduct_pos hinnerPrime))

theorem isSectionSixRecurrenceStateOfSourceTuple
    {epsilon : Real} {length ell : Nat}
    {region : Set (Fin ell → Real)}
    (band : SectionSixStateBand) (kind : SectionSixStateKind)
    (p : Fin ell → Nat) (inner : List Nat)
    (hp : IsPropositionSixOnePrimeTuple epsilon length region p)
    (hinnerPrime : ∀ q, q ∈ inner → q.Prime)
    (hinnerSorted : inner.SortedLE)
    {X delta theta thetaOne thetaTwo : Real}
    (hrange : sectionSixStateInnerRange X delta theta inner)
    (hcutoff : sectionSixStateCutoffPredicate kind
      (sectionSixStateBandCutoff band X thetaOne thetaTwo)
      (primeTupleProduct p * inner.prod) inner) :
    IsSectionSixRecurrenceState X delta theta thetaOne thetaTwo
      (sectionSixRecurrenceStateOfSourceTuple band kind p inner hp
        hinnerPrime hinnerSorted) := by
  exact ⟨hrange, hcutoff⟩

end

end PrimesRestrictedDigits
