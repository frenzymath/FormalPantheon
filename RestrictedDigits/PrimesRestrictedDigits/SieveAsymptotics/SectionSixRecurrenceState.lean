import PrimesRestrictedDigits.SieveAsymptotics.SectionSixPrimeFactorSplit
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-!
# Indexed corrected Section 6 recurrence states

This finite wrapper keeps the five printed/repeated state kinds explicit and indexes them by
the low or high product band. It is the representation layer for Proposition 6.1; branch range
predicates and analytic estimates are deliberately supplied by later modules.
-/

namespace PrimesRestrictedDigits

noncomputable section

inductive SectionSixStateBand
  | low
  | high
  deriving DecidableEq, Fintype

inductive SectionSixStateKind
  | T
  | U
  | V
  | RU
  | RV
  deriving DecidableEq, Fintype

structure SectionSixRecurrenceState
    (band : SectionSixStateBand) (ell n : Nat)
    extends SectionSixPrimeFactorSplit ell n where
  kind : SectionSixStateKind

theorem sectionSixStateKind_card : Fintype.card SectionSixStateKind = 5 := by
  decide

theorem sectionSixStateBand_card : Fintype.card SectionSixStateBand = 2 := by
  decide

theorem sectionSixRecurrenceState_pair_injective
    {band : SectionSixStateBand} {ell n : Nat} :
    Function.Injective
      (fun s : SectionSixRecurrenceState band ell n => (s.kind, s.outer)) := by
  intro s t h
  have hkind : s.kind = t.kind := congrArg Prod.fst h
  have houter : s.outer = t.outer := congrArg Prod.snd h
  have hsplit : s.toSectionSixPrimeFactorSplit =
      t.toSectionSixPrimeFactorSplit :=
    sectionSixPrimeFactorSplit_outer_injective houter
  cases s
  cases t
  simp_all

private theorem recurrenceState_outer_mem_support
    {band : SectionSixStateBand} {ell n : Nat}
    (hn : n ≠ 0) (s : SectionSixRecurrenceState band ell n) :
    ∀ i, s.outer i ∈ n.primeFactorsList.toFinset := by
  intro i
  have hdivProduct : s.outer i ∣ primeTupleProduct s.outer := by
    unfold primeTupleProduct
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have houterDvd : primeTupleProduct s.outer ∣ n := by
    exact ⟨s.inner.prod, s.product_eq.symm⟩
  have hdiv : s.outer i ∣ n := hdivProduct.trans houterDvd
  have hmem : s.outer i ∈ n.primeFactorsList :=
    (Nat.mem_primeFactorsList hn).mpr ⟨s.outerPrime i, hdiv⟩
  exact List.mem_toFinset.mpr hmem

theorem card_sectionSixRecurrenceState_le_five_primeSupport_pow
    {band : SectionSixStateBand} {ell n : Nat} (hn : n ≠ 0)
    (S : Finset (SectionSixRecurrenceState band ell n)) :
    S.card ≤ 5 * (n.primeFactorsList.toFinset.card) ^ ell := by
  classical
  let support : Finset Nat := n.primeFactorsList.toFinset
  let tuples : Finset (Fin ell → Nat) :=
    Fintype.piFinset (fun _ : Fin ell => support)
  let target : Finset (SectionSixStateKind × (Fin ell → Nat)) :=
    Finset.univ.product tuples
  have hmem (s : SectionSixRecurrenceState band ell n) (hs : s ∈ S) :
      (s.kind, s.outer) ∈ target := by
    simp [target]
    rw [Fintype.mem_piFinset]
    intro i
    exact recurrenceState_outer_mem_support hn s i
  have himage : S.image (fun s => (s.kind, s.outer)) ⊆ target := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
    exact hmem s hs
  have hinj := sectionSixRecurrenceState_pair_injective
    (band := band) (ell := ell) (n := n)
  calc
    S.card = (S.image (fun s => (s.kind, s.outer))).card :=
      (Finset.card_image_of_injective S hinj).symm
    _ ≤ target.card := Finset.card_le_card himage
    _ = 5 * support.card ^ ell := by
      simp [target, tuples, sectionSixStateKind_card]
    _ = 5 * (n.primeFactorsList.toFinset.card) ^ ell := by rfl

theorem card_sectionSixRecurrenceState_le_five_factorLength_pow
    {band : SectionSixStateBand} {ell n : Nat} (hn : n ≠ 0)
    (S : Finset (SectionSixRecurrenceState band ell n)) :
    S.card ≤ 5 * (n.primeFactorsList.length) ^ ell := by
  have hsupport := card_sectionSixRecurrenceState_le_five_primeSupport_pow hn S
  calc
    S.card ≤ 5 * (n.primeFactorsList.toFinset.card) ^ ell := hsupport
    _ ≤ 5 * (n.primeFactorsList.length) ^ ell := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (List.toFinset_card_le _) _

end

end PrimesRestrictedDigits
