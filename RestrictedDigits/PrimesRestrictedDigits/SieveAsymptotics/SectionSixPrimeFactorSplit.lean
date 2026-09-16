import PrimesRestrictedDigits.MajorArcs.Factorization
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.NormNum

/-!
# Finite prime-factor split multiplicity

For a fixed complete modulus, a sorted inner prime list is unique once the outer tuple is
fixed. This is the finite factorization bound needed before the Section 6 recurrence states
are embedded.
-/

namespace PrimesRestrictedDigits

noncomputable section

structure SectionSixPrimeFactorSplit (ell n : Nat) where
  outer : Fin ell -> Nat
  inner : List Nat
  outerPrime : forall i, (outer i).Prime
  innerPrime : forall p, p ∈ inner -> p.Prime
  outerMonotone : Monotone outer
  innerSorted : inner.SortedLE
  product_eq : primeTupleProduct outer * inner.prod = n

theorem sectionSixPrimeFactorSplit_outer_injective
    {ell n : Nat} :
    Function.Injective
      (fun s : SectionSixPrimeFactorSplit ell n => s.outer) := by
  intro s t houter
  have houterProduct : primeTupleProduct s.outer =
      primeTupleProduct t.outer := congrArg primeTupleProduct houter
  have houterPos : 0 < primeTupleProduct s.outer := by
    rw [primeTupleProduct]
    exact Finset.prod_pos fun i hi => (s.outerPrime i).pos
  have hinnerProduct : s.inner.prod = t.inner.prod := by
    apply Nat.mul_left_cancel houterPos
    calc
      primeTupleProduct s.outer * s.inner.prod = n := s.product_eq
      _ = primeTupleProduct t.outer * t.inner.prod := t.product_eq.symm
      _ = primeTupleProduct s.outer * t.inner.prod := by rw [houterProduct]
  have hpermS : List.Perm s.inner (s.inner.prod).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · rfl
    · exact s.innerPrime
  have hpermT : List.Perm t.inner (t.inner.prod).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · rfl
    · exact t.innerPrime
  have hperm : List.Perm s.inner t.inner := by
    have hmid : List.Perm (s.inner.prod).primeFactorsList
        (t.inner.prod).primeFactorsList := by
      rw [hinnerProduct]
    exact hpermS.trans (hmid.trans hpermT.symm)
  have hinner : s.inner = t.inner :=
    hperm.eq_of_sortedLE s.innerSorted t.innerSorted
  cases s
  cases t
  simp_all

theorem card_sectionSixPrimeFactorSplit_le_primeSupport_pow
    {ell n : Nat} (hn : n ≠ 0)
    (S : Finset (SectionSixPrimeFactorSplit ell n)) :
    S.card ≤ (n.primeFactorsList.toFinset.card) ^ ell := by
  classical
  let support : Finset Nat := n.primeFactorsList.toFinset
  let outerTuples : Finset (Fin ell -> Nat) :=
    Fintype.piFinset (fun _ : Fin ell => support)
  have houterMem (s : SectionSixPrimeFactorSplit ell n) (hs : s ∈ S) :
      s.outer ∈ outerTuples := by
    simp only [outerTuples, Fintype.mem_piFinset]
    intro i
    have hdivProduct : s.outer i ∣ primeTupleProduct s.outer := by
      unfold primeTupleProduct
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have houterDvd : primeTupleProduct s.outer ∣ n := by
      exact ⟨s.inner.prod, s.product_eq.symm⟩
    have hdiv : s.outer i ∣ n := hdivProduct.trans houterDvd
    have hmem : s.outer i ∈ n.primeFactorsList :=
      (Nat.mem_primeFactorsList hn).mpr ⟨s.outerPrime i, hdiv⟩
    change s.outer i ∈ n.primeFactorsList.toFinset
    exact List.mem_toFinset.mpr hmem
  have himage : S.image (fun s => s.outer) ⊆ outerTuples := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨s, hs, rfl⟩
    exact houterMem s hs
  have hinj := sectionSixPrimeFactorSplit_outer_injective (ell := ell) (n := n)
  calc
    S.card = (S.image (fun s => s.outer)).card :=
      (Finset.card_image_of_injective S hinj).symm
    _ ≤ outerTuples.card := Finset.card_le_card himage
    _ = support.card ^ ell := by
      simp [outerTuples, Fintype.card_fin]
    _ = (n.primeFactorsList.toFinset.card) ^ ell := by rfl

theorem card_sectionSixPrimeFactorSplit_le_factorLength_pow
    {ell n : Nat} (hn : n ≠ 0)
    (S : Finset (SectionSixPrimeFactorSplit ell n)) :
    S.card ≤ (n.primeFactorsList.length) ^ ell := by
  have hsupport := card_sectionSixPrimeFactorSplit_le_primeSupport_pow hn S
  exact hsupport.trans (Nat.pow_le_pow_left (List.toFinset_card_le _) _)

end

end PrimesRestrictedDigits
