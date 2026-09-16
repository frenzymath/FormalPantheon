import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectRepeatedCarrier

/-!
# Exact carriers for direct strict Section 6 terms

The direct strict and repeated terms have the same accepted `(p,q)` index set, but the strict
complete modulus contains only one copy of `q`. This file keeps that distinction explicit
before the strict cofactor is represented as an integer multiple of `d*q`.
-/

namespace PrimesRestrictedDigits

noncomputable section

open scoped BigOperators

/-- A direct strict index is the same accepted outer-tuple/continuation-prime
pair used by the repeated branch. -/
abbrev SectionSixDirectStrictIndex (ell : Nat) :=
  SectionSixDirectRepeatedIndex ell

/-- The positive once-dilated modulus `d*q`. -/
def sectionSixDirectStrictModulus
    {ell : Nat} (index : SectionSixDirectStrictIndex ell) : PNat :=
  (primeTupleProduct index.1).toPNat' * Nat.toPNat' index.2

/-- The natural complete key used for divisor incidence. -/
def sectionSixDirectStrictKey
    {ell : Nat} (index : SectionSixDirectStrictIndex ell) : Nat :=
  (sectionSixDirectStrictModulus index : Nat)

/-- Multiplication by the positive strict complete modulus. -/
def sectionSixDirectStrictRepresentedEmbedding
    {ell : Nat} (index : SectionSixDirectStrictIndex ell) : Nat ↪ Nat :=
  { toFun := fun m => m * sectionSixDirectStrictKey index
    inj' := mul_left_injective₀
      (PNat.ne_zero (sectionSixDirectStrictModulus index)) }

/-- The strictly sifted cofactor carrier before multiplication by `d*q`. -/
noncomputable def sectionSixDirectStrictCofactorCarrier
    (C : Finset Nat) {ell : Nat}
    (index : SectionSixDirectStrictIndex ell) : Finset Nat :=
  strictSiftedCarrier
    (sieveDilation C (sectionSixDirectStrictModulus index))
    (index.2 : Real)

/-- The exact represented-integer carrier for one direct strict index. -/
noncomputable def sectionSixDirectStrictRepresentedCarrier
    (C : Finset Nat) {ell : Nat}
    (index : SectionSixDirectStrictIndex ell) : Finset Nat :=
  (sectionSixDirectStrictCofactorCarrier C index).map
    (sectionSixDirectStrictRepresentedEmbedding index)

@[simp] theorem mem_sectionSixDirectStrictRepresentedCarrier
    {C : Finset Nat} {ell n : Nat}
    {index : SectionSixDirectStrictIndex ell} :
    n ∈ sectionSixDirectStrictRepresentedCarrier C index ↔
      ∃ m ∈ sectionSixDirectStrictCofactorCarrier C index,
        m * sectionSixDirectStrictKey index = n := by
  simp [sectionSixDirectStrictRepresentedCarrier,
    sectionSixDirectStrictRepresentedEmbedding]

theorem card_sectionSixDirectStrictRepresentedCarrier_eq
    {C : Finset Nat} {ell : Nat}
    (index : SectionSixDirectStrictIndex ell) :
    (sectionSixDirectStrictRepresentedCarrier C index).card =
      (sectionSixDirectStrictCofactorCarrier C index).card := by
  simp [sectionSixDirectStrictRepresentedCarrier]

/-- On an accepted index, the PNat key is the literal product `d*q`. -/
theorem sectionSixDirectStrictKey_eq
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    sectionSixDirectStrictKey index =
      primeTupleProduct index.1 * index.2 := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  have hpositive :=
    primeTupleProduct_pos_of_mem_propositionSixOnePrimeTuples htuple
  have hprime := (mem_sievePrimeInterval.mp hindexData.2).1
  unfold sectionSixDirectStrictKey sectionSixDirectStrictModulus
  simp [hpositive, hprime.pos]

private theorem directStrict_accepted_prime
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    ∀ i, (index.1 i).Prime := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  exact (mem_propositionSixOnePrimeTuples.mp htuple).2.1

private theorem directStrict_accepted_monotone
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    Monotone index.1 := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  exact (mem_propositionSixOnePrimeTuples.mp htuple).2.2.1

private theorem directStrict_accepted_coordinate_lower
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    ∀ i, (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) ≤
      (index.1 i : Real) := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  exact (mem_propositionSixOnePrimeTuples.mp htuple).2.2.2.1

private theorem directStrict_augmented_prime
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    ∀ i, (Matrix.vecCons index.2 index.1 i).Prime := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have hprimeQ := (mem_sievePrimeInterval.mp hindexData.2).1
  have hprimeP := directStrict_accepted_prime hindex
  intro i
  refine Fin.cases hprimeQ ?_ i
  intro j
  exact hprimeP j

private theorem directStrict_augmented_monotone
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    Monotone (Matrix.vecCons index.2 index.1) := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have hqUpper := (mem_sievePrimeInterval.mp hindexData.2).2.2
  have hcoord := directStrict_accepted_coordinate_lower hindex
  have hqLe : ∀ i, index.2 ≤ index.1 i := by
    intro i
    exact_mod_cast (hqUpper.trans (hcoord i))
  have hPmono := directStrict_accepted_monotone hindex
  cases ell with
  | zero =>
      intro i j _hij
      have hij : i = j := Subsingleton.elim _ _
      subst j
      exact le_rfl
  | succ n =>
      exact hPmono.vecCons (hqLe 0)

/-- Complete `d*q` keys determine accepted direct strict indices, including
ties between `q` and the first outer coordinate. -/
theorem sectionSixDirectStrictKey_injOn
    (epsilon delta : Real) (ell length : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand) :
    Set.InjOn sectionSixDirectStrictKey
      (sectionSixDirectRepeatedIndices epsilon delta ell region length band :
        Set (SectionSixDirectStrictIndex ell)) := by
  intro i hi j hj hkey
  rcases i with ⟨p, q⟩
  rcases j with ⟨r, s⟩
  have hkeyP := sectionSixDirectStrictKey_eq hi
  have hkeyR := sectionSixDirectStrictKey_eq hj
  rw [hkeyP, hkeyR] at hkey
  have hproduct :
      primeTupleProduct (Matrix.vecCons q p) =
        primeTupleProduct (Matrix.vecCons s r) := by
    simpa [primeTupleProduct, Fin.prod_univ_succ, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using hkey
  have htuple := eq_of_monotone_primeTupleProduct_eq
    (directStrict_augmented_prime hi)
    (directStrict_augmented_prime hj)
    (directStrict_augmented_monotone hi)
    (directStrict_augmented_monotone hj)
    hproduct
  have hq : q = s := by
    have h := congrFun htuple (0 : Fin (ell + 1))
    simpa using h
  have hp : p = r := by
    funext k
    have h := congrFun htuple (Fin.succ k)
    simpa using h
  exact Prod.ext hp hq

end

end PrimesRestrictedDigits
