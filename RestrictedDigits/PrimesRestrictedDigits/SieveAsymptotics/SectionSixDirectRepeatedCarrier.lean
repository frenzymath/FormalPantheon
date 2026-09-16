import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectRangeRecurrence
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.NormNum

/-!
# Exact carriers for direct repeated Section 6 terms

The corrected direct recurrence is indexed by an outer prime tuple and its continuation prime.
The complete modulus `d*q^2` is retained as the finite incidence key; later Type-I estimates
charge only the square `q^2`.
-/

namespace PrimesRestrictedDigits

noncomputable section

open scoped BigOperators

/-- A direct repeated index consists of an accepted outer tuple and one
continuation prime. -/
abbrev SectionSixDirectRepeatedIndex (ell : Nat) :=
  (Fin ell -> Nat) × Nat

/-- The exact finite index set for one closed direct band. -/
noncomputable def sectionSixDirectRepeatedIndices
    (epsilon delta : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) :
    Finset (SectionSixDirectRepeatedIndex ell) := by
  classical
  exact (sectionSixDirectRangePrimeTuples epsilon ell region length band).product
    (sievePrimeInterval
      (((10 ^ length : Nat) : Real) ^ delta)
      (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon))

@[simp] theorem mem_sectionSixDirectRepeatedIndices
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell} :
    index ∈ sectionSixDirectRepeatedIndices epsilon delta ell region length band ↔
      index.1 ∈ sectionSixDirectRangePrimeTuples
        epsilon ell region length band ∧
      index.2 ∈ sievePrimeInterval
        (((10 ^ length : Nat) : Real) ^ delta)
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) := by
  classical
  simp [sectionSixDirectRepeatedIndices]

/-- The complete positive modulus attached to a direct repeated index. -/
def sectionSixDirectRepeatedModulus
    {ell : Nat} (index : SectionSixDirectRepeatedIndex ell) : PNat :=
  (((primeTupleProduct index.1).toPNat' * Nat.toPNat' index.2) *
    Nat.toPNat' index.2)

/-- The natural key used for divisor incidence. -/
def sectionSixDirectRepeatedKey
    {ell : Nat} (index : SectionSixDirectRepeatedIndex ell) : Nat :=
  (sectionSixDirectRepeatedModulus index : Nat)

/-- Multiplication by the complete positive modulus. -/
def sectionSixDirectRepeatedRepresentedEmbedding
    {ell : Nat} (index : SectionSixDirectRepeatedIndex ell) : Nat ↪ Nat :=
  { toFun := fun m => m * sectionSixDirectRepeatedKey index
    inj' := mul_left_injective₀
      (PNat.ne_zero (sectionSixDirectRepeatedModulus index)) }

/-- The weakly sifted cofactor carrier before multiplication by the complete
modulus. -/
noncomputable def sectionSixDirectRepeatedCofactorCarrier
    (C : Finset Nat) {ell : Nat}
    (index : SectionSixDirectRepeatedIndex ell) : Finset Nat :=
  weakSiftedCarrier
    (sieveDilation C (sectionSixDirectRepeatedModulus index))
    (index.2 : Real)

/-- The represented integer carrier for one direct repeated index. -/
noncomputable def sectionSixDirectRepeatedRepresentedCarrier
    (C : Finset Nat) {ell : Nat}
    (index : SectionSixDirectRepeatedIndex ell) : Finset Nat :=
  (sectionSixDirectRepeatedCofactorCarrier C index).map
    (sectionSixDirectRepeatedRepresentedEmbedding index)

@[simp] theorem mem_sectionSixDirectRepeatedRepresentedCarrier
    {C : Finset Nat} {ell n : Nat}
    {index : SectionSixDirectRepeatedIndex ell} :
    n ∈ sectionSixDirectRepeatedRepresentedCarrier C index ↔
      ∃ m ∈ sectionSixDirectRepeatedCofactorCarrier C index,
        m * sectionSixDirectRepeatedKey index = n := by
  simp [sectionSixDirectRepeatedRepresentedCarrier,
    sectionSixDirectRepeatedRepresentedEmbedding]

theorem card_sectionSixDirectRepeatedRepresentedCarrier_eq
    {C : Finset Nat} {ell : Nat}
    (index : SectionSixDirectRepeatedIndex ell) :
    (sectionSixDirectRepeatedRepresentedCarrier C index).card =
      (sectionSixDirectRepeatedCofactorCarrier C index).card := by
  simp [sectionSixDirectRepeatedRepresentedCarrier]

/-- On an accepted index, the PNat key has its literal complete-product value.
This normalization is the bridge to the sorted augmented prime tuple. -/
theorem sectionSixDirectRepeatedKey_eq
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    sectionSixDirectRepeatedKey index =
      primeTupleProduct index.1 * index.2 * index.2 := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  have hpositive := primeTupleProduct_pos_of_mem_propositionSixOnePrimeTuples htuple
  have hprime := (mem_sievePrimeInterval.mp hindexData.2).1
  unfold sectionSixDirectRepeatedKey sectionSixDirectRepeatedModulus
  simp [hpositive, hprime.pos]

private theorem directRepeated_accepted_prime
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    ∀ i, (index.1 i).Prime := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  exact (mem_propositionSixOnePrimeTuples.mp htuple).2.1

private theorem directRepeated_accepted_monotone
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    Monotone index.1 := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  exact (mem_propositionSixOnePrimeTuples.mp htuple).2.2.1

private theorem directRepeated_accepted_coordinate_lower
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    ∀ i, (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) ≤
      (index.1 i : Real) := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  exact (mem_propositionSixOnePrimeTuples.mp htuple).2.2.2.1

private theorem directRepeated_augmented_prime
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    ∀ i, (Matrix.vecCons index.2 (Matrix.vecCons index.2 index.1) i).Prime := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have hprimeQ := (mem_sievePrimeInterval.mp hindexData.2).1
  have hprimeP := directRepeated_accepted_prime hindex
  intro i
  refine Fin.cases ?_ ?_ i
  · exact hprimeQ
  · intro j
    refine Fin.cases ?_ ?_ j
    · exact hprimeQ
    · intro k
      exact hprimeP k

private theorem directRepeated_augmented_monotone
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    Monotone (Matrix.vecCons index.2 (Matrix.vecCons index.2 index.1)) := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have hqUpper := (mem_sievePrimeInterval.mp hindexData.2).2.2
  have hcoord := directRepeated_accepted_coordinate_lower hindex
  have hqLe : ∀ i, index.2 ≤ index.1 i := by
    intro i
    exact_mod_cast (hqUpper.trans (hcoord i))
  have hPmono := directRepeated_accepted_monotone hindex
  have hinner : Monotone (Matrix.vecCons index.2 index.1) := by
    cases ell with
    | zero =>
        intro i j _hij
        have hij : i = j := Subsingleton.elim _ _
        subst j
        exact le_rfl
    | succ n =>
        exact hPmono.vecCons (hqLe 0)
  exact hinner.vecCons le_rfl

theorem sectionSixDirectRepeatedKey_injOn
    (epsilon delta : Real) (ell length : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand) :
    Set.InjOn sectionSixDirectRepeatedKey
      (sectionSixDirectRepeatedIndices epsilon delta ell region length band :
        Set (SectionSixDirectRepeatedIndex ell)) := by
  intro i hi j hj hkey
  rcases i with ⟨p, q⟩
  rcases j with ⟨r, s⟩
  have hkeyP := sectionSixDirectRepeatedKey_eq hi
  have hkeyR := sectionSixDirectRepeatedKey_eq hj
  rw [hkeyP, hkeyR] at hkey
  have hproduct :
      primeTupleProduct (Matrix.vecCons q (Matrix.vecCons q p)) =
        primeTupleProduct (Matrix.vecCons s (Matrix.vecCons s r)) := by
    simpa [primeTupleProduct, Fin.prod_univ_succ, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using hkey
  have htuple := eq_of_monotone_primeTupleProduct_eq
    (directRepeated_augmented_prime hi)
    (directRepeated_augmented_prime hj)
    (directRepeated_augmented_monotone hi)
    (directRepeated_augmented_monotone hj)
    hproduct
  have hq : q = s := by
    have h := congrFun htuple (0 : Fin (ell + 2))
    simpa using h
  have hp : p = r := by
    funext k
    have h := congrFun htuple (Fin.succ (Fin.succ k))
    simpa using h
  exact Prod.ext hp hq

end

end PrimesRestrictedDigits
