import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLedger

/-!
# First-ledger repeated-prime carriers

This file gives the exact represented carrier and dependent finite index for the
repeated-prime terms retained by the corrected first Section 6 ledger.

Source: MAYNARD-PRD-PUBLISHED, Section 6, pp. 139--140, Eq. (6.5).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The complete positive modulus for a weak repeated-prime term. -/
def sectionSixFirstRepeatedModulus (d : PNat) (q : Nat) : PNat :=
  (d * Nat.toPNat' q) * Nat.toPNat' q

/-- The natural complete-modulus key used for divisor incidence. -/
def sectionSixFirstRepeatedKey (d : PNat) (q : Nat) : Nat :=
  (sectionSixFirstRepeatedModulus d q : Nat)

/-- Multiplication by the complete repeated-prime modulus. -/
def sectionSixFirstRepeatedRepresentedEmbedding
    (d : PNat) (q : Nat) : Nat ↪ Nat :=
  { toFun := fun m => m * sectionSixFirstRepeatedKey d q
    inj' := mul_left_injective₀
      (PNat.ne_zero (sectionSixFirstRepeatedModulus d q)) }

/-- The represented integer image of one weak repeated-prime cofactor
carrier. -/
noncomputable def sectionSixFirstRepeatedRepresentedCarrier
    (C : Finset Nat) (d : PNat) (q : Nat) : Finset Nat :=
  (weakSiftedCarrier
      (sieveDilation C (sectionSixFirstRepeatedModulus d q))
      (q : Real)).map
    (sectionSixFirstRepeatedRepresentedEmbedding d q)

@[simp] theorem mem_sectionSixFirstRepeatedRepresentedCarrier
    {C : Finset Nat} {d : PNat} {q n : Nat} :
    n ∈ sectionSixFirstRepeatedRepresentedCarrier C d q ↔
      ∃ m ∈ weakSiftedCarrier
          (sieveDilation C (sectionSixFirstRepeatedModulus d q))
          (q : Real),
        m * sectionSixFirstRepeatedKey d q = n := by
  simp [sectionSixFirstRepeatedRepresentedCarrier,
    sectionSixFirstRepeatedRepresentedEmbedding]

theorem card_sectionSixFirstRepeatedRepresentedCarrier_eq
    (C : Finset Nat) (d : PNat) (q : Nat) :
    (sectionSixFirstRepeatedRepresentedCarrier C d q).card =
      (weakSiftedCarrier
        (sieveDilation C (sectionSixFirstRepeatedModulus d q))
        (q : Real)).card := by
  simp [sectionSixFirstRepeatedRepresentedCarrier]

/-- At a prime source index, the total PNat construction is the literal
natural product d*q^2. -/
theorem sectionSixFirstRepeatedKey_eq
    (d : PNat) {q : Nat} (hq : q.Prime) :
    sectionSixFirstRepeatedKey d q = (d : Nat) * q * q := by
  unfold sectionSixFirstRepeatedKey sectionSixFirstRepeatedModulus
  rw [PNat.mul_coe, PNat.mul_coe, Nat.toPNat'_coe, if_pos hq.pos]

/-- Exact cardinality discrepancy represented by one repeated-prime term. -/
theorem sectionSixRepeatedPrimeTerm_eq_firstRepeatedCardDiscrepancy
    (digit : Fin 10) (length : Nat) (d : PNat)
    {q : Nat} (hq : q.Prime) :
    sectionSixRepeatedPrimeTerm digit length d q =
      ((sectionSixFirstRepeatedRepresentedCarrier
        (paddedRestrictedNumbers digit length) d q).card : Real) -
      (restrictedDigitDensity digit : Real) *
          (((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
        ((sectionSixFirstRepeatedRepresentedCarrier
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
          d q).card : Real) := by
  rw [sectionSixRepeatedPrimeTerm_eq_weakSiftedSum digit length d hq,
    sectionSixWeakSiftedSum_eq_card_sub_density_mul_card]
  change
    ((weakSiftedCarrier
      (sieveDilation (paddedRestrictedNumbers digit length)
        (sectionSixFirstRepeatedModulus d q)) (q : Real)).card : Real) -
      (restrictedDigitDensity digit : Real) *
          (((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
        ((weakSiftedCarrier
          (sieveDilation
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
            (sectionSixFirstRepeatedModulus d q)) (q : Real)).card : Real) =
      _
  rw [← card_sectionSixFirstRepeatedRepresentedCarrier_eq
      (paddedRestrictedNumbers digit length) d q,
    ← card_sectionSixFirstRepeatedRepresentedCarrier_eq
      (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) d q]

/-- A dependent pair of an outer prime and its repeated inner prime. -/
abbrev SectionSixFirstSecondRepeatedIndex :=
  Sigma fun _ : Nat => Nat

/-- The exact dependent index set of one nested repeated-prime ledger sum. -/
noncomputable def sectionSixFirstSecondRepeatedIndices
    (length : Nat) (z a b : Real) :
    Finset SectionSixFirstSecondRepeatedIndex :=
  (sievePrimeInterval a b).sigma fun p =>
    sievePrimeInterval z (sectionSixFirstFactorThreshold length p)

@[simp] theorem mem_sectionSixFirstSecondRepeatedIndices
    {length : Nat} {z a b : Real}
    {index : SectionSixFirstSecondRepeatedIndex} :
    index ∈ sectionSixFirstSecondRepeatedIndices length z a b ↔
      index.1 ∈ sievePrimeInterval a b ∧
      index.2 ∈ sievePrimeInterval z
        (sectionSixFirstFactorThreshold length index.1) := by
  classical
  simp [sectionSixFirstSecondRepeatedIndices]

/-- Reindex the existing nested ledger sum by its dependent pair index. -/
theorem sectionSixFirstSecondRepeatedSum_eq_indexSum
    (digit : Fin 10) (length : Nat) (z a b : Real) :
    sectionSixFirstSecondRepeatedSum digit length z a b =
      ∑ index ∈ sectionSixFirstSecondRepeatedIndices length z a b,
        sectionSixRepeatedPrimeTerm digit length
          (Nat.toPNat' index.1) index.2 := by
  unfold sectionSixFirstSecondRepeatedSum
    sectionSixFirstSecondRepeatedIndices
  rw [Finset.sum_sigma']

end

end PrimesRestrictedDigits
