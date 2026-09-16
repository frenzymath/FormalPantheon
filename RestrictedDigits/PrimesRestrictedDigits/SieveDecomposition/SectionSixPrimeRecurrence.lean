import PrimesRestrictedDigits.SieveDecomposition.RepeatedPrimeRecurrence
import PrimesRestrictedDigits.SieveDecomposition.SectionSixWeight

/-!
# Section 6 specialized prime recurrence

This specializes the exact outer repeated-prime recurrence to Maynard's Section 6 weight. The
second term is weakly sifted after two copies of the outer prime; it is retained rather than
silently discarded.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 136--143 and 156--158.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The strict once-dilated prime term for the decimal Section 6 weight. -/
def sectionSixStrictPrimeTerm
    (digit : Fin 10) (length : Nat) (d : PNat) (p : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  strictPrimeBuchstabTerm (sieveDilation B d) p
    (fun n => sectionSixWeight A B lambda (n * (d : Nat)))

/-- The weak twice-dilated repeated-prime term for the decimal Section 6
weight. -/
def sectionSixRepeatedPrimeTerm
    (digit : Fin 10) (length : Nat) (d : PNat) (p : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  repeatedPrimeBuchstabTerm (sieveDilation B d) p
    (fun n => sectionSixWeight A B lambda (n * (d : Nat)))

theorem sectionSixStrictPrimeTerm_eq_siftedSum
    (digit : Fin 10) (length : Nat) (d : PNat)
    {p : Nat} (hp : p.Prime) :
    sectionSixStrictPrimeTerm digit length d p =
      sectionSixSiftedSum digit length (d * Nat.toPNat' p) (p : Real) := by
  unfold sectionSixStrictPrimeTerm sectionSixSiftedSum
  unfold strictPrimeBuchstabTerm
  simp only [sieveDilation_mul]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [PNat.mul_coe]
  rw [Nat.toPNat'_coe, if_pos hp.pos]
  ring_nf

theorem sectionSixRepeatedPrimeTerm_eq_weakSiftedSum
    (digit : Fin 10) (length : Nat) (d : PNat)
    {p : Nat} (hp : p.Prime) :
    sectionSixRepeatedPrimeTerm digit length d p =
      sectionSixWeakSiftedSum digit length
        ((d * Nat.toPNat' p) * Nat.toPNat' p) (p : Real) := by
  unfold sectionSixRepeatedPrimeTerm sectionSixWeakSiftedSum
  unfold repeatedPrimeBuchstabTerm
  simp only [sieveDilation_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [PNat.mul_coe]
  rw [Nat.toPNat'_coe, if_pos hp.pos]
  ring_nf

/-- Exact Section 6 recurrence, including the repeated-prime correction. -/
theorem sectionSixSiftedSum_eq_sub_strict_sub_repeated
    (digit : Fin 10) (length : Nat) (d : PNat)
    {z1 z2 : Real} (hz : z1 ≤ z2) :
    sectionSixSiftedSum digit length d z2 =
      sectionSixSiftedSum digit length d z1 -
          (∑ p ∈ sievePrimeInterval z1 z2,
            sectionSixStrictPrimeTerm digit length d p) -
        ∑ p ∈ sievePrimeInterval z1 z2,
          sectionSixRepeatedPrimeTerm digit length d p := by
  unfold sectionSixSiftedSum
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  have h := sum_strictSiftedCarrier_eq_sub_strict_sub_repeated
    (sieveDilation B d) hz
    (fun n => sectionSixWeight A B lambda (n * (d : Nat)))
  have hstrict :
      (∑ p ∈ sievePrimeInterval z1 z2,
        strictPrimeBuchstabTerm (sieveDilation B d) p
          (fun n => sectionSixWeight A B lambda (n * (d : Nat)))) =
        ∑ p ∈ sievePrimeInterval z1 z2,
          sectionSixStrictPrimeTerm digit length d p := by
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [sectionSixStrictPrimeTerm]
  have hrep :
      (∑ p ∈ sievePrimeInterval z1 z2,
        repeatedPrimeBuchstabTerm (sieveDilation B d) p
          (fun n => sectionSixWeight A B lambda (n * (d : Nat)))) =
        ∑ p ∈ sievePrimeInterval z1 z2,
          sectionSixRepeatedPrimeTerm digit length d p := by
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [sectionSixRepeatedPrimeTerm]
  change
    (∑ n ∈ strictSiftedCarrier (sieveDilation B d) z2,
      sectionSixWeight A B lambda (n * (d : Nat))) = _
  calc
    _ = (∑ n ∈ strictSiftedCarrier (sieveDilation B d) z1,
        sectionSixWeight A B lambda (n * (d : Nat))) -
          (∑ p ∈ sievePrimeInterval z1 z2,
            strictPrimeBuchstabTerm (sieveDilation B d) p
              (fun n => sectionSixWeight A B lambda (n * (d : Nat)))) -
        ∑ p ∈ sievePrimeInterval z1 z2,
          repeatedPrimeBuchstabTerm (sieveDilation B d) p
            (fun n => sectionSixWeight A B lambda (n * (d : Nat))) := h
    _ = sectionSixSiftedSum digit length d z1 -
          (∑ p ∈ sievePrimeInterval z1 z2,
            sectionSixStrictPrimeTerm digit length d p) -
        ∑ p ∈ sievePrimeInterval z1 z2,
          sectionSixRepeatedPrimeTerm digit length d p := by
      rw [hstrict, hrep]
      rfl

end

end PrimesRestrictedDigits
