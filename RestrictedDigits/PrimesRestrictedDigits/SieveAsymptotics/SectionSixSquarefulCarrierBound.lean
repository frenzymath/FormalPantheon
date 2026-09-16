import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedIncidenceAggregate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedSquareTail
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Positive squareful Section 6 carriers

This file supplies the elementary ambient cardinality bound needed after the variable-modulus
incidence theorem. The interval is the literal source interval `(y,z]`; the positive filter
removes the ambient zero before the quotient count. and proof record
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The positive members of a finite carrier divisible by a given square. -/
noncomputable def sectionSixPositiveSquareProgression
    (C : Finset Nat) (q : Nat) : Finset Nat :=
  C.filter fun n => 0 < n ∧ q * q ∣ n

@[simp] theorem mem_sectionSixPositiveSquareProgression
    {C : Finset Nat} {q n : Nat} :
    n ∈ sectionSixPositiveSquareProgression C q ↔
      n ∈ C ∧ 0 < n ∧ q * q ∣ n := by
  simp [sectionSixPositiveSquareProgression]

/--
The direct squareful filter is the union of its square progressions. No disjointness of
different prime-square progressions is asserted.
-/
theorem sectionSixRepeatedSquarefulCarrier_eq_biUnion
    (C : Finset Nat) (X delta theta : Real) :
    sectionSixRepeatedSquarefulCarrier C X delta theta =
      (sievePrimeInterval (X ^ delta) (X ^ theta)).biUnion
        (sectionSixPositiveSquareProgression C) := by
  classical
  ext n
  simp only [mem_sectionSixRepeatedSquarefulCarrier, Finset.mem_biUnion,
    mem_sectionSixPositiveSquareProgression]
  constructor
  · rintro ⟨hnC, hnPos, q, hq, hqSq⟩
    exact ⟨q, hq, hnC, hnPos, hqSq⟩
  · rintro ⟨q, hq, hnC, hnPos, hqSq⟩
    exact ⟨hnC, hnPos, q, hq, hqSq⟩

/-- Squareful subcarriers are monotone in the underlying finite carrier. -/
theorem sectionSixRepeatedSquarefulCarrier_mono
    {C B : Finset Nat} (hCB : C ⊆ B) (X delta theta : Real) :
    sectionSixRepeatedSquarefulCarrier C X delta theta ⊆
      sectionSixRepeatedSquarefulCarrier B X delta theta := by
  intro n hn
  have hnData := mem_sectionSixRepeatedSquarefulCarrier.mp hn
  exact mem_sectionSixRepeatedSquarefulCarrier.mpr
    ⟨hCB hnData.1, hnData.2⟩

/-- One positive square progression below a decimal power has at most
`X/q^2` elements.  The strict ambient endpoint is handled by `X-1`. -/
theorem card_sectionSixPositiveSquareProgression_maynardAmbient_le
    (length : Nat) {q : Nat} (hq : q.Prime) :
    ((sectionSixPositiveSquareProgression
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) q).card : Real) ≤
      ((10 ^ length : Nat) : Real) / (q : Real) ^ (2 : Nat) := by
  classical
  let XNat : Nat := 10 ^ length
  let qSq : Nat := q * q
  let upper : Nat := (XNat - 1) / qSq
  let quotient : Nat → Nat := fun n => n / qSq
  have hqSqPos : 0 < qSq := by
    dsimp only [qSq]
    exact Nat.mul_pos hq.pos hq.pos
  have hmaps : Set.MapsTo quotient
      (sectionSixPositiveSquareProgression
        (maynardAmbientCarrier (XNat : Real)) q : Set Nat)
      (Finset.Icc 1 upper : Set Nat) := by
    intro n hn
    have hnData := mem_sectionSixPositiveSquareProgression.mp hn
    have hnX : n < XNat := by
      exact_mod_cast (mem_maynardAmbientCarrier.mp hnData.1)
    have hnPred : n ≤ XNat - 1 := Nat.le_sub_one_of_lt hnX
    have hqSqDvd : qSq ∣ n := by
      simpa only [qSq] using hnData.2.2
    have hqSqLe : qSq ≤ n := Nat.le_of_dvd hnData.2.1 hqSqDvd
    have hlower : 1 ≤ quotient n := by
      dsimp only [quotient]
      exact (Nat.le_div_iff_mul_le hqSqPos).2 (by simpa using hqSqLe)
    have hupper : quotient n ≤ upper := by
      dsimp only [quotient, upper]
      exact Nat.div_le_div_right hnPred
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  have hinj : Set.InjOn quotient
      (sectionSixPositiveSquareProgression
        (maynardAmbientCarrier (XNat : Real)) q : Set Nat) := by
    intro a ha b hb hab
    have haDvd : qSq ∣ a := by
      simpa only [qSq] using
        (mem_sectionSixPositiveSquareProgression.mp ha).2.2
    have hbDvd : qSq ∣ b := by
      simpa only [qSq] using
        (mem_sectionSixPositiveSquareProgression.mp hb).2.2
    calc
      a = quotient a * qSq := by
        dsimp only [quotient]
        exact (Nat.div_mul_cancel haDvd).symm
      _ = quotient b * qSq := by rw [hab]
      _ = b := by
        dsimp only [quotient]
        exact Nat.div_mul_cancel hbDvd
  have hcard :
      (sectionSixPositiveSquareProgression
          (maynardAmbientCarrier (XNat : Real)) q).card ≤
        (Finset.Icc 1 upper).card :=
    Finset.card_le_card_of_injOn quotient hmaps hinj
  rw [Nat.card_Icc] at hcard
  have hcardUpper :
      (sectionSixPositiveSquareProgression
          (maynardAmbientCarrier (XNat : Real)) q).card ≤ upper := by
    simpa only [Nat.add_sub_cancel] using hcard
  have hupperDiv : upper ≤ XNat / qSq := by
    dsimp only [upper]
    exact Nat.div_le_div_right (Nat.sub_le XNat 1)
  have hcast :
      ((sectionSixPositiveSquareProgression
          (maynardAmbientCarrier (XNat : Real)) q).card : Real) ≤
        ((XNat / qSq : Nat) : Real) := by
    exact_mod_cast hcardUpper.trans hupperDiv
  calc
    ((sectionSixPositiveSquareProgression
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) q).card : Real) =
        ((sectionSixPositiveSquareProgression
          (maynardAmbientCarrier (XNat : Real)) q).card : Real) := by
      rfl
    _ ≤ ((XNat / qSq : Nat) : Real) := hcast
    _ ≤ (XNat : Real) / (qSq : Real) := Nat.cast_div_le
    _ = ((10 ^ length : Nat) : Real) / (q : Real) ^ (2 : Nat) := by
      simp only [XNat, qSq, Nat.cast_mul, pow_two]

/-- The positive large-prime-square subset of the decimal ambient has
cardinality at most `2*X/X^delta`. -/
theorem card_sectionSixRepeatedSquarefulCarrier_maynardAmbient_le
    (length : Nat) {delta theta : Real}
    (hy : 2 ≤ ((10 ^ length : Nat) : Real) ^ delta) :
    ((sectionSixRepeatedSquarefulCarrier
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
        ((10 ^ length : Nat) : Real) delta theta).card : Real) ≤
      2 * ((10 ^ length : Nat) : Real) /
        (((10 ^ length : Nat) : Real) ^ delta) := by
  classical
  let X : Real := ((10 ^ length : Nat) : Real)
  let P : Finset Nat := sievePrimeInterval (X ^ delta) (X ^ theta)
  rw [sectionSixRepeatedSquarefulCarrier_eq_biUnion]
  have hcardNat :
      (P.biUnion (sectionSixPositiveSquareProgression
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real)))).card ≤
        ∑ q ∈ P,
          (sectionSixPositiveSquareProgression
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) q).card := by
    exact Finset.card_biUnion_le
  have hcardReal :
      ((P.biUnion (sectionSixPositiveSquareProgression
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real)))).card : Real) ≤
        ∑ q ∈ P,
          ((sectionSixPositiveSquareProgression
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) q).card : Real) := by
    exact_mod_cast hcardNat
  calc
    ((P.biUnion (sectionSixPositiveSquareProgression
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real)))).card : Real) ≤
        ∑ q ∈ P,
          ((sectionSixPositiveSquareProgression
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) q).card : Real) :=
      hcardReal
    _ ≤ ∑ q ∈ P, X / (q : Real) ^ (2 : Nat) := by
      apply Finset.sum_le_sum
      intro q hq
      exact card_sectionSixPositiveSquareProgression_maynardAmbient_le length
        (mem_sievePrimeInterval.mp hq).1
    _ = X * (∑ q ∈ P, 1 / (q : Real) ^ (2 : Nat)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ X * (2 / (X ^ delta)) := by
      gcongr
      exact sum_reciprocal_square_sievePrimeInterval_le hy
    _ = 2 * ((10 ^ length : Nat) : Real) /
        (((10 ^ length : Nat) : Real) ^ delta) := by
      dsimp only [X]
      ring

/-- Any subcarrier of the decimal ambient satisfies the same squareful bound. -/
theorem card_sectionSixRepeatedSquarefulCarrier_le
    (length : Nat) {delta theta : Real} (C : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 2 ≤ ((10 ^ length : Nat) : Real) ^ delta) :
    ((sectionSixRepeatedSquarefulCarrier C
        ((10 ^ length : Nat) : Real) delta theta).card : Real) ≤
      2 * ((10 ^ length : Nat) : Real) /
        (((10 ^ length : Nat) : Real) ^ delta) := by
  have hcard := Finset.card_le_card
    (sectionSixRepeatedSquarefulCarrier_mono hC
      ((10 ^ length : Nat) : Real) delta theta)
  have hcardReal :
      ((sectionSixRepeatedSquarefulCarrier C
          ((10 ^ length : Nat) : Real) delta theta).card : Real) ≤
        ((sectionSixRepeatedSquarefulCarrier
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
          ((10 ^ length : Nat) : Real) delta theta).card : Real) := by
    exact_mod_cast hcard
  exact hcardReal.trans
    (card_sectionSixRepeatedSquarefulCarrier_maynardAmbient_le length hy)

end

end PrimesRestrictedDigits
