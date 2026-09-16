import PrimesRestrictedDigits.Digits.LocalDensity
import PrimesRestrictedDigits.SieveDecomposition.Definitions

/-!
# Section 6 weighted sifted carriers

This file implements the finite weighted sequence and the exact strict and weak carrier
identities underlying Maynard's equations (6.1)--(6.2).

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 136--137, equations (6.1)--(6.2);
`MAYNARD-PRD-ARXIV-V2`, `Digits.tex` lines 416 and 424--443.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The total Section 6 indicator weight on the natural numbers. -/
def sectionSixWeight
    (A B : Finset Nat) (lambda : Real) (n : Nat) : Real :=
  (if n ∈ A then 1 else 0) - lambda * (if n ∈ B then 1 else 0)

theorem sectionSixWeight_of_mem_ambient
    (A B : Finset Nat) (lambda : Real) {n : Nat} (hn : n ∈ B) :
    sectionSixWeight A B lambda n =
      (if n ∈ A then 1 else 0) - lambda := by
  simp [sectionSixWeight, hn]

theorem sectionSixWeight_eq_zero_of_not_mem_ambient
    (A B : Finset Nat) (lambda : Real) {n : Nat}
    (hAB : A ⊆ B) (hn : n ∉ B) :
    sectionSixWeight A B lambda n = 0 := by
  have hnA : n ∉ A := fun hnA => hn (hAB hnA)
  simp [sectionSixWeight, hnA, hn]

theorem paddedRestrictedNumbers_subset_maynardAmbientCarrier
    (digit : Fin 10) (length : Nat) :
    paddedRestrictedNumbers digit length ⊆
      maynardAmbientCarrier ((10 ^ length : Nat) : Real) := by
  intro n hn
  rw [mem_maynardAmbientCarrier]
  exact_mod_cast (mem_paddedRestrictedNumbers.mp hn).1

theorem sectionSix_lt_div_iff_mul_lt
    (m : Nat) (d : PNat) (X : Real) :
    (m : Real) < X / ((d : Nat) : Real) ↔
      (((m * (d : Nat) : Nat) : Real) < X) := by
  rw [lt_div_iff₀ (by exact_mod_cast d.2), Nat.cast_mul]

theorem sectionSix_card_maynardAmbientCarrier_powTen (length : Nat) :
    ((maynardAmbientCarrier ((10 ^ length : Nat) : Real)).card : Real) =
      ((10 ^ length : Nat) : Real) := by
  have hcarrier :
      maynardAmbientCarrier ((10 ^ length : Nat) : Real) =
        Finset.range (10 ^ length) := by
    ext n
    rw [mem_maynardAmbientCarrier, Finset.mem_range]
    exact_mod_cast (show n < 10 ^ length ↔ n < 10 ^ length from Iff.rfl)
  rw [hcarrier, Finset.card_range]

theorem zero_mem_strictSiftedCarrier_sieveDilation
    (B : Finset Nat) (d : PNat) (z : Real) :
    0 ∈ strictSiftedCarrier (sieveDilation B d) z ↔
      0 ∈ B ∧ z < 2 := by
  rw [zero_mem_strictSiftedCarrier, zero_mem_sieveDilation]

theorem zero_mem_weakSiftedCarrier_sieveDilation
    (B : Finset Nat) (d : PNat) (z : Real) :
    0 ∈ weakSiftedCarrier (sieveDilation B d) z ↔
      0 ∈ B ∧ z ≤ 2 := by
  rw [zero_mem_weakSiftedCarrier, zero_mem_sieveDilation]

private theorem sectionSixFilteredSum_bridge
    (A B : Finset Nat) (hAB : A ⊆ B) (lambda : Real) (d : PNat)
    (rough : Nat → Prop) [DecidablePred rough] :
    (∑ m ∈ (sieveDilation B d).filter rough,
      sectionSixWeight A B lambda (m * (d : Nat))) =
      (((sieveDilation A d).filter rough).card : Real) -
        lambda * (((sieveDilation B d).filter rough).card : Real) := by
  classical
  have hrestricted :
      ((sieveDilation B d).filter rough).filter
          (fun m => m * (d : Nat) ∈ A) =
        (sieveDilation A d).filter rough := by
    ext m
    simp only [Finset.mem_filter, mem_sieveDilation]
    constructor
    · rintro ⟨⟨_hmB, hmRough⟩, hmA⟩
      exact ⟨hmA, hmRough⟩
    · rintro ⟨hmA, hmRough⟩
      exact ⟨⟨hAB hmA, hmRough⟩, hmA⟩
  have hambient :
      ((sieveDilation B d).filter rough).filter
          (fun m => m * (d : Nat) ∈ B) =
        (sieveDilation B d).filter rough := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    exact mem_sieveDilation.mp (Finset.mem_filter.mp hm).1
  simp only [sectionSixWeight]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_boole, hrestricted, hambient]

theorem sectionSixStrictSum_bridge
    (A B : Finset Nat) (hAB : A ⊆ B) (lambda : Real)
    (d : PNat) (z : Real) :
    (∑ m ∈ strictSiftedCarrier (sieveDilation B d) z,
      sectionSixWeight A B lambda (m * (d : Nat))) =
      ((strictSiftedCarrier (sieveDilation A d) z).card : Real) -
        lambda *
          ((strictSiftedCarrier (sieveDilation B d) z).card : Real) := by
  classical
  simpa only [strictSiftedCarrier] using
    sectionSixFilteredSum_bridge A B hAB lambda d (strictRoughPredicate z)

theorem sectionSixWeakSum_bridge
    (A B : Finset Nat) (hAB : A ⊆ B) (lambda : Real)
    (d : PNat) (z : Real) :
    (∑ m ∈ weakSiftedCarrier (sieveDilation B d) z,
      sectionSixWeight A B lambda (m * (d : Nat))) =
      ((weakSiftedCarrier (sieveDilation A d) z).card : Real) -
        lambda *
          ((weakSiftedCarrier (sieveDilation B d) z).card : Real) := by
  classical
  simpa only [weakSiftedCarrier] using
    sectionSixFilteredSum_bridge A B hAB lambda d (weakRoughPredicate z)

/-- Maynard's strict `S_d(z)` at a fixed decimal length. -/
noncomputable def sectionSixSiftedSum
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  ∑ m ∈ strictSiftedCarrier (sieveDilation B d) z,
    sectionSixWeight A B lambda (m * (d : Nat))

/-- The weak-threshold decimal companion used by exact prime fibers. -/
noncomputable def sectionSixWeakSiftedSum
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  ∑ m ∈ weakSiftedCarrier (sieveDilation B d) z,
    sectionSixWeight A B lambda (m * (d : Nat))

theorem sectionSixSiftedSum_eq_card_sub_density_mul_card
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) :
    sectionSixSiftedSum digit length d z =
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d) z).card : Real) -
        ((restrictedDigitDensity digit : Real) *
          (((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real))) *
          ((strictSiftedCarrier
            (sieveDilation
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) d) z).card : Real) := by
  unfold sectionSixSiftedSum
  exact sectionSixStrictSum_bridge _ _
    (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length) _ d z

theorem sectionSixWeakSiftedSum_eq_card_sub_density_mul_card
    (digit : Fin 10) (length : Nat) (d : PNat) (z : Real) :
    sectionSixWeakSiftedSum digit length d z =
      ((weakSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d) z).card : Real) -
        ((restrictedDigitDensity digit : Real) *
          (((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real))) *
          ((weakSiftedCarrier
            (sieveDilation
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) d) z).card : Real) := by
  unfold sectionSixWeakSiftedSum
  exact sectionSixWeakSum_bridge _ _
    (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length) _ d z

end

end PrimesRestrictedDigits
