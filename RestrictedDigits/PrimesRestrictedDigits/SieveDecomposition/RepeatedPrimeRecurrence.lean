import PrimesRestrictedDigits.SieveDecomposition.RepeatedPrimeFiber

/-!
# Outer repeated-prime Buchstab recurrence

The strict Buchstab carrier is split into weak least-prime fibers. Each such fiber has a
strict once-dilated part and a weak twice-dilated part; retaining the latter is necessary when
prime powers occur.

and `MAYNARD-PRD-PUBLISHED`, Section 6 and Proposition 6.1.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The strict cofactor contribution attached to an outer prime index. -/
noncomputable def strictPrimeBuchstabTerm
    {M : Type*} [AddCommMonoid M]
    (C : Finset Nat) (p : Nat) (w : Nat → M) : M :=
  ∑ m ∈ strictSiftedCarrier (sieveDilation C (Nat.toPNat' p)) (p : Real),
    w (m * p)

/-- The contribution left after extracting a second copy of the outer prime. -/
noncomputable def repeatedPrimeBuchstabTerm
    {M : Type*} [AddCommMonoid M]
    (C : Finset Nat) (p : Nat) (w : Nat → M) : M :=
  ∑ k ∈ weakSiftedCarrier
      (sieveDilation
        (sieveDilation C (Nat.toPNat' p)) (Nat.toPNat' p)) (p : Real),
    w ((k * p) * p)

/-- Sum the exact strict and repeated pieces over one prime interval. -/
theorem sum_weakPrimeThresholdFiberInterval_eq_strict_add_repeated
    {M : Type*} [AddCommMonoid M]
    (C : Finset Nat) (z1 z2 : Real) (w : Nat → M) :
    (∑ p ∈ sievePrimeInterval z1 z2,
        ∑ n ∈ weakPrimeThresholdFiber C p, w n) =
      (∑ p ∈ sievePrimeInterval z1 z2,
        strictPrimeBuchstabTerm C p w) +
        ∑ p ∈ sievePrimeInterval z1 z2,
          repeatedPrimeBuchstabTerm C p w := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpMem
  have hp' := (mem_sievePrimeInterval.mp hpMem).1
  have hpnat : (⟨p, hp'.pos⟩ : ℕ+) = Nat.toPNat' p := by
    apply PNat.eq
    rw [Nat.toPNat'_coe, if_pos hp'.pos]
    rfl
  unfold strictPrimeBuchstabTerm repeatedPrimeBuchstabTerm
  rw [← hpnat]
  exact sum_weakPrimeThresholdFiber_eq_strict_add_repeatedDilation C hp' w

/-- The additive-monoid form of the corrected outer Buchstab recurrence. -/
theorem sum_strictSiftedCarrier_buchstab_with_repeated
    {M : Type*} [AddCommMonoid M]
    (C : Finset Nat) {z1 z2 : Real} (hz : z1 ≤ z2)
    (w : Nat → M) :
    (∑ n ∈ strictSiftedCarrier C z2, w n) +
        (∑ p ∈ sievePrimeInterval z1 z2,
          strictPrimeBuchstabTerm C p w) +
      ∑ p ∈ sievePrimeInterval z1 z2,
        repeatedPrimeBuchstabTerm C p w =
      ∑ n ∈ strictSiftedCarrier C z1, w n := by
  have hsplit :=
    sum_weakPrimeThresholdFiberInterval_eq_strict_add_repeated C z1 z2 w
  have hbuch := sum_strictSiftedCarrier_buchstab C hz w
  calc
    (∑ n ∈ strictSiftedCarrier C z2, w n) +
          (∑ p ∈ sievePrimeInterval z1 z2,
            strictPrimeBuchstabTerm C p w) +
        ∑ p ∈ sievePrimeInterval z1 z2,
          repeatedPrimeBuchstabTerm C p w =
      (∑ n ∈ strictSiftedCarrier C z2, w n) +
        (∑ p ∈ sievePrimeInterval z1 z2,
          ∑ n ∈ weakPrimeThresholdFiber C p, w n) := by
      rw [hsplit]
      simp only [add_assoc]
    _ = ∑ n ∈ strictSiftedCarrier C z1, w n := hbuch

/-- The signed form of the corrected outer recurrence. -/
theorem sum_strictSiftedCarrier_eq_sub_strict_sub_repeated
    {M : Type*} [AddCommGroup M]
    (C : Finset Nat) {z1 z2 : Real} (hz : z1 ≤ z2)
    (w : Nat → M) :
    (∑ n ∈ strictSiftedCarrier C z2, w n) =
      (∑ n ∈ strictSiftedCarrier C z1, w n) -
          (∑ p ∈ sievePrimeInterval z1 z2,
            strictPrimeBuchstabTerm C p w) -
        ∑ p ∈ sievePrimeInterval z1 z2,
          repeatedPrimeBuchstabTerm C p w := by
  have h := sum_strictSiftedCarrier_buchstab_with_repeated C hz w
  apply (eq_sub_iff_add_eq).2
  apply (eq_sub_iff_add_eq).2
  simpa only [add_assoc, add_left_comm, add_comm] using h

end PrimesRestrictedDigits
