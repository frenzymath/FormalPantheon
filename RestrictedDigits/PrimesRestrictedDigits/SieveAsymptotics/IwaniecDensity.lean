import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.SelbergSieve

/-!
# Iwaniec sieve density identities

This gives the full Moebius density baseline and the exact half-open telescope in
`IWANIEC-ROSSER-SIEVE-1980`, Section 4, pp. 179--180, Eq. (4.3). It estimates no Rosser
correction term.
-/

open scoped BigOperators ArithmeticFunction.Moebius

open ArithmeticFunction Finset Nat

namespace PrimesRestrictedDigits

noncomputable section

/-- The finite density product relative to an ambient factor set, with the
strict upper cutoff used by Iwaniec's `V(z)`. -/
def sieveDensityBelow
    (P : Finset Nat) (nu : Nat → Real) (z : Real) : Real :=
  ∏ p ∈ P.filter (fun p : Nat ↦ (p : Real) < z), (1 - nu p)

/-- If every ambient factor is below the cutoff, the cutoff density is the
full finite product. -/
theorem sieveDensityBelow_eq_fullProduct
    (P : Finset Nat) (nu : Nat → Real) {z : Real}
    (hcutoff : ∀ p ∈ P, (p : Real) < z) :
    sieveDensityBelow P nu z = ∏ p ∈ P, (1 - nu p) := by
  rw [sieveDensityBelow, Finset.filter_eq_self.mpr hcutoff]

/-- The exact finite density telescope on the weak-lower, strict-upper
interval `[w,z)`. -/
theorem sum_mul_sieveDensityBelow_eq_sub
    (P : Finset Nat) (nu : Nat → Real)
    {w z : Real} (hwz : w ≤ z) :
    (∑ p ∈ P.filter
        (fun p : Nat ↦ w ≤ (p : Real) ∧ (p : Real) < z),
      nu p * sieveDensityBelow P nu p) =
      sieveDensityBelow P nu w - sieveDensityBelow P nu z := by
  let A := P.filter (fun p : Nat ↦ (p : Real) < w)
  let B := P.filter
    (fun p : Nat ↦ w ≤ (p : Real) ∧ (p : Real) < z)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    simp only [A, Finset.mem_filter] at hpA
    simp only [B, Finset.mem_filter] at hpB
    linarith
  have hBelowW : P.filter (fun p : Nat ↦ (p : Real) < w) = A := rfl
  have hBelowZ : P.filter (fun p : Nat ↦ (p : Real) < z) = A ∪ B := by
    ext p
    simp only [A, B, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hp
      by_cases hpw : (p : Real) < w
      · exact Or.inl ⟨hp.1, hpw⟩
      · exact Or.inr ⟨hp.1, le_of_not_gt hpw, hp.2⟩
    · rintro (⟨hpP, hpw⟩ | ⟨hpP, _, hpz⟩)
      · exact ⟨hpP, hpw.trans_le hwz⟩
      · exact ⟨hpP, hpz⟩
  have hPrefix (p : Nat) (hp : p ∈ B) :
      P.filter (fun q : Nat ↦ (q : Real) < p) =
        A ∪ B.filter (fun q ↦ q < p) := by
    have hpData : p ∈ P ∧ w ≤ (p : Real) ∧ (p : Real) < z := by
      simpa only [B, Finset.mem_filter] using hp
    ext q
    simp only [A, B, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hq
      by_cases hqw : (q : Real) < w
      · exact Or.inl ⟨hq.1, hqw⟩
      · right
        refine ⟨⟨hq.1, le_of_not_gt hqw, ?_⟩, ?_⟩
        · exact hq.2.trans hpData.2.2
        · exact_mod_cast hq.2
    · rintro (⟨hqP, hqw⟩ | ⟨⟨hqP, _, _⟩, hqp⟩)
      · exact ⟨hqP, hqw.trans_le hpData.2.1⟩
      · exact ⟨hqP, by exact_mod_cast hqp⟩
  have hDensityPrefix (p : Nat) (hp : p ∈ B) :
      sieveDensityBelow P nu p =
        (∏ q ∈ A, (1 - nu q)) *
          ∏ q ∈ B with q < p, (1 - nu q) := by
    rw [sieveDensityBelow, hPrefix p hp,
      Finset.prod_union (hAB.mono_right (Finset.filter_subset _ _))]
  have hOrdered :
      (∑ p ∈ B, nu p * ∏ q ∈ B with q < p, (1 - nu q)) =
        1 - ∏ p ∈ B, (1 - nu p) := by
    rw [Finset.prod_one_sub_ordered]
    ring
  rw [show P.filter
      (fun p : Nat ↦ w ≤ (p : Real) ∧ (p : Real) < z) = B by rfl]
  calc
    (∑ p ∈ B, nu p * sieveDensityBelow P nu p) =
        (∏ q ∈ A, (1 - nu q)) *
          ∑ p ∈ B, nu p * ∏ q ∈ B with q < p, (1 - nu q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hDensityPrefix p hp]
      ring
    _ = (∏ q ∈ A, (1 - nu q)) *
        (1 - ∏ p ∈ B, (1 - nu p)) := by rw [hOrdered]
    _ = sieveDensityBelow P nu w - sieveDensityBelow P nu z := by
      rw [sieveDensityBelow, hBelowW, sieveDensityBelow, hBelowZ,
        Finset.prod_union hAB]
      ring

end

/-- The full Moebius main sum is the product of the local density factors. -/
theorem boundingSieveMainSum_moebius_eq_prod_one_sub_nu
    (s : BoundingSieve) :
    s.mainSum (fun d ↦ (ArithmeticFunction.moebius d : Real)) =
      ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  rw [BoundingSieve.mainSum]
  symm
  simpa only [Int.cast_natCast, Int.cast_ofNat] using
    s.nu_mult.prodPrimeFactors_one_sub_of_squarefree s.nu
      s.prodPrimes_squarefree

/-- If all sieving factors lie below `z`, the full Moebius main sum is the
strict-cutoff density at `z`. -/
theorem boundingSieveMainSum_moebius_eq_sieveDensityBelow
    (s : BoundingSieve) {z : Real}
    (hcutoff : ∀ p ∈ s.prodPrimes.primeFactors, (p : Real) < z) :
    s.mainSum (fun d ↦ (ArithmeticFunction.moebius d : Real)) =
      PrimesRestrictedDigits.sieveDensityBelow
        s.prodPrimes.primeFactors s.nu z := by
  rw [PrimesRestrictedDigits.sieveDensityBelow_eq_fullProduct
    _ _ hcutoff]
  exact boundingSieveMainSum_moebius_eq_prod_one_sub_nu s

end PrimesRestrictedDigits
