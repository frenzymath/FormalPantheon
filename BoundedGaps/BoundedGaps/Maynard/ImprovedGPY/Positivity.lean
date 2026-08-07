import BoundedGaps.Proof.TupleBridge

/-!
# Positivity in the improved GPY method

Maynard2013v3, Section 3, equation `eq:BasicSum` (source lines 154--175),
observes that a positive weighted excess with nonnegative weights forces a
translate containing more than the threshold number of primes.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- Maynard's `S₁`: total sieve weight on `[N,2N)`. -/
noncomputable def sieveWeightSum (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico N (2 * N), w n

/-- Maynard's `S₂`: sieve weight multiplied by the number of prime shifts. -/
noncomputable def primeWeightedSieveSum (H : Finset ℕ) (N : ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico N (2 * N), (BoundedGaps.primeShiftCount H n : ℝ) * w n

/-- The weighted excess `S₂ - rho*S₁` from `eq:BasicSum`. -/
noncomputable def sieveExcess (H : Finset ℕ) (N : ℕ) (rho : ℝ)
    (w : ℕ → ℝ) : ℝ :=
  primeWeightedSieveSum H N w - rho * sieveWeightSum N w

/-- At every sufficiently large scale, some nonnegative weights have positive
sieve excess. The weights may depend on the scale. -/
def HasEventuallyPositiveSieveExcess (H : Finset ℕ) (rho : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ w : ℕ → ℝ,
    (∀ n ∈ Finset.Ico N (2 * N), 0 ≤ w n) ∧
      0 < sieveExcess H N rho w

theorem sieveExcess_eq_sum (H : Finset ℕ) (N : ℕ) (rho : ℝ)
    (w : ℕ → ℝ) :
    sieveExcess H N rho w =
      ∑ n ∈ Finset.Ico N (2 * N),
        ((BoundedGaps.primeShiftCount H n : ℝ) - rho) * w n := by
  simp only [sieveExcess, primeWeightedSieveSum, sieveWeightSum, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum]

theorem exists_primeShiftCount_gt_of_sieveExcess_pos
    {H : Finset ℕ} {N : ℕ} {rho : ℝ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Ico N (2 * N), 0 ≤ w n)
    (hpos : 0 < sieveExcess H N rho w) :
    ∃ n ∈ Finset.Ico N (2 * N),
      rho < (BoundedGaps.primeShiftCount H n : ℝ) := by
  by_contra hnone
  have hterm : ∀ n ∈ Finset.Ico N (2 * N),
      ((BoundedGaps.primeShiftCount H n : ℝ) - rho) * w n ≤ 0 := by
    intro n hn
    have hcount : (BoundedGaps.primeShiftCount H n : ℝ) ≤ rho := by
      exact le_of_not_gt (fun hgt => hnone ⟨n, hn, hgt⟩)
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcount) (hw n hn)
  have hsum := Finset.sum_nonpos hterm
  rw [← sieveExcess_eq_sum] at hsum
  exact (not_lt_of_ge hsum) hpos

theorem infinitelyOftenAtLeastTwoPrimeShifts_of_eventuallyPositiveSieveExcess
    {H : Finset ℕ} (hpos : HasEventuallyPositiveSieveExcess H 1) :
    BoundedGaps.InfinitelyOftenAtLeastPrimeShifts H 2 := by
  obtain ⟨N₀, hN₀⟩ := hpos
  intro T
  let N := max N₀ (T + 1)
  obtain ⟨w, hw, hexcess⟩ := hN₀ N (le_max_left _ _)
  obtain ⟨n, hn, hcount⟩ :=
    exists_primeShiftCount_gt_of_sieveExcess_pos hw hexcess
  refine ⟨n, ?_, ?_⟩
  · have hNn := (Finset.mem_Ico.mp hn).1
    have hTN : T + 1 ≤ N := le_max_right _ _
    omega
  · have hcountNat : 1 < BoundedGaps.primeShiftCount H n := by
      exact_mod_cast hcount
    omega

theorem boundedGapsStatement_of_engelsma_eventuallyPositiveSieveExcess
    (hpos : HasEventuallyPositiveSieveExcess BoundedGaps.engelsmaTuple 1) :
    BoundedGaps.boundedGapsStatement :=
  BoundedGaps.boundedGapsStatement_of_engelsma_two_prime_shifts
    (infinitelyOftenAtLeastTwoPrimeShifts_of_eventuallyPositiveSieveExcess hpos)

end BoundedGaps.Maynard
