import BoundedGaps.Maynard.PreSievedPrimeMertens

noncomputable section

/-!
# Prime Mertens intervals with an extra coprimality modulus

Maynard's S2 coordinate fiber excludes primes dividing both the primorial
pre-sieve and the varying off-coordinate product.  This file isolates the
additional deleted prime mass and retains it explicitly in the interval
estimate used at source lines 524--527.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real

noncomputable def primeLogDivisorMass (P : ℕ) : ℝ :=
  ∑ p ∈ P.primeFactors, Real.log p / (p : ℝ)

noncomputable def augmentedPreSievedPrimeLogIntervalSum
    (D P w z : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE z \ Nat.primesLE (w - 1),
    if p ∣ primorial D * P then 0 else Real.log p / (p : ℝ)

private noncomputable def extraModulusPrimeLogIntervalSum
    (D P w z : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE z \ Nat.primesLE (w - 1)).filter
      (fun p => ¬p ∣ primorial D ∧ p ∣ P),
    Real.log p / (p : ℝ)

private theorem preSievedPrimeLogIntervalSum_eq_augmented_add_extra
    (D P w z : ℕ) :
    preSievedPrimeLogIntervalSum D w z =
      augmentedPreSievedPrimeLogIntervalSum D P w z +
        extraModulusPrimeLogIntervalSum D P w z := by
  classical
  unfold preSievedPrimeLogIntervalSum augmentedPreSievedPrimeLogIntervalSum
    extraModulusPrimeLogIntervalSum
  rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
  by_cases hpW : p ∣ primorial D
  · have hpWP : p ∣ primorial D * P := dvd_mul_of_dvd_left hpW P
    simp [hpW, hpWP]
  · by_cases hpP : p ∣ P
    · have hpWP : p ∣ primorial D * P := dvd_mul_of_dvd_right hpP _
      simp [hpW, hpP, hpWP]
    · have hpWP : ¬p ∣ primorial D * P := by
        simpa [hpPrime.dvd_mul] using not_or_intro hpW hpP
      simp [hpW, hpP, hpWP]

private theorem extraModulusPrimeLogIntervalSum_nonneg
    (D P w z : ℕ) :
    0 ≤ extraModulusPrimeLogIntervalSum D P w z := by
  unfold extraModulusPrimeLogIntervalSum
  apply Finset.sum_nonneg
  intro p hp
  positivity

private theorem extraModulusPrimeLogIntervalSum_le
    {D P w z : ℕ} (hP : 0 < P) :
    extraModulusPrimeLogIntervalSum D P w z ≤ primeLogDivisorMass P := by
  classical
  unfold extraModulusPrimeLogIntervalSum primeLogDivisorMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hpData.1).1
    exact Nat.mem_primeFactors.mpr ⟨hpPrime, hpData.2.2, hP.ne'⟩
  · intro p hpP hpNot
    positivity

theorem exists_uniform_augmentedPreSievedPrimeLogInterval_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ {D P w z : ℕ}, 0 < P → 2 ≤ w → w ≤ z →
      -(K + Real.log D + primeLogDivisorMass P) ≤
          augmentedPreSievedPrimeLogIntervalSum D P w z -
            Real.log ((z : ℝ) / (w : ℝ)) ∧
      augmentedPreSievedPrimeLogIntervalSum D P w z -
          Real.log ((z : ℝ) / (w : ℝ)) ≤ K := by
  obtain ⟨K, hK, hbase⟩ := exists_uniform_preSievedPrimeLogInterval_bounds
  refine ⟨K, hK, fun {D P w z} hP hw hwz => ?_⟩
  have hbounds := hbase (D := D) hw hwz
  have hdecomp :=
    preSievedPrimeLogIntervalSum_eq_augmented_add_extra D P w z
  have hextraNonneg := extraModulusPrimeLogIntervalSum_nonneg D P w z
  have hextraLe := extraModulusPrimeLogIntervalSum_le
    (D := D) (w := w) (z := z) hP
  constructor <;> linarith

end BoundedGaps.Maynard
