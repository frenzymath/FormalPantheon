import BoundedGaps.Maynard.PrimeMertensInterval

noncomputable section

/-!
# The pre-sieved prime Mertens interval estimate

Deleting primes dividing `D#` can only decrease the interval sum. The deleted
mass is at most the initial prime logarithmic harmonic sum at `D`, so SEM-162
gives precisely the `O(1 + log D)` lower-error parameter used by Maynard.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real

noncomputable def preSievedPrimeLogIntervalSum
    (D w z : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE z \ Nat.primesLE (w - 1),
    if p ∣ primorial D then 0 else Real.log p / (p : ℝ)

private noncomputable def excludedPrimeLogIntervalSum
    (D w z : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE z \ Nat.primesLE (w - 1),
    if p ∣ primorial D then Real.log p / (p : ℝ) else 0

private theorem primeLogIntervalSum_eq_preSieved_add_excluded
    (D w z : ℕ) :
    primeLogIntervalSum w z =
      preSievedPrimeLogIntervalSum D w z +
        excludedPrimeLogIntervalSum D w z := by
  classical
  unfold primeLogIntervalSum preSievedPrimeLogIntervalSum
    excludedPrimeLogIntervalSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hdvd : p ∣ primorial D <;> simp [hdvd]

private theorem excludedPrimeLogIntervalSum_nonneg (D w z : ℕ) :
    0 ≤ excludedPrimeLogIntervalSum D w z := by
  unfold excludedPrimeLogIntervalSum
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · positivity
  · rfl

private theorem excludedPrimeLogIntervalSum_le (D w z : ℕ) :
    excludedPrimeLogIntervalSum D w z ≤ primeLogHarmonicSum D := by
  classical
  unfold excludedPrimeLogIntervalSum primeLogHarmonicSum
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_sdiff] at hp
    have hpPrime := Nat.prime_of_mem_primesLE hp.1.1
    exact Nat.mem_primesLE.mpr
      ⟨hpPrime.dvd_primorial_iff.mp hp.2, hpPrime⟩
  · intro p hpD hpNot
    positivity

theorem exists_uniform_preSievedPrimeLogInterval_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ {D w z : ℕ}, 2 ≤ w → w ≤ z →
      -(K + Real.log D) ≤
          preSievedPrimeLogIntervalSum D w z -
            Real.log ((z : ℝ) / (w : ℝ)) ∧
      preSievedPrimeLogIntervalSum D w z -
          Real.log ((z : ℝ) / (w : ℝ)) ≤ K := by
  obtain ⟨Cint, hCint⟩ :=
    exists_uniform_abs_primeLogIntervalSum_sub_log_div
  obtain ⟨Cinit, hCinit⟩ :=
    exists_uniform_abs_primeLogHarmonicSum_sub_log
  let K := |Cint| + |Cinit| + 1
  refine ⟨K, by unfold K; positivity, fun {D w z} hw hwz => ?_⟩
  have hdecomp := primeLogIntervalSum_eq_preSieved_add_excluded D w z
  have hexcludedNonneg := excludedPrimeLogIntervalSum_nonneg D w z
  have hexcludedLe := excludedPrimeLogIntervalSum_le D w z
  have hinterval := abs_le.mp (hCint hw hwz)
  have hinit := abs_le.mp (hCinit D)
  have hCintLe : Cint ≤ |Cint| := le_abs_self Cint
  have hCinitLe : Cinit ≤ |Cinit| := le_abs_self Cinit
  have hlogD : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  constructor
  · rw [hdecomp] at hinterval
    unfold K
    linarith
  · rw [hdecomp] at hinterval
    unfold K
    linarith

end BoundedGaps.Maynard
