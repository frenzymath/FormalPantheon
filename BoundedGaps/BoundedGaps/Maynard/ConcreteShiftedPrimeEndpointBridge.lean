import BoundedGaps.Maynard.IntervalDistribution
import BoundedGaps.Maynard.ConcreteS2ShiftKernel

namespace BoundedGaps.Maynard

private theorem cast_prime_filter_Ico_eq_primeCount_sub
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    (((Finset.Ico A B).filter Nat.Prime).card : ℝ) =
      (primeCountTotal (B - 1) : ℝ) -
        (primeCountTotal (A - 1) : ℝ) := by
  have hAeq : A - 1 + 1 = A := by omega
  have hBeq : B - 1 + 1 = B := by omega
  unfold primeCountTotal Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.natCast_card_filter]
  simpa [hAeq, hBeq] using
    (Finset.sum_Ico_eq_sub
      (f := fun n : ℕ => if n.Prime then (1 : ℝ) else 0) hAB)

private theorem abs_primeCountTotal_add_sub_le
    (a h : ℕ) :
    |(primeCountTotal (a + h) : ℝ) - (primeCountTotal a : ℝ)| ≤ (h : ℝ) := by
  have hcard := cast_prime_filter_Ico_eq_primeCount_sub
    (A := a + 1) (B := a + h + 1) (by omega) (by omega)
  have hsubset :
      (Finset.Ico (a + 1) (a + h + 1)).filter Nat.Prime ⊆
        Finset.Ico (a + 1) (a + h + 1) := by
    exact Finset.filter_subset Nat.Prime _
  have hcardNat := Finset.card_le_card hsubset
  rw [Nat.card_Ico] at hcardNat
  have hcardNat' :
      (Finset.filter Nat.Prime (Finset.Ico (a + 1) (a + h + 1))).card ≤ h := by
    omega
  have hcardReal :
      ((((Finset.Ico (a + 1) (a + h + 1)).filter Nat.Prime).card : ℕ) : ℝ)
        ≤ (h : ℝ) := by
    exact_mod_cast hcardNat'
  have hcard' :
      (((Finset.Ico (a + 1) (a + h + 1)).filter Nat.Prime).card : ℝ) =
        (primeCountTotal (a + h) : ℝ) - (primeCountTotal a : ℝ) := by
    simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel_left] using hcard
  have hinc :
      0 ≤ (primeCountTotal (a + h) : ℝ) - (primeCountTotal a : ℝ) := by
    rw [← hcard']
    positivity
  have hupper :
      (primeCountTotal (a + h) : ℝ) - (primeCountTotal a : ℝ) ≤ (h : ℝ) := by
    rw [← hcard']
    exact hcardReal
  rw [abs_of_nonneg hinc]
  exact hupper

/--
For a fixed shift, the exact half-open shifted prime interval differs from
the unshifted `[N, 2*N)` interval only by its two endpoint strips.  This is
the finite arithmetic bridge used before any prime-number-theorem input;
see SEM-400 and Maynard2013v3, equations (5.15)--(5.17).
-/
theorem abs_engelsmaShiftedPrimeIntervalCount_sub_primeCountTotalInInterval_le
    {N : ℕ} (hN : 0 < N) (h : BoundedGaps.engelsmaTuple) :
    |engelsmaShiftedPrimeIntervalCount N h -
        (primeCountTotalInInterval N : ℝ)| ≤ 2 * (h.1 : ℝ) := by
  have htotal := cast_primeCountTotalInInterval hN
  unfold engelsmaShiftedPrimeIntervalCount
  rw [htotal]
  have hA := abs_primeCountTotal_add_sub_le (2 * N - 1) h.1
  have hB := abs_primeCountTotal_add_sub_le (N - 1) h.1
  have h2N : 2 * N + h.1 - 1 = (2 * N - 1) + h.1 := by omega
  have hN' : N + h.1 - 1 = (N - 1) + h.1 := by omega
  rw [h2N, hN']
  have hrearrange :
      ((primeCountTotal ((2 * N - 1) + h.1) : ℝ) -
          (primeCountTotal ((N - 1) + h.1) : ℝ)) -
          ((primeCountTotal (2 * N - 1) : ℝ) -
            (primeCountTotal (N - 1) : ℝ)) =
        ((primeCountTotal ((2 * N - 1) + h.1) : ℝ) -
            (primeCountTotal (2 * N - 1) : ℝ)) -
          ((primeCountTotal ((N - 1) + h.1) : ℝ) -
            (primeCountTotal (N - 1) : ℝ)) := by ring
  rw [hrearrange]
  calc
    |((primeCountTotal ((2 * N - 1) + h.1) : ℝ) -
          (primeCountTotal (2 * N - 1) : ℝ)) -
        ((primeCountTotal ((N - 1) + h.1) : ℝ) -
          (primeCountTotal (N - 1) : ℝ))| ≤
      |(primeCountTotal ((2 * N - 1) + h.1) : ℝ) -
          (primeCountTotal (2 * N - 1) : ℝ)| +
        |(primeCountTotal ((N - 1) + h.1) : ℝ) -
          (primeCountTotal (N - 1) : ℝ)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le
          ((primeCountTotal ((2 * N - 1) + h.1) : ℝ) -
            (primeCountTotal (2 * N - 1) : ℝ))
          0
          ((primeCountTotal ((N - 1) + h.1) : ℝ) -
            (primeCountTotal (N - 1) : ℝ)))
    _ ≤ (h.1 : ℝ) + (h.1 : ℝ) := add_le_add hA hB
    _ = 2 * (h.1 : ℝ) := by ring

end BoundedGaps.Maynard
