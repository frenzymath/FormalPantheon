import PrimesRestrictedDigits.BasicEstimates.StrictAbelSummation
import Mathlib.MeasureTheory.Function.Floor

/-!
# Strict and weak real prime counts

This file compares the strict count used at the boundaries of Eq. (7.45) with
the conventional weak real prime count used by the prime number theorem.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

/-- The conventional number of primes at most a real cutoff. -/
noncomputable def realPrimeCounting (t : Real) : Real :=
  Nat.primeCounting (Nat.floor t)

private theorem ceil_eq_floor_add_one_of_nonneg_of_not_natCast
    {t : Real} (ht : 0 ≤ t)
    (hnat : t ∉ Set.range fun n : Nat => (n : Real)) :
    Nat.ceil t = Nat.floor t + 1 := by
  have hne : Nat.ceil t ≠ Nat.floor t := by
    intro heq
    have ht_eq : t = (Nat.floor t : Real) := le_antisymm
      (by simpa [heq] using (Nat.le_ceil t))
      (Nat.floor_le ht)
    exact hnat ⟨Nat.floor t, ht_eq.symm⟩
  have hfc : Nat.floor t ≤ Nat.ceil t := Nat.floor_le_ceil t
  have hcf : Nat.ceil t ≤ Nat.floor t + 1 := Nat.ceil_le_floor_add_one t
  omega

theorem realPrimeCountingLt_le_realPrimeCounting (t : Real) :
    realPrimeCountingLt t ≤ realPrimeCounting t := by
  unfold realPrimeCountingLt realPrimeCounting
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  exact_mod_cast Nat.monotone_primeCounting'
    (Nat.ceil_le_floor_add_one t)

theorem realPrimeCounting_le_realPrimeCountingLt_add_one (t : Real) :
    realPrimeCounting t ≤ realPrimeCountingLt t + 1 := by
  unfold realPrimeCountingLt realPrimeCounting
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  have hmono : Nat.primeCounting' (Nat.floor t + 1) ≤
      Nat.primeCounting' (Nat.ceil t + 1) :=
    Nat.monotone_primeCounting' (Nat.add_le_add_right (Nat.floor_le_ceil t) 1)
  have hstep : Nat.primeCounting' (Nat.ceil t + 1) ≤
      Nat.primeCounting' (Nat.ceil t) + 1 := by
    rw [Nat.primeCounting', Nat.count_succ]
    split <;> omega
  exact_mod_cast hmono.trans hstep

/-- The endpoint jump is present exactly when the natural endpoint is prime. -/
theorem realPrimeCountingLt_sub_realPrimeCounting_natCast (n : Nat) :
    realPrimeCountingLt (n : Real) - realPrimeCounting (n : Real) =
      if n.Prime then -1 else 0 := by
  simp [realPrimeCountingLt, realPrimeCounting, Nat.primeCounting,
    Nat.primeCounting', Nat.count_succ]
  split_ifs <;> norm_num

theorem abs_realPrimeCountingLt_sub_realPrimeCounting_le_one (t : Real) :
    |realPrimeCountingLt t - realPrimeCounting t| ≤ 1 := by
  rw [abs_sub_le_iff]
  constructor <;> linarith
    [realPrimeCountingLt_le_realPrimeCounting t,
      realPrimeCounting_le_realPrimeCountingLt_add_one t]

theorem realPrimeCountingLt_eq_realPrimeCounting_of_not_natCast
    {t : Real} (hnat : t ∉ Set.range fun n : Nat => (n : Real)) :
    realPrimeCountingLt t = realPrimeCounting t := by
  by_cases ht : 0 ≤ t
  · unfold realPrimeCountingLt realPrimeCounting
    rw [Nat.primeCounting_eq_primeCounting'_succ,
      ceil_eq_floor_add_one_of_nonneg_of_not_natCast ht hnat]
  · have hceil : Nat.ceil t = 0 := Nat.ceil_eq_zero.mpr (le_of_not_ge ht)
    have hfloor : Nat.floor t = 0 := Nat.floor_eq_zero.mpr (by linarith)
    simp [realPrimeCountingLt, realPrimeCounting, hceil, hfloor,
      Nat.primeCounting', Nat.primeCounting]

theorem realPrimeCountingLt_ae_eq_realPrimeCounting :
    realPrimeCountingLt =ᵐ[volume] realPrimeCounting := by
  have hnull : volume (Set.range (fun n : Nat => (n : Real))) = 0 :=
    Set.countable_range (fun n : Nat => (n : Real)) |>.measure_zero volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht
  exact realPrimeCountingLt_eq_realPrimeCounting_of_not_natCast ht

theorem measurable_realPrimeCounting : Measurable realPrimeCounting := by
  exact (measurable_of_countable (fun n : Nat => (Nat.primeCounting n : Real))).comp
    Nat.measurable_floor

theorem measurable_realPrimeCountingLt : Measurable realPrimeCountingLt := by
  exact (measurable_of_countable (fun n : Nat => (Nat.primeCounting' n : Real))).comp
    Nat.measurable_ceil

end PrimesRestrictedDigits
