import PrimesRestrictedDigits.SieveAsymptotics.RosserRankRecurrence
import PrimesRestrictedDigits.SieveAsymptotics.RosserRecurrenceVanishing

/-!
# Partial-sum recurrences for finite Rosser failures

The exact rank recurrences are summed through a finite rank `R`. The upper identity retains
the cubic level hypothesis that removes rank zero and makes the separate singleton gate
automatic.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem upperRosserFailurePartialSum_succ
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat) :
    upperRosserFailurePartialSum P nu level z (R + 1) =
      upperRosserFailurePartialSum P nu level z R +
        upperRosserFailureSumAtRank P nu level z (R + 1) := by
  rw [upperRosserFailurePartialSum, upperRosserFailurePartialSum]
  exact Finset.sum_range_succ _ _

theorem lowerRosserFailurePartialSum_succ
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat) :
    lowerRosserFailurePartialSum P nu level z (R + 1) =
      lowerRosserFailurePartialSum P nu level z R +
        lowerRosserFailureSumAtRank P nu level z (R + 1) := by
  rw [lowerRosserFailurePartialSum, lowerRosserFailurePartialSum,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ R + 1)]

/-- The finite form of Iwaniec's (4.4) before the weak root support is made
explicit. -/
theorem lowerRosserFailurePartialSum_succ_eq_sum_upper_unrestricted
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) :
    lowerRosserFailurePartialSum P nu level z (R + 1) =
      ∑ p ∈ P.filter (fun p : Nat ↦ (p : Real) < z),
        nu p * upperRosserFailurePartialSum P nu (level / p) p R := by
  induction R with
  | zero =>
      rw [lowerRosserFailurePartialSum_succ,
        lowerRosserFailurePartialSum_zero, zero_add,
        lowerRosserFailureSumAtRank_succ_eq_sum_upper P nu level z 0 hprime]
      apply Finset.sum_congr rfl
      intro p hp
      rw [upperRosserFailurePartialSum_zero]
  | succ R ih =>
      rw [lowerRosserFailurePartialSum_succ, ih,
        lowerRosserFailureSumAtRank_succ_eq_sum_upper
          P nu level z (R + 1) hprime,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [upperRosserFailurePartialSum_succ]
      ring

/-- Under the cubic level condition, every head below `z` passes the first
upper gate. -/
theorem upperRosserFailureSumAtRank_succ_eq_sum_lower_of_cube_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hcube : z ^ 3 ≤ level) :
    upperRosserFailureSumAtRank P nu level z (r + 1) =
      ∑ p ∈ P.filter (fun p : Nat ↦ (p : Real) < z),
        nu p * lowerRosserFailureSumAtRank P nu (level / p) p (r + 1) := by
  rw [upperRosserFailureSumAtRank_succ_eq_sum_lower
    P nu level z r hprime]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpP, hpz, hgate⟩
    exact ⟨hpP, hpz⟩
  · rintro ⟨hpP, hpz⟩
    refine ⟨hpP, hpz, ?_⟩
    have hpCube : (p : Real) ^ 3 < z ^ 3 :=
      pow_lt_pow_left₀ hpz (by positivity) (by norm_num)
    nlinarith

/-- The finite form of Iwaniec's (4.5) before the weak root support is made
explicit. Rank zero vanishes under `z^3 ≤ level`. -/
theorem upperRosserFailurePartialSum_eq_sum_lower_of_cube_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hcube : z ^ 3 ≤ level) :
    upperRosserFailurePartialSum P nu level z R =
      ∑ p ∈ P.filter (fun p : Nat ↦ (p : Real) < z),
        nu p * lowerRosserFailurePartialSum P nu (level / p) p R := by
  induction R with
  | zero =>
      rw [upperRosserFailurePartialSum_zero,
        upperRosserFailureSumAtRank_eq_zero_of_cutoffPow_le
          P nu level z 0 hprime (by simpa using hcube)]
      simp
  | succ R ih =>
      rw [upperRosserFailurePartialSum_succ, ih,
        upperRosserFailureSumAtRank_succ_eq_sum_lower_of_cube_le
          P nu level z R hprime hcube,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [lowerRosserFailurePartialSum_succ]
      ring

end PrimesRestrictedDigits
