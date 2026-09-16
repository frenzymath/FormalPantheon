import PrimesRestrictedDigits.SieveAsymptotics.RosserRecurrenceVanishing
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedMoment

/-!
# Finite Rosser rank tails

The all-rank first-failure sums are finite, while the source induction controls finite partial
rank sums. This module records their exact residual tails. It is deliberately algebraic:
quantitative high-rank decay is a separate downstream node.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The upper ranks beyond a partial cutoff `R`. -/
def upperRosserFailureRankTail
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat) : Real :=
  ∑ r ∈ Finset.Ico (R + 1)
      (((sieveFactorsBelow P z).length + 1) / 2),
    upperRosserFailureSumAtRank P nu level z r

/-- The lower ranks beyond a partial cutoff `R`. -/
def lowerRosserFailureRankTail
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat) : Real :=
  ∑ r ∈ Finset.Icc (R + 1)
      ((sieveFactorsBelow P z).length / 2),
    lowerRosserFailureSumAtRank P nu level z r

/-- The upper all-rank sum is exactly its partial sum plus the remaining
finite rank interval. -/
theorem upperRosserFailureSum_eq_partial_add_rankTail
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat) :
    upperRosserFailureSum P nu level z =
      upperRosserFailurePartialSum P nu level z R +
        upperRosserFailureRankTail P nu level z R := by
  classical
  let N : Nat := ((sieveFactorsBelow P z).length + 1) / 2
  let f : Nat → Real :=
    fun r => upperRosserFailureSumAtRank P nu level z r
  by_cases h : R + 1 ≤ N
  · simpa only [upperRosserFailureSum, upperRosserFailurePartialSum,
      upperRosserFailureRankTail, N, f] using
      (Finset.sum_range_add_sum_Ico f h).symm
  · have hN : N ≤ R + 1 := by omega
    have hsum :
        (∑ r ∈ Finset.range N, f r) =
          ∑ r ∈ Finset.range (R + 1), f r := by
      apply Finset.sum_subset (Finset.range_mono hN)
      intro r hr hrN
      apply upperRosserFailureSumAtRank_eq_zero_of_length_lt
      simp only [Finset.mem_range] at hr hrN
      dsimp only [N] at hrN
      omega
    have htail : Finset.Ico (R + 1) N = ∅ :=
      Finset.Ico_eq_empty_of_le hN
    simpa only [upperRosserFailureSum, upperRosserFailurePartialSum,
      upperRosserFailureRankTail, N, f, htail, Finset.sum_empty, add_zero]
      using hsum

/-- The lower all-rank sum is exactly its partial sum plus the remaining
finite rank interval. -/
theorem lowerRosserFailureSum_eq_partial_add_rankTail
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat) :
    lowerRosserFailureSum P nu level z =
      lowerRosserFailurePartialSum P nu level z R +
        lowerRosserFailureRankTail P nu level z R := by
  classical
  let N : Nat := (sieveFactorsBelow P z).length / 2
  let f : Nat → Real :=
    fun r => lowerRosserFailureSumAtRank P nu level z r
  by_cases h : R ≤ N
  · have hsum := Finset.sum_Ico_consecutive f
      (m := 1) (n := R + 1) (k := N + 1)
      (by omega : 1 ≤ R + 1) (by omega : R + 1 ≤ N + 1)
    simpa only [lowerRosserFailureSum, lowerRosserFailurePartialSum,
      lowerRosserFailureRankTail, N, f,
      Finset.Ico_add_one_right_eq_Icc] using hsum.symm
  · have hN : N ≤ R := by omega
    have hsum :
        (∑ r ∈ Finset.Icc 1 N, f r) =
          ∑ r ∈ Finset.Icc 1 R, f r := by
      apply Finset.sum_subset
        (Finset.Icc_subset_Icc (le_refl 1) hN)
      intro r hr hrN
      apply lowerRosserFailureSumAtRank_eq_zero_of_length_lt
      simp only [Finset.mem_Icc] at hr hrN
      dsimp only [N] at hrN
      omega
    have htail : Finset.Icc (R + 1) N = ∅ := by
      apply Finset.Icc_eq_empty_of_lt
      omega
    simpa only [lowerRosserFailureSum, lowerRosserFailurePartialSum,
      lowerRosserFailureRankTail, N, f, htail, Finset.sum_empty, add_zero]
      using hsum

/-- Upper reciprocal-prime rank tails are nonnegative. -/
theorem upperRosserFailureRankTail_reciprocal_nonneg
    (P : Finset Nat) (level z : Real) (R : Nat)
    (hprime : forall p, p ∈ P -> p.Prime) :
    0 ≤ upperRosserFailureRankTail P (fun p => (p : Real)⁻¹)
      level z R := by
  rw [upperRosserFailureRankTail]
  apply Finset.sum_nonneg
  intro r hr
  exact upperRosserFailureSumAtRank_reciprocal_nonneg P level z r hprime

/-- Lower reciprocal-prime rank tails are nonnegative. -/
theorem lowerRosserFailureRankTail_reciprocal_nonneg
    (P : Finset Nat) (level z : Real) (R : Nat)
    (hprime : forall p, p ∈ P -> p.Prime) :
    0 ≤ lowerRosserFailureRankTail P (fun p => (p : Real)⁻¹)
      level z R := by
  rw [lowerRosserFailureRankTail]
  apply Finset.sum_nonneg
  intro r hr
  exact lowerRosserFailureSumAtRank_reciprocal_nonneg P level z r hprime

end

end PrimesRestrictedDigits
