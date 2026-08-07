import BoundedGaps.Maynard.MaynardS1StarredCross

noncomputable section

/-!
# Restriction of the S1 cross sum to starred tuples

Every nonstarred summand vanishes through at least one lower Y factor.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance starredYDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def nontrivialStarredAuxiliaryYSum
    (H : Finset ℕ) (R : ℕ) (y : (H → ℕ) → ℝ) : ℝ :=
  ∑ s ∈ crossMoebiusTupleBox H R,
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ maynardDivisorTupleBox H R,
          if IsStarredCrossTuple H u s then
            (∏ h : H, (Nat.totient (u h) : ℝ)) *
              leftCrossYFactor H y u s * rightCrossYFactor H y u s
          else 0
    else 0

theorem nontrivialAuxiliaryYSum_eq_starred
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) :
    nontrivialAuxiliaryYSum H R y =
      nontrivialStarredAuxiliaryYSum H R y := by
  classical
  unfold nontrivialAuxiliaryYSum nontrivialStarredAuxiliaryYSum
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsNe : s ≠ oneCrossMoebiusTuple H
  · rw [if_pos hsNe, if_pos hsNe]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hstar : IsStarredCrossTuple H u s
    · rw [if_pos hstar]
    · rw [if_neg hstar]
      by_cases hl : leftCrossYFactor H y u s = 0
      · simp [hl]
      · have hr : rightCrossYFactor H y u s = 0 := by
          by_contra hr
          exact hstar (isStarredCrossTuple_of_yFactors_ne_zero hy hl hr)
        simp [hr]
  · rw [if_neg hsNe, if_neg hsNe]

theorem incompatibleSum_eq_neg_starredAuxiliaryYSum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) :
    incompatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) =
      -nontrivialStarredAuxiliaryYSum H R y := by
  rw [incompatibleSum_eq_neg_nontrivialAuxiliaryYSum hy]
  rw [nontrivialAuxiliaryYSum_eq_starred hy]

end BoundedGaps.Maynard
