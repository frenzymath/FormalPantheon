import BoundedGaps.Maynard.MaynardS1CrossLowerTuples

noncomputable section

/-!
# Y-substitution in the nontrivial S1 cross sum

Both factored coefficient sums are replaced by their exact lower-tuple Y
expressions.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance crossYDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def nontrivialAuxiliaryYSum
    (H : Finset ℕ) (R : ℕ) (y : (H → ℕ) → ℝ) : ℝ :=
  ∑ s ∈ crossMoebiusTupleBox H R,
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ maynardDivisorTupleBox H R,
          (∏ h : H, (Nat.totient (u h) : ℝ)) *
            leftCrossYFactor H y u s * rightCrossYFactor H y u s
    else 0

theorem factoredSum_eq_nontrivialAuxiliaryYSum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) :
    nontrivialAuxiliaryFactoredSum H R
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) =
      nontrivialAuxiliaryYSum H R y := by
  classical
  unfold nontrivialAuxiliaryFactoredSum nontrivialAuxiliaryYSum
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsNe : s ≠ oneCrossMoebiusTuple H
  · rw [if_pos hsNe, if_pos hsNe]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [left_factoredCoefficientSum_eq_yFactor hy hu hs]
    rw [right_factoredCoefficientSum_eq_yFactor hy hu hs]
  · rw [if_neg hsNe, if_neg hsNe]

theorem nontrivialAuxiliaryMobiusSum_eq_ySum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) :
    nontrivialAuxiliaryMobiusSum H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) =
      nontrivialAuxiliaryYSum H R y := by
  rw [nontrivialAuxiliaryMobiusSum_eq_factoredSum
    (fun d hd => isMaynardDivisorTuple_of_mem_support hd)]
  exact factoredSum_eq_nontrivialAuxiliaryYSum hy

theorem incompatibleSum_eq_neg_nontrivialAuxiliaryYSum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) :
    incompatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) =
      -nontrivialAuxiliaryYSum H R y := by
  rw [incompatibleSum_eq_neg_nontrivialAuxiliaryMobiusSum
    (fun d hd => isMaynardDivisorTuple_of_mem_support hd)]
  rw [nontrivialAuxiliaryMobiusSum_eq_ySum hy]

end BoundedGaps.Maynard
