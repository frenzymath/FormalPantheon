import Waring.Analytic.ChenTenCumulativeParameters

/-!
# Finite-sum form of the double shift count

This file rewrites `scratchShiftSquareCount` as a pair of sums indexed by
`Fin`, matching the indexing used by the analytic averaging identities.
-/

set_option autoImplicit false

namespace Waring.Analytic

open scoped BigOperators

noncomputable section

private theorem sum_Icc_one_eq_fin
    {E : Type*} [AddCommMonoid E] (M : Nat) (f : Nat → E) :
    (∑ u ∈ Finset.Icc 1 M, f u) = ∑ j : Fin M, f j.val.succ := by
  have hset : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  rw [Nat.add_sub_cancel]
  simpa [Nat.add_comm, Nat.succ_eq_add_one] using
    (Fin.sum_univ_eq_sum_range (fun u => f (u + 1)) M).symm

/-- Casting the shift-square count to `Complex` gives the analytic double `Fin` sum. -/
theorem scratchShiftSquareCount_cast_eq_fin_sum
    (P N M : Nat) :
    (scratchShiftSquareCount P N M : Complex) =
      ∑ j : Fin M, ∑ k : Fin M,
        (positiveFifthPowerRepresentationCount 15 P
          (N - j.val.succ - k.val.succ) : Complex) := by
  unfold scratchShiftSquareCount scratchShiftSet
  push_cast
  rw [sum_Icc_one_eq_fin]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sum_Icc_one_eq_fin]

end

end Waring.Analytic
