import BoundedGaps.Maynard.MaynardS1YDiagonal
import BoundedGaps.Maynard.ConcreteS1Diagonal

namespace BoundedGaps.Maynard

open scoped BigOperators

/-! Remove the support predicate from the finite Y-diagonal summand. -/

theorem maynardYDiagonalSum_maynardYValue_eq_explicit
    {H : Finset ℕ} {R W : ℕ} {F : (H → ℝ) → ℝ} :
    maynardYDiagonalSum H R W (maynardYValue H R W F) =
      ∑ u ∈ maynardDivisorTupleSupport H R W,
        F (fun h => Real.log (u h) / Real.log R) ^ 2 /
          ∏ h : H, (Nat.totient (u h) : ℝ) := by
  classical
  unfold maynardYDiagonalSum
  apply Finset.sum_congr rfl
  intro u hu
  have hu' := isMaynardDivisorTuple_of_mem_support hu
  have hcond : divisorTupleProduct H u < R ∧
      Nat.Coprime (divisorTupleProduct H u) W ∧
      Squarefree (divisorTupleProduct H u) :=
    ⟨hu'.1, hu'.2.1, hu'.2.2⟩
  rw [maynardYValue, if_pos hcond]

theorem engelsmaMaynardYDiagonal_eq_explicit
    (alpha : ℝ) (N : ℕ) :
    engelsmaMaynardYDiagonal alpha N =
      ∑ u ∈ maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
        engelsmaSmallKCandidate
            (fun h => Real.log (u h) /
              Real.log (engelsmaMaynardRadius alpha N)) ^ 2 /
          ∏ h : BoundedGaps.engelsmaTuple,
            (Nat.totient (u h) : ℝ) := by
  unfold engelsmaMaynardYDiagonal
  exact maynardYDiagonalSum_maynardYValue_eq_explicit


end BoundedGaps.Maynard
