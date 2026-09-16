import PrimesRestrictedDigits.Fourier.TransferMatrix

/-!
# Recursive matrix path sums

The future-row/previous-column orientation of the digit transition matrix is
captured by a vector-valued recurrence. This is the finite algebraic form of
the expanded matrix paths in the source.
-/

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

def matrixRowPathSum {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℝ) : ℕ → ι → ℝ
  | 0 => 1
  | steps + 1 => matrix *ᵥ matrixRowPathSum matrix steps

theorem matrixRowPathSum_succ_apply {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℝ) (steps : ℕ) (future : ι) :
    matrixRowPathSum matrix (steps + 1) future =
      ∑ previous, matrix future previous *
        matrixRowPathSum matrix steps previous := by
  rfl

theorem matrixRowPathSum_eq_pow_mulVec_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι ℝ) (steps : ℕ) :
    matrixRowPathSum matrix steps = matrix ^ steps *ᵥ (1 : ι → ℝ) := by
  induction steps with
  | zero => simp [matrixRowPathSum]
  | succ steps ih =>
      rw [matrixRowPathSum, ih, Matrix.mulVec_mulVec, pow_succ']

theorem matrixRowPathSum_eq_rowSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι ℝ) (steps : ℕ) (future : ι) :
    matrixRowPathSum matrix steps future =
      ∑ previous, (matrix ^ steps) future previous := by
  rw [matrixRowPathSum_eq_pow_mulVec_one]
  rw [Matrix.mulVec]
  simp only [dotProduct, Pi.one_apply, mul_one]

theorem matrixRowPathSum_nonneg {ι : Type*} [Fintype ι]
    {matrix : Matrix ι ι ℝ} (hmatrix : ∀ i j, 0 ≤ matrix i j) :
    ∀ steps future, 0 ≤ matrixRowPathSum matrix steps future := by
  intro steps
  induction steps with
  | zero =>
      intro future
      simp [matrixRowPathSum]
  | succ steps ih =>
      intro future
      rw [matrixRowPathSum, Matrix.mulVec]
      apply Finset.sum_nonneg
      intro previous hprevious
      exact mul_nonneg (hmatrix future previous) (ih previous)

end PrimesRestrictedDigits
