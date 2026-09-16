import PrimesRestrictedDigits.Fourier.TransferMatrix

/-!
# Entrywise upper bounds for transition matrices

An exact analytic transition matrix may be bounded entrywise by a rational
certificate matrix. These lemmas propagate that bound through powers and row
sums before applying the subeigenvector certificate.
-/

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

section Multiplication

variable {ι : Type*} [Fintype ι]

private theorem matrix_mul_le_mul_of_nonneg
    {A B C D : Matrix ι ι ℝ}
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j)
    (hAC : ∀ i j, A i j ≤ C i j) (hBD : ∀ i j, B i j ≤ D i j) :
    ∀ i j, (A * B) i j ≤ (C * D) i j := by
  intro i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_le_sum
  intro index hindex
  exact mul_le_mul (hAC i index) (hBD index j)
    (hB index j) (hC i index)

end Multiplication

section Powers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_pow_le_pow_of_nonneg_of_le {M U : Matrix ι ι ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hMU : ∀ i j, M i j ≤ U i j)
    (k : ℕ) : ∀ i j, (M ^ k) i j ≤ (U ^ k) i j := by
  have hU : ∀ i j, 0 ≤ U i j := fun i j => (hM i j).trans (hMU i j)
  induction k with
  | zero =>
      intro i j
      rfl
  | succ k ih =>
      rw [pow_succ, pow_succ]
      intro i j
      exact matrix_mul_le_mul_of_nonneg hM
        (Matrix.pow_apply_nonneg hU k) ih hMU i j

theorem rowSum_pow_le_of_entrywise_upper_subEigen
    {M U : Matrix ι ι ℝ} {v : ι → ℝ} {rho : ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hMU : ∀ i j, M i j ≤ U i j)
    (hv : ∀ i, 1 ≤ v i) (hrho : 0 ≤ rho)
    (hsub : (U *ᵥ v) ≤ rho • v) (k : ℕ) (i : ι) :
    ∑ j, (M ^ k) i j ≤ rho ^ k * v i := by
  calc
    (∑ j, (M ^ k) i j) ≤ ∑ j, (U ^ k) i j := by
      apply Finset.sum_le_sum
      intro j hj
      exact matrix_pow_le_pow_of_nonneg_of_le hM hMU k i j
    _ ≤ rho ^ k * v i := by
      apply rowSum_pow_le_of_subEigen
      · intro row column
        exact (hM row column).trans (hMU row column)
      · exact hv
      · exact hrho
      · exact hsub

end Powers

end PrimesRestrictedDigits
