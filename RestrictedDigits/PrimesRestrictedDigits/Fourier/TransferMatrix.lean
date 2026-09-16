import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Module.Field

/-!
# Finite transfer-matrix growth from a subeigenvector

This is the exact algebraic certificate interface intended to replace the
uncertified Perron-Frobenius/numerical step in the Markov moment argument of
`MAYNARD-PRD-PUBLISHED`, Lemma 10.2. It makes no source-specific numerical
claim.
-/

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

section Monotonicity

variable {ι : Type*} [Fintype ι]

theorem mulVec_le_mulVec_of_nonneg {M : Matrix ι ι ℝ}
    (hM : ∀ i j, 0 ≤ M i j) {v w : ι → ℝ} (hvw : v ≤ w) :
    (M *ᵥ v) ≤ (M *ᵥ w) := by
  intro i
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (hvw j) (hM i j)

end Monotonicity

section Powers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pow_mulVec_le_of_subEigen {M : Matrix ι ι ℝ} {v : ι → ℝ} {rho : ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hrho : 0 ≤ rho)
    (hsub : (M *ᵥ v) ≤ rho • v) (k : ℕ) :
    (M ^ k *ᵥ v) ≤ rho ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec]
      calc
        M ^ k *ᵥ (M *ᵥ v) ≤ M ^ k *ᵥ (rho • v) :=
          mulVec_le_mulVec_of_nonneg
            (fun i j => Matrix.pow_apply_nonneg hM k i j) hsub
        _ = rho • (M ^ k *ᵥ v) := Matrix.mulVec_smul _ _ _
        _ ≤ rho • (rho ^ k • v) := smul_le_smul_of_nonneg_left ih hrho
        _ = rho ^ (k + 1) • v := by
          ext i
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [pow_succ]
          ring

theorem rowSum_pow_le_of_subEigen {M : Matrix ι ι ℝ} {v : ι → ℝ} {rho : ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 1 ≤ v i) (hrho : 0 ≤ rho)
    (hsub : (M *ᵥ v) ≤ rho • v) (k : ℕ) (i : ι) :
    ∑ j, (M ^ k) i j ≤ rho ^ k * v i := by
  have hmono : (M ^ k *ᵥ (1 : ι → ℝ)) ≤ M ^ k *ᵥ v :=
    mulVec_le_mulVec_of_nonneg
      (fun row j => Matrix.pow_apply_nonneg hM k row j) hv
  have hiter := pow_mulVec_le_of_subEigen hM hrho hsub k
  calc
    (∑ j, (M ^ k) i j) = (M ^ k *ᵥ (1 : ι → ℝ)) i := by
      rw [Matrix.mulVec]
      simp only [dotProduct, Pi.one_apply, mul_one]
    _ ≤ (M ^ k *ᵥ v) i := hmono i
    _ ≤ (rho ^ k • v) i := hiter i
    _ = rho ^ k * v i := by simp

end Powers

end PrimesRestrictedDigits
