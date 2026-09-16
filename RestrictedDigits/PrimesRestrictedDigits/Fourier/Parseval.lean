import Mathlib.Analysis.Fourier.ZMod

/-!
# Finite Parseval for the `ZMod` transform

The paper uses this finite-grid identity in Section 12 (source key
`MAYNARD-PRD-PUBLISHED`). Mathlib's `ZMod.dft` is unnormalized, so the scale
factor is the modulus. The continuous Parseval statement used elsewhere in the
paper is a separate analytic node.
-/

open scoped BigOperators ComplexConjugate ZMod
open Finset AddChar

namespace PrimesRestrictedDigits

variable {N : ℕ} [NeZero N]

private lemma sum_mul_dft_neg (f g : ZMod N → ℂ) :
    ∑ k, f k * ZMod.dft g (-k) = ∑ j, g j * ZMod.dft f (-j) := by
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sum]
  rw [sum_comm]
  congr 1 with j
  congr 1 with k
  simp only [mul_neg, neg_neg, mul_comm]
  ring

/-- Bilinear Fourier inversion with the unnormalized `ZMod.dft`. -/
theorem sum_dft_neg_mul_dft (f g : ZMod N → ℂ) :
    (∑ k, ZMod.dft f (-k) * ZMod.dft g k) =
      (N : ℂ) * ∑ j, f j * g j := by
  calc
    (∑ k, ZMod.dft f (-k) * ZMod.dft g k) =
        ∑ k, ZMod.dft f k * ZMod.dft g (-k) := by
      refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ ?_
      intro k
      simp
    _ = ∑ j, g j * ZMod.dft (ZMod.dft f) (-j) :=
      sum_mul_dft_neg (ZMod.dft f) g
    _ = (N : ℂ) * ∑ j, f j * g j := by
      rw [ZMod.dft_dft]
      simp only [smul_eq_mul, neg_neg]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The standard `Fin` representative agrees with its natural cast in `ZMod`. -/
theorem finEquiv_apply_eq_natCast_val
    {X : Nat} [NeZero X] (i : Fin X) :
    (ZMod.finEquiv X).toEquiv i = (i.val : ZMod X) := by
  apply ZMod.val_injective X
  rw [ZMod.val_natCast_of_lt i.isLt]
  cases X with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ X => rfl

private lemma conj_dft (Φ : ZMod N → ℂ) (k : ZMod N) :
    conj (ZMod.dft Φ k) = ZMod.dft (fun j ↦ conj (Φ j)) (-k) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul,
    ← AddChar.map_neg_eq_conj, neg_neg, mul_neg]

private lemma sum_conj_dft_mul_dft (Φ : ZMod N → ℂ) :
    ∑ k, conj (ZMod.dft Φ k) * ZMod.dft Φ k =
      (N : ℂ) * ∑ j, conj (Φ j) * Φ j := by
  calc
    ∑ k, conj (ZMod.dft Φ k) * ZMod.dft Φ k =
        ∑ k, ZMod.dft Φ k * ZMod.dft (fun j ↦ conj (Φ j)) (-k) := by
          congr 1 with k
          rw [conj_dft, mul_comm]
    _ = ∑ j, conj (Φ j) * ZMod.dft (ZMod.dft Φ) (-j) :=
          sum_mul_dft_neg (ZMod.dft Φ) (fun j ↦ conj (Φ j))
    _ = (N : ℂ) * ∑ j, conj (Φ j) * Φ j := by
          rw [ZMod.dft_dft]
          simp only [smul_eq_mul, neg_neg]
          rw [Finset.mul_sum]
          congr 1 with j
          ring

theorem sum_normSq_dft (Φ : ZMod N → ℂ) :
    ∑ k, Complex.normSq (ZMod.dft Φ k) =
      (N : ℝ) * ∑ j, Complex.normSq (Φ j) := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.normSq_eq_conj_mul_self] using sum_conj_dft_mul_dft Φ

theorem sum_norm_sq_dft (Φ : ZMod N → ℂ) :
    ∑ k, ‖ZMod.dft Φ k‖ ^ 2 =
      (N : ℝ) * ∑ j, ‖Φ j‖ ^ 2 := by
  simpa only [Complex.normSq_eq_norm_sq] using sum_normSq_dft Φ

end PrimesRestrictedDigits
