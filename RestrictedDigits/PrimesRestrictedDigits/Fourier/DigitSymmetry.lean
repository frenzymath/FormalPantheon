import PrimesRestrictedDigits.Fourier.DigitKernel
import Mathlib.Data.Fin.Rev

/-!
# Complement symmetry of the digit kernel

Reflecting every decimal digit `d` to `9 - d` multiplies the finite Fourier
sum by a unit phase and reverses its real frequency. This pairs excluded
digits without using the singular quotient form from the source.
-/

open scoped BigOperators
open ComplexConjugate

namespace PrimesRestrictedDigits

private noncomputable def symmetryPhase (d : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (d : ℝ) * x : ℝ) : ℂ) * Complex.I)

private theorem symmetryPhase_neg (d : ℕ) (x : ℝ) :
    symmetryPhase d (-x) = conj (symmetryPhase d x) := by
  rw [symmetryPhase, symmetryPhase, ← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

private noncomputable def symmetryKernelSum (a : Fin 10) (x : ℝ) : ℂ :=
  ∑ d : Fin 10, if d = a then 0 else symmetryPhase d.val x

private theorem allowed_sum_eq_symmetryKernelSum (a : Fin 10) (x : ℝ) :
    (∑ d ∈ allowedDecimalDigits a, symmetryPhase d x) =
      symmetryKernelSum a x := by
  rw [allowedDecimalDigits, Finset.sum_filter]
  calc
    (∑ d ∈ Finset.range 10,
        if d ≠ a.val then symmetryPhase d x else 0) =
        ∑ d ∈ Finset.range 10,
          if d = a.val then 0 else symmetryPhase d x := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hda : d = a.val <;> simp [hda]
    _ = ∑ d : Fin 10, if d.val = a.val then 0 else symmetryPhase d.val x := by
      symm
      exact Fin.sum_univ_eq_sum_range
        (fun d => if d = a.val then 0 else symmetryPhase d x) 10
    _ = symmetryKernelSum a x := by
      unfold symmetryKernelSum
      apply Finset.sum_congr rfl
      intro d hd
      simp only [Fin.ext_iff]

private theorem symmetryPhase_rev (d : Fin 10) (x : ℝ) :
    symmetryPhase d.rev.val x = symmetryPhase 9 x * symmetryPhase d.val (-x) := by
  rw [symmetryPhase, symmetryPhase, symmetryPhase, ← Complex.exp_add]
  congr 1
  have hd : d.val ≤ 9 := by omega
  rw [Fin.val_rev]
  norm_num
  ring

private theorem symmetryKernelSum_rev (a : Fin 10) (x : ℝ) :
    symmetryKernelSum a.rev x = symmetryPhase 9 x * symmetryKernelSum a (-x) := by
  unfold symmetryKernelSum
  rw [← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply, Fin.rev_eq_iff]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hda : d = a
  · simp [hda]
  · simp only [Fin.rev_rev, if_neg hda]
    rw [symmetryPhase_rev]

private theorem norm_symmetryKernelSum_rev (a : Fin 10) (x : ℝ) :
    ‖symmetryKernelSum a.rev x‖ = ‖symmetryKernelSum a (-x)‖ := by
  rw [symmetryKernelSum_rev, Complex.norm_mul]
  unfold symmetryPhase
  rw [Complex.norm_exp_ofReal_mul_I]
  simp

theorem digitKernel_neg (a : Fin 10) (x : ℝ) :
    digitKernel a (-x) = digitKernel a x := by
  unfold digitKernel
  congr 1
  change ‖∑ d ∈ allowedDecimalDigits a, symmetryPhase d (-x)‖ =
    ‖∑ d ∈ allowedDecimalDigits a, symmetryPhase d x‖
  simp_rw [symmetryPhase_neg]
  rw [← map_sum, Complex.norm_conj]

theorem digitKernel_rev (a : Fin 10) (x : ℝ) :
    digitKernel a.rev x = digitKernel a x := by
  calc
    digitKernel a.rev x = digitKernel a (-x) := by
      unfold digitKernel
      change (1 / 9 : ℝ) * ‖∑ d ∈ allowedDecimalDigits a.rev,
          symmetryPhase d x‖ =
        (1 / 9 : ℝ) * ‖∑ d ∈ allowedDecimalDigits a,
          symmetryPhase d (-x)‖
      rw [allowed_sum_eq_symmetryKernelSum, allowed_sum_eq_symmetryKernelSum,
        norm_symmetryKernelSum_rev]
    _ = digitKernel a x := digitKernel_neg a x

theorem oneSidedWindowMajorant_rev (a : Fin 10) (J : ℕ)
    (window : Fin (J + 1) → Fin 10) :
    oneSidedWindowMajorant a.rev J window =
      oneSidedWindowMajorant a J window := by
  unfold oneSidedWindowMajorant
  congr 1
  ext y
  constructor
  · rintro ⟨gamma, rfl⟩
    exact ⟨gamma, (digitKernel_rev a _).symm⟩
  · rintro ⟨gamma, rfl⟩
    exact ⟨gamma, digitKernel_rev a _⟩

end PrimesRestrictedDigits
