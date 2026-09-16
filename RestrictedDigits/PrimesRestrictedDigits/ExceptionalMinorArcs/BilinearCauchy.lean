import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearKernel
import PrimesRestrictedDigits.Fourier.KernelNormSq
import Mathlib.Analysis.Real.Sqrt

/-!
# Finite Cauchy expansion for bilinear phase sums

This file isolates the exact complex conjugation and phase sign in the second-moment step of
repaired Lemma 13.1.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem conjugate_phase_product
    {ι : Type*} (c : ι -> Complex) (theta : ι -> Real)
    (m : Nat) (i j : ι) :
    ((starRingEnd Complex)
          (c i * majorArcPhase ((m : Real) * theta i)) *
        (c j * majorArcPhase ((m : Real) * theta j))).re =
      ((starRingEnd Complex) (c i) * c j *
        majorArcPhase ((m : Real) * (theta j - theta i))).re := by
  have hconj :
      (starRingEnd Complex)
          (majorArcPhase ((m : Real) * theta i)) =
        majorArcPhase (-((m : Real) * theta i)) := by
    simpa only using
      (majorArcPhase_neg_eq_conj ((m : Real) * theta i)).symm
  rw [map_mul, hconj]
  congr 1
  calc
    ((starRingEnd Complex) (c i) *
        majorArcPhase (-((m : Real) * theta i))) *
          (c j * majorArcPhase ((m : Real) * theta j)) =
        (starRingEnd Complex) (c i) * c j *
          (majorArcPhase (-((m : Real) * theta i)) *
            majorArcPhase ((m : Real) * theta j)) := by ring
    _ = (starRingEnd Complex) (c i) * c j *
        majorArcPhase ((m : Real) * (theta j - theta i)) := by
      rw [← majorArcPhase_add_eq_mul]
      congr 1
      ring_nf

/-- Exact second-moment expansion. The phase is `theta j - theta i`; this is
the sign dictated by complex conjugation. -/
theorem sum_norm_sq_sum_mul_phase_eq
    {ι : Type*} (M : Finset Nat) (I : Finset ι)
    (c : ι -> Complex) (theta : ι -> Real) :
    (∑ m ∈ M,
      ‖∑ i ∈ I,
        c i * majorArcPhase ((m : Real) * theta i)‖ ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I,
        (((starRingEnd Complex) (c i) * c j) *
          (∑ m ∈ M,
            majorArcPhase ((m : Real) * (theta j - theta i)))).re := by
  calc
    (∑ m ∈ M,
        ‖∑ i ∈ I,
          c i * majorArcPhase ((m : Real) * theta i)‖ ^ 2) =
        ∑ m ∈ M,
          Complex.normSq
            (∑ i ∈ I,
              c i * majorArcPhase ((m : Real) * theta i)) := by
      apply Finset.sum_congr rfl
      intro m _
      exact Complex.sq_norm _
    _ = ∑ m ∈ M, ∑ i ∈ I, ∑ j ∈ I,
        ((starRingEnd Complex)
            (c i * majorArcPhase ((m : Real) * theta i)) *
          (c j * majorArcPhase ((m : Real) * theta j))).re := by
      apply Finset.sum_congr rfl
      intro m _
      exact complexNormSq_sum_double I
        (fun i => c i * majorArcPhase ((m : Real) * theta i))
    _ = ∑ m ∈ M, ∑ i ∈ I, ∑ j ∈ I,
        ((starRingEnd Complex) (c i) * c j *
          majorArcPhase ((m : Real) * (theta j - theta i))).re := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact conjugate_phase_product c theta m i j
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ m ∈ M,
        ((starRingEnd Complex) (c i) * c j *
          majorArcPhase ((m : Real) * (theta j - theta i))).re := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i ∈ I, ∑ j ∈ I,
        (((starRingEnd Complex) (c i) * c j) *
          (∑ m ∈ M,
            majorArcPhase ((m : Real) * (theta j - theta i)))).re := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← Complex.re_sum, Finset.mul_sum]

/-- Triangle inequality applied only after the exact second-moment phase sum
has been assembled. -/
theorem sum_norm_sq_sum_mul_phase_le
    {ι : Type*} (M : Finset Nat) (I : Finset ι)
    (c : ι -> Complex) (theta : ι -> Real) :
    (∑ m ∈ M,
      ‖∑ i ∈ I,
        c i * majorArcPhase ((m : Real) * theta i)‖ ^ 2) <=
      ∑ i ∈ I, ∑ j ∈ I,
        ‖c i‖ * ‖c j‖ *
          ‖∑ m ∈ M,
            majorArcPhase ((m : Real) * (theta j - theta i))‖ := by
  rw [sum_norm_sq_sum_mul_phase_eq]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    (((starRingEnd Complex) (c i) * c j) *
        (∑ m ∈ M,
          majorArcPhase ((m : Real) * (theta j - theta i)))).re <=
        ‖((starRingEnd Complex) (c i) * c j) *
          (∑ m ∈ M,
            majorArcPhase ((m : Real) * (theta j - theta i)))‖ :=
      Complex.re_le_norm _
    _ = ‖c i‖ * ‖c j‖ *
        ‖∑ m ∈ M,
          majorArcPhase ((m : Real) * (theta j - theta i))‖ := by
      simp only [norm_mul, RCLike.norm_conj]

/-- Finite complex Cauchy--Schwarz after taking norms termwise. -/
theorem norm_sum_mul_le_sqrt_mul_sqrt
    (M : Finset Nat) (beta T : Nat -> Complex) :
    ‖∑ m ∈ M, beta m * T m‖ <=
      Real.sqrt (∑ m ∈ M, ‖beta m‖ ^ 2) *
        Real.sqrt (∑ m ∈ M, ‖T m‖ ^ 2) := by
  calc
    ‖∑ m ∈ M, beta m * T m‖ <=
        ∑ m ∈ M, ‖beta m * T m‖ := norm_sum_le _ _
    _ = ∑ m ∈ M, ‖beta m‖ * ‖T m‖ := by
      apply Finset.sum_congr rfl
      intro m _
      rw [norm_mul]
    _ <= Real.sqrt (∑ m ∈ M, ‖beta m‖ ^ 2) *
        Real.sqrt (∑ m ∈ M, ‖T m‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt M
        (fun m => ‖beta m‖) (fun m => ‖T m‖)

end PrimesRestrictedDigits
