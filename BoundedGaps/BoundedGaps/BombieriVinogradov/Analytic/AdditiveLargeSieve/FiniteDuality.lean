import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Finite complex transpose duality

This file proves the finite squared-`ell2` transpose principle used in
Montgomery--Vaughan's additive large-sieve argument. See SEM-448.
-/

open scoped BigOperators ComplexConjugate

namespace BoundedGaps.Maynard.AdditiveLargeSieve

private lemma norm_sum_mul_sq_le (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have hnorm :
      ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖a i * b i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by simp_rw [Complex.norm_mul]
  calc
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
        (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
        mul_nonneg (norm_nonneg (a i)) (norm_nonneg (b i)))).mpr hnorm
    _ ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖)

private lemma complex_norm_sq_cast (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

private def transposeSum
    (s : Finset ι) (C : ι → κ → ℂ) (v : ι → ℂ) (n : κ) : ℂ :=
  ∑ r ∈ s, C r n * v r

private def matrixSum
    (t : Finset κ) (C : ι → κ → ℂ) (w : κ → ℂ) (r : ι) : ℂ :=
  ∑ n ∈ t, C r n * w n

private lemma energy_nonneg (s : Finset ι) (f : ι → ℂ) :
    0 ≤ ∑ i ∈ s, ‖f i‖ ^ 2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg ‖f i‖

private lemma matrix_energy_as_pairing
    (s : Finset ι) (t : Finset κ) (C : ι → κ → ℂ) (w : κ → ℂ) :
    (((∑ r ∈ s, ‖matrixSum t C w r‖ ^ 2 : ℝ) : ℂ)) =
      ∑ n ∈ t, w n * ∑ r ∈ s, C r n * star (matrixSum t C w r) := by
  calc
    (((∑ r ∈ s, ‖matrixSum t C w r‖ ^ 2 : ℝ) : ℂ)) =
        ∑ r ∈ s, star (matrixSum t C w r) * matrixSum t C w r := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro r _
      exact complex_norm_sq_cast _
    _ = ∑ r ∈ s, ∑ n ∈ t,
          star (matrixSum t C w r) * (C r n * w n) := by
      simp_rw [matrixSum, Finset.mul_sum]
    _ = ∑ n ∈ t, ∑ r ∈ s,
          star (matrixSum t C w r) * (C r n * w n) := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ t, ∑ r ∈ s,
          w n * (C r n * star (matrixSum t C w r)) := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ n ∈ t, w n * ∑ r ∈ s,
          C r n * star (matrixSum t C w r) := by
      simp_rw [Finset.mul_sum]

/-- Finite complex transpose duality for a squared `ℓ2` bound. The
coefficient conjugation is placed in the test vector, so the matrix itself is
transposed without conjugating its entries (SEM-448). -/
theorem finite_transpose_l2_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (C : ι → κ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hdual : ∀ v : ι → ℂ,
      (∑ n, ‖∑ r, C r n * v r‖ ^ 2) ≤
        A * ∑ r, ‖v r‖ ^ 2)
    (w : κ → ℂ) :
    (∑ r, ‖∑ n, C r n * w n‖ ^ 2) ≤
      A * ∑ n, ‖w n‖ ^ 2 := by
  let z : ι → ℂ := matrixSum Finset.univ C w
  let v : ι → ℂ := fun r => star (z r)
  let L : ℝ := ∑ r, ‖z r‖ ^ 2
  let W : ℝ := ∑ n, ‖w n‖ ^ 2
  let R : ℝ := ∑ n, ‖transposeSum Finset.univ C v n‖ ^ 2
  have hL : 0 ≤ L := energy_nonneg Finset.univ z
  have hW : 0 ≤ W := energy_nonneg Finset.univ w
  have hpair : (L : ℂ) = ∑ n, w n * transposeSum Finset.univ C v n := by
    dsimp only [L, v, z, transposeSum]
    rw [matrix_energy_as_pairing]
  have hcs : L ^ 2 ≤ W * R := by
    calc
      L ^ 2 = ‖(L : ℂ)‖ ^ 2 := by rw [Complex.norm_of_nonneg hL]
      _ = ‖∑ n, w n * transposeSum Finset.univ C v n‖ ^ 2 := by rw [hpair]
      _ ≤ W * R := norm_sum_mul_sq_le Finset.univ w
        (transposeSum Finset.univ C v)
  have hR : R ≤ A * L := by
    calc
      R ≤ A * ∑ r, ‖v r‖ ^ 2 := by
        dsimp only [R, transposeSum]
        exact hdual v
      _ = A * L := by
        dsimp only [L, v]
        rw [Complex.star_def]
        simp only [Complex.norm_conj]
  have hsq : L ^ 2 ≤ (A * W) * L := by
    calc
      L ^ 2 ≤ W * R := hcs
      _ ≤ W * (A * L) := mul_le_mul_of_nonneg_left hR hW
      _ = (A * W) * L := by ring
  have hmain : L ≤ A * W := by
    rcases hL.eq_or_lt with hLzero | hLpos
    · rw [← hLzero]
      exact mul_nonneg hA hW
    · rw [← mul_le_mul_iff_right₀ hLpos]
      simpa only [pow_two, mul_assoc, mul_comm] using hsq
  simpa only [L, W, z, matrixSum] using hmain

end BoundedGaps.Maynard.AdditiveLargeSieve
