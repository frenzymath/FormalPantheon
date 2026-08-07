import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert.EigenvectorCancellation
import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert.TrigonometricIdentity
import BoundedGaps.BombieriVinogradov.Analytic.CircleReciprocalSquarePacking
import BoundedGaps.BombieriVinogradov.Analytic.CosecantPointwise

/-!
# The coefficient-one analytic estimate

This file combines the SEM-445 pointwise majorant with the SEM-446 circle
packing theorem. The factors `3 / pi^2` and `pi^2 / 3` cancel exactly, closing
the normalized eigenvalue estimate in MontgomeryVaughanHilbert1974, p. 80.
-/

open scoped ComplexConjugate
open Finset Metric

noncomputable section

namespace BoundedGaps.Maynard.CosecantHilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma sum_erase_eq_sum_ite_real (a : ι) (f : ι → ℝ) :
    ∑ b ∈ Finset.univ.erase a, f b = ∑ b, if b = a then 0 else f b := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_erase, ne_eq, Finset.mem_univ]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩

private lemma offDiagonal_sum_comm_real (f : ι → ι → ℝ) :
    (∑ s, ∑ r ∈ Finset.univ.erase s, f r s) =
      ∑ r, ∑ s ∈ Finset.univ.erase r, f r s := by
  simp_rw [sum_erase_eq_sum_ite_real]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : r = s
  · subst s
    simp
  · simp [h, Ne.symm h]

omit [Fintype ι] [DecidableEq ι] in
private lemma cotangentPiDiff_eq_cot (x : ι → ℝ) (r s : ι) :
    cotangentPiDiff x r s = Real.cot (Real.pi * (x r - x s)) := by
  rw [cotangentPiDiff, Real.cot_eq_cos_div_sin, div_eq_mul_inv]

private def cscCotangentWeight (x : ι → ℝ) (r s : ι) : ℝ :=
  |cotangentPiDiff x r s * cosecantPi (x r - x s)|

private lemma cosecantPi_neg (a : ℝ) :
    cosecantPi (-a) = -cosecantPi a := by
  rw [cosecantPi, cosecantPi, mul_neg, Real.sin_neg, inv_neg]

omit [Fintype ι] [DecidableEq ι] in
private lemma cscCotangentWeight_comm (x : ι → ℝ) (r s : ι) :
    cscCotangentWeight x r s = cscCotangentWeight x s r := by
  rw [cscCotangentWeight, cscCotangentWeight, cotangentPiDiff_swap,
    show x s - x r = -(x r - x s) by ring, cosecantPi_neg]
  congr 1
  ring

omit [Fintype ι] [DecidableEq ι] in
private lemma csc_sq_add_two_weight_le
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s →
      δ ≤ dist (x r : UnitAddCircle) (x s : UnitAddCircle))
    {r s : ι} (hrs : r ≠ s) :
    cosecantPi (x r - x s) ^ 2 + 2 * cscCotangentWeight x r s ≤
      3 / (Real.pi ^ 2 *
        dist (x r : UnitAddCircle) (x s : UnitAddCircle) ^ 2) := by
  have hpoint := cosecant_cotangent_majorant (x r - x s)
    (quotientDiff_ne_zero x hδ hsep hrs)
  have hnorm : ‖((x r - x s : ℝ) : UnitAddCircle)‖ =
      dist (x r : UnitAddCircle) (x s : UnitAddCircle) := by
    change ‖(x r : UnitAddCircle) - (x s : UnitAddCircle)‖ = _
    rw [dist_eq_norm]
  rw [hnorm] at hpoint
  rw [cscCotangentWeight, cotangentPiDiff_eq_cot]
  exact hpoint

private lemma sum_csc_sq_add_two_weight_le_inv_sq
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s →
      δ ≤ dist (x r : UnitAddCircle) (x s : UnitAddCircle))
    (s : ι) :
    (∑ r ∈ Finset.univ.erase s,
      (cosecantPi (x r - x s) ^ 2 + 2 * cscCotangentWeight x r s)) ≤
      δ⁻¹ ^ 2 := by
  calc
    (∑ r ∈ Finset.univ.erase s,
      (cosecantPi (x r - x s) ^ 2 + 2 * cscCotangentWeight x r s)) ≤
        ∑ r ∈ Finset.univ.erase s,
          3 / (Real.pi ^ 2 *
            dist (x r : UnitAddCircle) (x s : UnitAddCircle) ^ 2) := by
      apply Finset.sum_le_sum
      intro r hr
      exact csc_sq_add_two_weight_le x hδ hsep (Finset.ne_of_mem_erase hr)
    _ = (3 / Real.pi ^ 2) *
        ∑ r ∈ Finset.univ.erase s,
          (dist (x s : UnitAddCircle) (x r : UnitAddCircle) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [dist_comm (x s : UnitAddCircle) (x r : UnitAddCircle)]
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring
    _ ≤ (3 / Real.pi ^ 2) * (Real.pi ^ 2 / (3 * δ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_inv_sq_circle_dist_le
          (fun r => (x r : UnitAddCircle)) hδ hsep s
      · positivity
    _ = δ⁻¹ ^ 2 := by
      field_simp [ne_of_gt Real.pi_pos, hδ.ne']

private lemma montgomeryVaughanS1_re_eq (x : ι → ℝ) (u : ι → ℂ) :
    (montgomeryVaughanS1 x u).re =
      ∑ r, ∑ s ∈ Finset.univ.erase r,
        ‖u s‖ ^ 2 * cosecantPi (x r - x s) ^ 2 := by
  rw [montgomeryVaughanS1, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show star (u s) * u s = (‖u s‖ ^ 2 : ℂ) by
    exact RCLike.conj_mul (u s)]
  rw [cosecantPi]
  norm_cast

private lemma montgomeryVaughanS5_re_le (x : ι → ℝ) (u : ι → ℂ) :
    (montgomeryVaughanS5 x u).re ≤
      ∑ s, ∑ r ∈ Finset.univ.erase s,
        ‖u s‖ * ‖u r‖ * cscCotangentWeight x r s := by
  rw [montgomeryVaughanS5, Complex.re_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply (Complex.re_le_norm _).trans_eq
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
  rw [cscCotangentWeight, cosecantPi, cotangentPiDiff, abs_mul]
  simp only [abs_mul]
  ring

private lemma two_mul_sum_norm_mul_norm_weight_le
    (x : ι → ℝ) (u : ι → ℂ) :
    2 * (∑ s, ∑ r ∈ Finset.univ.erase s,
      ‖u s‖ * ‖u r‖ * cscCotangentWeight x r s) ≤
      2 * (∑ s, ∑ r ∈ Finset.univ.erase s,
        ‖u s‖ ^ 2 * cscCotangentWeight x r s) := by
  let D := ∑ s, ∑ r ∈ Finset.univ.erase s,
    ‖u s‖ ^ 2 * cscCotangentWeight x r s
  have hyoung :
      2 * (∑ s, ∑ r ∈ Finset.univ.erase s,
        ‖u s‖ * ‖u r‖ * cscCotangentWeight x r s) ≤
        ∑ s, ∑ r ∈ Finset.univ.erase s,
          (‖u s‖ ^ 2 + ‖u r‖ ^ 2) * cscCotangentWeight x r s := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    calc
      2 * (‖u s‖ * ‖u r‖ * cscCotangentWeight x r s) =
          (2 * ‖u s‖ * ‖u r‖) * cscCotangentWeight x r s := by ring
      _ ≤ (‖u s‖ ^ 2 + ‖u r‖ ^ 2) * cscCotangentWeight x r s :=
        mul_le_mul_of_nonneg_right (two_mul_le_add_sq _ _) (abs_nonneg _)
  have hswap :
      (∑ s, ∑ r ∈ Finset.univ.erase s,
        ‖u r‖ ^ 2 * cscCotangentWeight x r s) = D := by
    calc
      (∑ s, ∑ r ∈ Finset.univ.erase s,
        ‖u r‖ ^ 2 * cscCotangentWeight x r s) =
          ∑ r, ∑ s ∈ Finset.univ.erase r,
            ‖u r‖ ^ 2 * cscCotangentWeight x r s :=
        offDiagonal_sum_comm_real
          (fun r s => ‖u r‖ ^ 2 * cscCotangentWeight x r s)
      _ = D := by
        dsimp [D]
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        rw [cscCotangentWeight_comm]
  calc
    2 * (∑ s, ∑ r ∈ Finset.univ.erase s,
      ‖u s‖ * ‖u r‖ * cscCotangentWeight x r s) ≤
        ∑ s, ∑ r ∈ Finset.univ.erase s,
          (‖u s‖ ^ 2 + ‖u r‖ ^ 2) * cscCotangentWeight x r s := hyoung
    _ = D + D := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [hswap]
    _ = 2 * D := by ring
    _ = 2 * (∑ s, ∑ r ∈ Finset.univ.erase s,
        ‖u s‖ ^ 2 * cscCotangentWeight x r s) := rfl

private lemma montgomeryVaughan_energy_le
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s →
      δ ≤ dist (x r : UnitAddCircle) (x s : UnitAddCircle))
    (u : ι → ℂ) (hnorm : (∑ r, ‖u r‖ ^ 2) = 1) :
    (montgomeryVaughanS1 x u).re + 2 * (montgomeryVaughanS5 x u).re ≤
      δ⁻¹ ^ 2 := by
  have hS1 : (montgomeryVaughanS1 x u).re =
      ∑ s, ∑ r ∈ Finset.univ.erase s,
        ‖u s‖ ^ 2 * cosecantPi (x r - x s) ^ 2 := by
    rw [montgomeryVaughanS1_re_eq]
    exact (offDiagonal_sum_comm_real
      (fun r s => ‖u s‖ ^ 2 * cosecantPi (x r - x s) ^ 2)).symm
  have hS5 : 2 * (montgomeryVaughanS5 x u).re ≤
      2 * (∑ s, ∑ r ∈ Finset.univ.erase s,
        ‖u s‖ ^ 2 * cscCotangentWeight x r s) := by
    calc
      2 * (montgomeryVaughanS5 x u).re ≤
          2 * (∑ s, ∑ r ∈ Finset.univ.erase s,
            ‖u s‖ * ‖u r‖ * cscCotangentWeight x r s) :=
        mul_le_mul_of_nonneg_left (montgomeryVaughanS5_re_le x u) (by norm_num)
      _ ≤ 2 * (∑ s, ∑ r ∈ Finset.univ.erase s,
          ‖u s‖ ^ 2 * cscCotangentWeight x r s) :=
        two_mul_sum_norm_mul_norm_weight_le x u
  calc
    (montgomeryVaughanS1 x u).re + 2 * (montgomeryVaughanS5 x u).re ≤
        (montgomeryVaughanS1 x u).re +
          2 * (∑ s, ∑ r ∈ Finset.univ.erase s,
            ‖u s‖ ^ 2 * cscCotangentWeight x r s) :=
      add_le_add_right hS5 _
    _ = ∑ s, ∑ r ∈ Finset.univ.erase s,
        ‖u s‖ ^ 2 *
          (cosecantPi (x r - x s) ^ 2 + 2 * cscCotangentWeight x r s) := by
      rw [hS1]
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      ring_nf
    _ ≤ ∑ s, ‖u s‖ ^ 2 * δ⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      calc
        (∑ r ∈ Finset.univ.erase s,
          ‖u s‖ ^ 2 *
            (cosecantPi (x r - x s) ^ 2 + 2 * cscCotangentWeight x r s)) =
            ‖u s‖ ^ 2 *
              ∑ r ∈ Finset.univ.erase s,
                (cosecantPi (x r - x s) ^ 2 +
                  2 * cscCotangentWeight x r s) := by
          rw [Finset.mul_sum]
        _ ≤ ‖u s‖ ^ 2 * δ⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_left
            (sum_csc_sq_add_two_weight_le_inv_sq x hδ hsep s)
            (sq_nonneg ‖u s‖)
    _ = δ⁻¹ ^ 2 := by
      rw [← Finset.sum_mul, hnorm, one_mul]

/-- Every normalized source eigenvector has eigenvalue at most `delta⁻¹` in
square, with the trigonometric identity derived from separation. -/
lemma normalizedEigenvalue_sq_le_of_separated
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s →
      δ ≤ dist (x r : UnitAddCircle) (x s : UnitAddCircle))
    (u : ι → ℂ) (μ : ℝ)
    (hu : ∀ s, sourceRowSum x u s = Complex.I * μ * u s)
    (hnorm : (∑ r, ‖u r‖ ^ 2) = 1) :
    μ ^ 2 ≤ δ⁻¹ ^ 2 := by
  rw [eigenvalue_sq_eq_re_S1_add_two_re_S5 x u μ
    (cosecantCotangentIdentity_of_separated x hδ hsep) hu hnorm]
  exact montgomeryVaughan_energy_le x hδ hsep u hnorm

/-- Internal all-vector composition consumed by the public SEM-447 facade. -/
lemma norm_cosecantBilinearForm_le_of_separated
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s →
      δ ≤ dist (x r : UnitAddCircle) (x s : UnitAddCircle))
    (u : ι → ℂ) :
    ‖cosecantBilinearForm x u‖ ≤ δ⁻¹ * ∑ i, ‖u i‖ ^ 2 := by
  apply norm_cosecantBilinearForm_le_of_normalized_eigenvector_estimate x hδ
  intro μ v hv hnorm
  exact normalizedEigenvalue_sq_le_of_separated x hδ hsep v μ hv hnorm

end BoundedGaps.Maynard.CosecantHilbert
