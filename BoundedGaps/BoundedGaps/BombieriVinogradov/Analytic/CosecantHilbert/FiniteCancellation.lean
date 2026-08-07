import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert.FiniteExpansion
import Mathlib.Tactic.LinearCombination

/-!
# Finite Montgomery--Vaughan cancellation

This file formalizes the `S_3`, `S_4`, and `S_5` cancellation in equations (3.7)--(3.9) of
Montgomery--Vaughan's proof of the sharp cosecant Hilbert inequality.
-/

open scoped ComplexConjugate
open Finset Matrix

noncomputable section

namespace BoundedGaps.Maynard.CosecantHilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section SourceCancellation

private def montgomeryVaughanA (x : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ r, ∑ s ∈ Finset.univ.erase r,
    ∑ t ∈ (Finset.univ.erase r).erase s,
      star (u s) * u t *
        (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
        (cotangentPiDiff x r s : ℂ)

private def montgomeryVaughanB (x : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ r, ∑ s ∈ Finset.univ.erase r,
    ∑ t ∈ (Finset.univ.erase r).erase s,
      star (u s) * u t *
        (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
        (cotangentPiDiff x r t : ℂ)

lemma montgomeryVaughanS2_eq_A_sub_B
    (x : ι → ℝ) (u : ι → ℂ) (htrig : CosecantCotangentIdentity x) :
    montgomeryVaughanS2 x u =
      montgomeryVaughanA x u - montgomeryVaughanB x u := by
  rw [montgomeryVaughanS2, montgomeryVaughanA, montgomeryVaughanB,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hrs : r ≠ s := Ne.symm (Finset.ne_of_mem_erase hs)
  have htr : t ≠ r := by
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
  have hts : t ≠ s := Finset.ne_of_mem_erase ht
  have hi := htrig r s t hrs (Ne.symm htr) (Ne.symm hts)
  calc
    star (u s) * u t *
        (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ) *
        (((Real.sin (Real.pi * (x r - x t)))⁻¹ : ℝ) : ℂ) =
      (star (u s) * u t) *
        ((((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ) *
        (((Real.sin (Real.pi * (x r - x t)))⁻¹ : ℝ) : ℂ)) := by ring
    _ = (star (u s) * u t) *
        ((((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
        ((cotangentPiDiff x r s : ℂ) - (cotangentPiDiff x r t : ℂ))) := by rw [hi]
    _ = star (u s) * u t *
          (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
          (cotangentPiDiff x r s : ℂ) -
        star (u s) * u t *
          (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
          (cotangentPiDiff x r t : ℂ) := by ring

omit [Fintype ι] [DecidableEq ι] in
lemma cotangentPiDiff_swap (x : ι → ℝ) (r s : ι) :
    cotangentPiDiff x s r = -cotangentPiDiff x r s := by
  rw [cotangentPiDiff, cotangentPiDiff]
  rw [show x s - x r = -(x r - x s) by ring, mul_neg, Real.cos_neg,
    Real.sin_neg, inv_neg]
  ring

lemma reverseSourceRowSum_eq_neg (x : ι → ℝ) (u : ι → ℂ) (s : ι) :
    (∑ r ∈ Finset.univ.erase s,
      u r * (((Real.sin (Real.pi * (x s - x r)))⁻¹ : ℝ) : ℂ)) =
      -sourceRowSum x u s := by
  rw [sourceRowSum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show x s - x r = -(x r - x s) by ring, mul_neg, Real.sin_neg, inv_neg]
  rw [Complex.ofReal_neg]
  ring

/-- The sum denoted `S_3` in (3.7). Here `r=t` is allowed. -/
def montgomeryVaughanS3 (x : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ s, ∑ r ∈ Finset.univ.erase s, ∑ t ∈ Finset.univ.erase s,
    star (u s) * u t *
      (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
      (cotangentPiDiff x r s : ℂ)

/-- The sum denoted `S_4` in (3.8). Here `r=s` is allowed. -/
def montgomeryVaughanS4 (x : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ t, ∑ r ∈ Finset.univ.erase t, ∑ s ∈ Finset.univ.erase t,
    star (u s) * u t *
      (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
      (cotangentPiDiff x r t : ℂ)

/-- The correction term denoted `S_5` in (3.9). -/
def montgomeryVaughanS5 (x : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ s, ∑ r ∈ Finset.univ.erase s,
    star (u s) * u r *
      (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ) *
      (cotangentPiDiff x r s : ℂ)

/-- Hermitian matrix whose quadratic form is `S_5`. The row/column order matches (3.9). -/
def cscCotangentKernel (x : ι → ℝ) : Matrix ι ι ℂ := fun s r =>
  if s = r then 0
  else (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ) *
    (cotangentPiDiff x r s : ℂ)

omit [Fintype ι] in
lemma cscCotangentKernel_isHermitian (x : ι → ℝ) :
    (cscCotangentKernel x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro s r
  by_cases hsr : s = r
  · subst r
    simp [cscCotangentKernel]
  · rw [cscCotangentKernel, cscCotangentKernel, if_neg hsr,
      if_neg (Ne.symm hsr)]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [show x s - x r = -(x r - x s) by ring, mul_neg, Real.sin_neg, inv_neg,
      cotangentPiDiff_swap]
    push_cast
    ring

lemma montgomeryVaughanS5_eq_star_dotProduct_mulVec
    (x : ι → ℝ) (u : ι → ℂ) :
    montgomeryVaughanS5 x u = star u ⬝ᵥ (cscCotangentKernel x *ᵥ u) := by
  rw [montgomeryVaughanS5, dotProduct]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro s hs
  have hdiag : (cscCotangentKernel x) s s * u s = 0 := by
    simp [cscCotangentKernel]
  have hsum :
      ∑ r ∈ Finset.univ.erase s, (cscCotangentKernel x) s r * u r =
        ∑ r, (cscCotangentKernel x) s r * u r :=
    Finset.sum_erase Finset.univ hdiag
  rw [← hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrs : r ≠ s := Finset.ne_of_mem_erase hr
  rw [cscCotangentKernel, if_neg (Ne.symm hrs)]
  rw [Pi.star_apply]
  ring

lemma montgomeryVaughanS5_im (x : ι → ℝ) (u : ι → ℂ) :
    (montgomeryVaughanS5 x u).im = 0 := by
  rw [montgomeryVaughanS5_eq_star_dotProduct_mulVec]
  exact (cscCotangentKernel_isHermitian x).im_star_dotProduct_mulVec_self u

lemma star_montgomeryVaughanS5 (x : ι → ℝ) (u : ι → ℂ) :
    star (montgomeryVaughanS5 x u) = montgomeryVaughanS5 x u := by
  rw [Complex.star_def, Complex.conj_eq_iff_im]
  exact montgomeryVaughanS5_im x u

lemma montgomeryVaughanS5_row_first (x : ι → ℝ) (u : ι → ℂ) :
    montgomeryVaughanS5 x u =
      ∑ r, ∑ s ∈ Finset.univ.erase r,
        star (u s) * u r *
          (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ) *
          (cotangentPiDiff x r s : ℂ) := by
  rw [montgomeryVaughanS5]
  exact offDiagonal_sum_comm (fun r s =>
    star (u s) * u r *
      (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ) *
      (cotangentPiDiff x r s : ℂ))

lemma montgomeryVaughanS5_same_orientation (x : ι → ℝ) (u : ι → ℂ) :
    montgomeryVaughanS5 x u =
      ∑ r, ∑ t ∈ Finset.univ.erase r,
        star (u r) * u t *
          (((Real.sin (Real.pi * (x r - x t)))⁻¹ : ℝ) : ℂ) *
          (cotangentPiDiff x r t : ℂ) := by
  rw [montgomeryVaughanS5]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro t ht
  rw [show x t - x r = -(x r - x t) by ring, mul_neg, Real.sin_neg, inv_neg,
    Complex.ofReal_neg, cotangentPiDiff_swap, Complex.ofReal_neg]
  ring

private lemma montgomeryVaughanB_t_first (x : ι → ℝ) (u : ι → ℂ) :
    montgomeryVaughanB x u =
      ∑ r, ∑ t ∈ Finset.univ.erase r,
        ∑ s ∈ (Finset.univ.erase r).erase t,
          star (u s) * u t *
            (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
            (cotangentPiDiff x r t : ℂ) := by
  rw [montgomeryVaughanB]
  apply Finset.sum_congr rfl
  intro r hr
  exact offDiagonal_sum_comm_on (Finset.univ.erase r)
    (fun s t =>
      star (u s) * u t *
        (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
        (cotangentPiDiff x r t : ℂ))

lemma montgomeryVaughanS3_eq_A_sub_S5 (x : ι → ℝ) (u : ι → ℂ) :
    montgomeryVaughanS3 x u =
      montgomeryVaughanA x u - montgomeryVaughanS5 x u := by
  rw [montgomeryVaughanS3]
  calc
    (∑ s, ∑ r ∈ Finset.univ.erase s, ∑ t ∈ Finset.univ.erase s,
      star (u s) * u t *
        (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
        (cotangentPiDiff x r s : ℂ)) =
      ∑ r, ∑ s ∈ Finset.univ.erase r, ∑ t ∈ Finset.univ.erase s,
        star (u s) * u t *
          (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
          (cotangentPiDiff x r s : ℂ) :=
        offDiagonal_sum_comm (fun r s =>
          ∑ t ∈ Finset.univ.erase s,
            star (u s) * u t *
              (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
              (cotangentPiDiff x r s : ℂ))
    _ = montgomeryVaughanA x u - montgomeryVaughanS5 x u := by
      rw [montgomeryVaughanA, montgomeryVaughanS5_row_first,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      have hsr : s ≠ r := Finset.ne_of_mem_erase hs
      have hrmem : r ∈ Finset.univ.erase s := by simp [Ne.symm hsr]
      rw [← Finset.sum_erase_add (Finset.univ.erase s)
        (fun t =>
          star (u s) * u t *
            (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
            (cotangentPiDiff x r s : ℂ)) hrmem]
      rw [Finset.erase_right_comm]
      rw [show x s - x r = -(x r - x s) by ring, mul_neg, Real.sin_neg, inv_neg,
        Complex.ofReal_neg]
      ring

lemma montgomeryVaughanS4_eq_B_add_S5 (x : ι → ℝ) (u : ι → ℂ) :
    montgomeryVaughanS4 x u =
      montgomeryVaughanB x u + montgomeryVaughanS5 x u := by
  rw [montgomeryVaughanS4]
  calc
    (∑ t, ∑ r ∈ Finset.univ.erase t, ∑ s ∈ Finset.univ.erase t,
      star (u s) * u t *
        (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
        (cotangentPiDiff x r t : ℂ)) =
      ∑ r, ∑ t ∈ Finset.univ.erase r, ∑ s ∈ Finset.univ.erase t,
        star (u s) * u t *
          (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
          (cotangentPiDiff x r t : ℂ) :=
        offDiagonal_sum_comm (fun r t =>
          ∑ s ∈ Finset.univ.erase t,
            star (u s) * u t *
              (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
              (cotangentPiDiff x r t : ℂ))
    _ = montgomeryVaughanB x u + montgomeryVaughanS5 x u := by
      rw [montgomeryVaughanB_t_first, montgomeryVaughanS5_same_orientation,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have htr : t ≠ r := Finset.ne_of_mem_erase ht
      have hrmem : r ∈ Finset.univ.erase t := by simp [Ne.symm htr]
      rw [← Finset.sum_erase_add (Finset.univ.erase t)
        (fun s =>
          star (u s) * u t *
            (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
            (cotangentPiDiff x r t : ℂ)) hrmem]
      rw [Finset.erase_right_comm]

lemma montgomeryVaughanS2_eq_S3_sub_S4_add_two_S5
    (x : ι → ℝ) (u : ι → ℂ) (htrig : CosecantCotangentIdentity x) :
    montgomeryVaughanS2 x u =
      montgomeryVaughanS3 x u - montgomeryVaughanS4 x u +
        2 * montgomeryVaughanS5 x u := by
  rw [montgomeryVaughanS2_eq_A_sub_B x u htrig]
  have h3 := montgomeryVaughanS3_eq_A_sub_S5 x u
  have h4 := montgomeryVaughanS4_eq_B_add_S5 x u
  linear_combination -h3 + h4

lemma montgomeryVaughanS5_eq_ofReal_re (x : ι → ℝ) (u : ι → ℂ) :
    montgomeryVaughanS5 x u = ((montgomeryVaughanS5 x u).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [montgomeryVaughanS5_im]

/-- The common diagonal expression obtained from both (3.7) and (3.8). -/
def cotangentWeightedDiagonal (x : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ s, ∑ r ∈ Finset.univ.erase s,
    star (u s) * u s * (cotangentPiDiff x r s : ℂ)

lemma montgomeryVaughanS3_eq_of_source_eigenvector
    (x : ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (hu : ∀ s, sourceRowSum x u s = Complex.I * μ * u s) :
    montgomeryVaughanS3 x u =
      (-Complex.I * μ) * cotangentWeightedDiagonal x u := by
  rw [montgomeryVaughanS3, cotangentWeightedDiagonal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show (∑ t ∈ Finset.univ.erase s,
      star (u s) * u t *
        (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
        (cotangentPiDiff x r s : ℂ)) =
      star (u s) *
        (∑ t ∈ Finset.univ.erase s,
          u t * (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ)) *
        (cotangentPiDiff x r s : ℂ) by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t ht
          ring]
  rw [reverseSourceRowSum_eq_neg, hu]
  ring

lemma montgomeryVaughanS4_eq_of_source_eigenvector
    (x : ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (hu : ∀ s, sourceRowSum x u s = Complex.I * μ * u s) :
    montgomeryVaughanS4 x u =
      (-Complex.I * μ) * cotangentWeightedDiagonal x u := by
  rw [montgomeryVaughanS4, cotangentWeightedDiagonal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hconj :
      (∑ s ∈ Finset.univ.erase t,
        star (u s) *
          (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ)) =
        -Complex.I * μ * star (u t) := by
    have hstar := congrArg star (hu t)
    rw [sourceRowSum] at hstar
    simp only [map_sum, map_mul, Complex.conj_ofReal, Complex.star_def,
      Complex.conj_I] at hstar
    simpa only [Complex.star_def] using hstar
  rw [show (∑ s ∈ Finset.univ.erase t,
      star (u s) * u t *
        (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
        (cotangentPiDiff x r t : ℂ)) =
      (∑ s ∈ Finset.univ.erase t,
        star (u s) *
          (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ)) *
        u t * (cotangentPiDiff x r t : ℂ) by
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s hs
          ring]
  rw [hconj]
  ring

lemma montgomeryVaughanS3_eq_S4_of_source_eigenvector
    (x : ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (hu : ∀ s, sourceRowSum x u s = Complex.I * μ * u s) :
    montgomeryVaughanS3 x u = montgomeryVaughanS4 x u := by
  rw [montgomeryVaughanS3_eq_of_source_eigenvector x u μ hu,
    montgomeryVaughanS4_eq_of_source_eigenvector x u μ hu]

/-- Equations (3.6)--(3.9), including the eigenvector cancellation `S_3=S_4`. -/
lemma montgomeryVaughanS2_eq_two_re_S5_of_source_eigenvector
    (x : ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (htrig : CosecantCotangentIdentity x)
    (hu : ∀ s, sourceRowSum x u s = Complex.I * μ * u s) :
    montgomeryVaughanS2 x u =
      2 * ((montgomeryVaughanS5 x u).re : ℂ) := by
  rw [montgomeryVaughanS2_eq_S3_sub_S4_add_two_S5 x u htrig,
    montgomeryVaughanS3_eq_S4_of_source_eigenvector x u μ hu, sub_self, zero_add]
  exact congrArg (fun z : ℂ => 2 * z) (montgomeryVaughanS5_eq_ofReal_re x u)

end SourceCancellation

end BoundedGaps.Maynard.CosecantHilbert
