import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert.Basic

/-!
# Finite Montgomery--Vaughan expansion

This file formalizes the finite square expansion through equation (3.5) and states the
trigonometric identity (3.6) used in Montgomery--Vaughan's sharp cosecant Hilbert inequality.
-/

open scoped ComplexConjugate
open Finset Matrix

noncomputable section

namespace BoundedGaps.Maynard.CosecantHilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section SourceCancellation

/-- The row inside the absolute square on the right side of (3.3). -/
def conjugateCosecantRow (x : ι → ℝ) (u : ι → ℂ) (r : ι) : ℂ :=
  ∑ s ∈ Finset.univ.erase r,
    star (u s) * (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ)

/-- The expanded diagonal contribution `S_1` from (3.4), in row-first order. -/
def montgomeryVaughanS1 (x : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ r, ∑ s ∈ Finset.univ.erase r,
    star (u s) * u s *
      (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ) ^ 2

/-- The expanded off-diagonal contribution `S_2` from (3.5).
The inner erase makes `r`, `s`, and `t` pairwise distinct. -/
def montgomeryVaughanS2 (x : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ r, ∑ s ∈ Finset.univ.erase r,
    ∑ t ∈ (Finset.univ.erase r).erase s,
      star (u s) * u t *
        (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ) *
        (((Real.sin (Real.pi * (x r - x t)))⁻¹ : ℝ) : ℂ)

/-- The equality part of (3.3): expansion of the sum of squared row norms. -/
lemma cauchyEnergy_eq_S1_add_S2 (x : ι → ℝ) (u : ι → ℂ) :
    (∑ r, (Complex.normSq (conjugateCosecantRow x u r) : ℂ)) =
      montgomeryVaughanS1 x u + montgomeryVaughanS2 x u := by
  rw [montgomeryVaughanS1, montgomeryVaughanS2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_add_distrib]
  rw [conjugateCosecantRow, Complex.normSq_eq_conj_mul_self]
  rw [mul_comm]
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  simp_rw [starRingEnd_apply, star_star]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  have hsmem : s ∈ Finset.univ.erase r := hs
  rw [← Finset.sum_erase_add (Finset.univ.erase r)
    (fun t =>
      star (u s) *
        ↑(Real.sin (Real.pi * (x r - x s)))⁻¹ *
        (u t * ↑(Real.sin (Real.pi * (x r - x t)))⁻¹)) hsmem]
  ring_nf

lemma offDiagonal_sum_comm (f : ι → ι → ℂ) :
    (∑ s, ∑ r ∈ Finset.univ.erase s, f r s) =
      ∑ r, ∑ s ∈ Finset.univ.erase r, f r s := by
  simp_rw [sum_erase_eq_sum_ite]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : r = s
  · subst s
    simp
  · simp [h, Ne.symm h]

omit [Fintype ι] in
private lemma sum_erase_eq_sum_ite_on (S : Finset ι) (a : ι) (f : ι → ℂ) :
    ∑ b ∈ S.erase a, f b = ∑ b ∈ S, if b = a then 0 else f b := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩

omit [Fintype ι] in
lemma offDiagonal_sum_comm_on (S : Finset ι) (f : ι → ι → ℂ) :
    (∑ s ∈ S, ∑ r ∈ S.erase s, f s r) =
      ∑ r ∈ S, ∑ s ∈ S.erase r, f s r := by
  simp_rw [sum_erase_eq_sum_ite_on]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : r = s
  · subst s
    simp
  · simp [h, Ne.symm h]

/-- The cotangent factor occurring in (3.6)--(3.9). -/
def cotangentPiDiff (x : ι → ℝ) (r s : ι) : ℝ :=
  Real.cos (Real.pi * (x r - x s)) *
    (Real.sin (Real.pi * (x r - x s)))⁻¹

/-- Equation (3.6), isolated as the precise trigonometric input to the finite algebra. -/
def CosecantCotangentIdentity (x : ι → ℝ) : Prop :=
  ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
    (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ) *
        (((Real.sin (Real.pi * (x r - x t)))⁻¹ : ℝ) : ℂ) =
      (((Real.sin (Real.pi * (x s - x t)))⁻¹ : ℝ) : ℂ) *
        ((cotangentPiDiff x r s : ℂ) - (cotangentPiDiff x r t : ℂ))

end SourceCancellation

end BoundedGaps.Maynard.CosecantHilbert
