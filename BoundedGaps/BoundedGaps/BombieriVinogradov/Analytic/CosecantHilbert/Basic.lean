import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped ComplexConjugate
open Finset Matrix

noncomputable section

namespace BoundedGaps.Maynard

/-- The exact off-diagonal expression in Montgomery--Vaughan Theorem 1,
equation (1.2). Real lifts are retained; only the later separation hypothesis
uses their images in `UnitAddCircle` (SEM-447). -/
noncomputable def cosecantBilinearForm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ r, ∑ s ∈ Finset.univ.erase r,
    u r * star (u s) *
      (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ)

namespace CosecantHilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! The matrix and row conventions below are those of equations (3.1)--(3.9):
`K r s = csc (pi (x r - x s))` off the diagonal and `H = I • K`.
-/

def cosecantKernel (x : ι → ℝ) : Matrix ι ι ℂ := fun r s =>
  if r = s then 0
  else (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ)

def hermitianCosecantKernel (x : ι → ℝ) : Matrix ι ι ℂ :=
  Complex.I • cosecantKernel x

def sourceRowSum (x : ι → ℝ) (u : ι → ℂ) (s : ι) : ℂ :=
  ∑ r ∈ Finset.univ.erase s,
    u r * (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ)

omit [Fintype ι] in
lemma cosecantKernel_diag (x : ι → ℝ) (r : ι) : cosecantKernel x r r = 0 := by
  simp [cosecantKernel]

omit [Fintype ι] in
lemma cosecantKernel_swap (x : ι → ℝ) (r s : ι) :
    cosecantKernel x s r = -cosecantKernel x r s := by
  by_cases hrs : r = s
  · subst s
    simp [cosecantKernel]
  · rw [cosecantKernel, cosecantKernel, if_neg hrs, if_neg (Ne.symm hrs)]
    rw [show x s - x r = -(x r - x s) by ring, mul_neg, Real.sin_neg, inv_neg]
    norm_cast

omit [Fintype ι] in
lemma star_cosecantKernel (x : ι → ℝ) (r s : ι) :
    star (cosecantKernel x r s) = cosecantKernel x r s := by
  by_cases hrs : r = s
  · subst s
    simp [cosecantKernel]
  · rw [cosecantKernel, if_neg hrs]
    exact Complex.conj_ofReal _

omit [Fintype ι] in
lemma hermitianCosecantKernel_isHermitian (x : ι → ℝ) :
    (hermitianCosecantKernel x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro r s
  change star (Complex.I * (cosecantKernel x) s r) =
    Complex.I * (cosecantKernel x) r s
  calc
    star (Complex.I * (cosecantKernel x) s r) =
        star Complex.I * star ((cosecantKernel x) s r) := by rw [star_mul']
    _ = (-Complex.I) * (cosecantKernel x) s r := by
      rw [show star Complex.I = -Complex.I by exact Complex.conj_I,
        star_cosecantKernel]
    _ = (-Complex.I) * (-(cosecantKernel x) r s) := by
      rw [cosecantKernel_swap]
    _ = Complex.I * (cosecantKernel x) r s := by ring

lemma sourceRowSum_eq_neg_mulVec (x : ι → ℝ) (u : ι → ℂ) (s : ι) :
    sourceRowSum x u s = -(cosecantKernel x *ᵥ u) s := by
  have hdiag : (cosecantKernel x) s s * u s = 0 := by
    rw [cosecantKernel_diag, zero_mul]
  have hsum :
      ∑ i ∈ Finset.univ.erase s, (cosecantKernel x) s i * u i =
        ∑ i, (cosecantKernel x) s i * u i :=
    Finset.sum_erase Finset.univ hdiag
  rw [sourceRowSum, mulVec, dotProduct, ← hsum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hrs : r ≠ s := Finset.ne_of_mem_erase hr
  rw [show (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ) =
      (cosecantKernel x) r s by simp [cosecantKernel, hrs]]
  rw [cosecantKernel_swap]
  ring

lemma sourceRowSum_of_eigenvector
    (x : ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (hu : hermitianCosecantKernel x *ᵥ u = (μ : ℂ) • u) (s : ι) :
    sourceRowSum x u s = Complex.I * μ * u s := by
  have hs := congr_fun hu s
  rw [sourceRowSum_eq_neg_mulVec]
  have hs' : Complex.I * (cosecantKernel x *ᵥ u) s = (μ : ℂ) * u s := by
    simpa only [hermitianCosecantKernel, smul_mulVec, Pi.smul_apply, smul_eq_mul]
      using hs
  calc
    -(cosecantKernel x *ᵥ u) s =
        Complex.I * (Complex.I * (cosecantKernel x *ᵥ u) s) := by
          rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    _ = Complex.I * ((μ : ℂ) * u s) := by rw [hs']
    _ = Complex.I * μ * u s := by ring

/-! Exposing this finite reindexing lemma keeps all erase conventions explicit
for the source-cancellation module; no diagonal term is hidden by notation.
-/
lemma sum_erase_eq_sum_ite (a : ι) (f : ι → ℂ) :
    ∑ b ∈ Finset.univ.erase a, f b = ∑ b, if b = a then 0 else f b := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_erase, ne_eq, Finset.mem_univ]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩

lemma cosecantBilinearForm_eq_sum_star_mul_sourceRowSum
    (x : ι → ℝ) (u : ι → ℂ) :
    cosecantBilinearForm x u = ∑ s, star (u s) * sourceRowSum x u s := by
  simp_rw [cosecantBilinearForm, sourceRowSum, Finset.mul_sum,
    sum_erase_eq_sum_ite]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hrs : r = s
  · subst s
    simp
  · simp [hrs, Ne.symm hrs]
    ring

end CosecantHilbert

end BoundedGaps.Maynard
