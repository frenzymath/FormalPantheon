import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert.Basic
import Mathlib.Analysis.Matrix.Spectrum

open scoped ComplexConjugate
open Finset Matrix

noncomputable section

namespace BoundedGaps.Maynard.CosecantHilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! This file contains the finite-dimensional spectral reduction behind
Montgomery--Vaughan (3.1).  The remaining eigenvalue estimate is supplied by
the separately audited pointwise and circle-packing modules (SEM-447).
-/

section EigenbasisBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [DecidableEq ι] in
/-- A Hermitian diagonalization estimate, independent of how its basis was found. -/
lemma norm_inner_apply_le_of_orthonormal_eigenbasis
    (T : E →ₗ[ℂ] E) (b : OrthonormalBasis ι ℂ E) (μ : ι → ℝ)
    (hT : ∀ i, T (b i) = (μ i : ℂ) • b i)
    {C : ℝ} (_hC : 0 ≤ C) (hμ : ∀ i, |μ i| ≤ C) (u : E) :
    ‖inner ℂ u (T u)‖ ≤ C * ‖u‖ ^ 2 := by
  let a : ι → ℂ := fun i => (b.repr u).ofLp i
  have hu : ∑ i, a i • b i = u := b.sum_repr u
  have hTu : T u = ∑ i, ((μ i : ℂ) * a i) • b i := by
    rw [← hu, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, hT]
    simp only [smul_smul]
    ring_nf
  have hinner :
      inner ℂ u (T u) = ∑ i, star (a i) * ((μ i : ℂ) * a i) := by
    calc
      inner ℂ u (T u) =
          inner ℂ (∑ i, a i • b i) (∑ i, ((μ i : ℂ) * a i) • b i) := by
            rw [hu, hTu]
      _ = ∑ i, star (a i) * ((μ i : ℂ) * a i) := by
        rw [sum_inner]
        apply Finset.sum_congr rfl
        intro i hi
        rw [inner_smul_left]
        rw [b.orthonormal.inner_right_fintype]
        rw [Complex.star_def]
  have hnorm : ∑ i, ‖a i‖ ^ 2 = ‖u‖ ^ 2 := by
    change (∑ i, ‖(b.repr u).ofLp i‖ ^ 2) = ‖u‖ ^ 2
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) (b.repr u)]
    rw [b.repr.norm_map]
  rw [hinner]
  calc
    ‖∑ i, star (a i) * ((μ i : ℂ) * a i)‖ ≤
        ∑ i, ‖star (a i) * ((μ i : ℂ) * a i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * ‖a i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_star, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have ha : 0 ≤ ‖a i‖ := norm_nonneg _
      nlinarith [hμ i]
    _ = C * ∑ i, ‖a i‖ ^ 2 := by rw [Finset.mul_sum]
    _ = C * ‖u‖ ^ 2 := by rw [hnorm]

/-- Matrix form of the reusable eigenbasis estimate. -/
lemma norm_star_dotProduct_mulVec_le_of_eigenvalues
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    {C : ℝ} (hC : 0 ≤ C) (hμ : ∀ i, |hA.eigenvalues i| ≤ C)
    (u : ι → ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ u)‖ ≤ C * ∑ i, ‖u i‖ ^ 2 := by
  let U : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  have hbound := norm_inner_apply_le_of_orthonormal_eigenbasis
    (ι := ι) (E := EuclideanSpace ℂ ι) ((Matrix.toLpLin 2 2) A)
    hA.eigenvectorBasis hA.eigenvalues
    (fun i => by
      rw [Matrix.toLpLin_apply, hA.mulVec_eigenvectorBasis]
      rw [WithLp.toLp_smul, WithLp.toLp_ofLp]
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)
    hC hμ U
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hbound
  change ‖star u ⬝ᵥ (A *ᵥ u)‖ ≤ C * ∑ i, ‖u i‖ ^ 2
  simpa only [U, WithLp.ofLp_toLp, Matrix.toLpLin_apply,
    PiLp.norm_sq_eq_of_L2, dotProduct_comm] using hbound

lemma cosecantBilinearForm_eq_I_mul_hermitianForm
    (x : ι → ℝ) (u : ι → ℂ) :
    cosecantBilinearForm x u =
      Complex.I * (star u ⬝ᵥ (hermitianCosecantKernel x *ᵥ u)) := by
  rw [cosecantBilinearForm_eq_sum_star_mul_sourceRowSum, dotProduct]
  simp_rw [sourceRowSum_eq_neg_mulVec]
  rw [hermitianCosecantKernel, smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  calc
    star (u s) * -(cosecantKernel x *ᵥ u) s =
        -(star (u s) * (cosecantKernel x *ᵥ u) s) := by ring
    _ = (Complex.I * Complex.I) *
        (star (u s) * (cosecantKernel x *ᵥ u) s) := by
          rw [Complex.I_mul_I]
          ring
    _ = Complex.I *
        (star (u s) * (Complex.I * (cosecantKernel x *ᵥ u) s)) := by ring

/-- The spectral reduction: it remains only to bound each squared eigenvalue. -/
lemma norm_cosecantBilinearForm_le_of_eigenvalue_sq_le
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (heigen : ∀ i,
      (hermitianCosecantKernel_isHermitian x).eigenvalues i ^ 2 ≤ δ⁻¹ ^ 2)
    (u : ι → ℂ) :
    ‖cosecantBilinearForm x u‖ ≤ δ⁻¹ * ∑ i, ‖u i‖ ^ 2 := by
  have hC : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have habs : ∀ i,
      |(hermitianCosecantKernel_isHermitian x).eigenvalues i| ≤ δ⁻¹ := by
    intro i
    rw [← (sq_le_sq₀ (abs_nonneg _) hC)]
    simpa only [sq_abs] using heigen i
  rw [cosecantBilinearForm_eq_I_mul_hermitianForm, norm_mul, Complex.norm_I,
    one_mul]
  exact norm_star_dotProduct_mulVec_le_of_eigenvalues
    (hermitianCosecantKernel x) (hermitianCosecantKernel_isHermitian x)
    hC habs u

/-! This bridge exposes the exact hypothesis consumed by the later
Montgomery--Vaughan cancellation proof, without asserting an analytic bound. -/
lemma norm_cosecantBilinearForm_le_of_normalized_eigenvector_estimate
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hanalytic : ∀ (μ : ℝ) (v : ι → ℂ),
      (∀ s, sourceRowSum x v s = Complex.I * μ * v s) →
      (∑ r, ‖v r‖ ^ 2) = 1 → μ ^ 2 ≤ δ⁻¹ ^ 2)
    (u : ι → ℂ) :
    ‖cosecantBilinearForm x u‖ ≤ δ⁻¹ * ∑ i, ‖u i‖ ^ 2 := by
  apply norm_cosecantBilinearForm_le_of_eigenvalue_sq_le x hδ
  intro i
  let hH := hermitianCosecantKernel_isHermitian x
  let v : ι → ℂ := (hH.eigenvectorBasis i).ofLp
  have hv : hermitianCosecantKernel x *ᵥ v =
      (hH.eigenvalues i : ℂ) • v := by
    have heig := hH.mulVec_eigenvectorBasis i
    change hermitianCosecantKernel x *ᵥ (hH.eigenvectorBasis i).ofLp =
      (hH.eigenvalues i : ℂ) • (hH.eigenvectorBasis i).ofLp
    rw [heig]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  apply hanalytic (hH.eigenvalues i) v
  · exact fun s => sourceRowSum_of_eigenvector x v (hH.eigenvalues i) hv s
  · have hvnorm : ‖hH.eigenvectorBasis i‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
    have hsquare := PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) (hH.eigenvectorBasis i)
    simpa only [v, hvnorm, one_pow] using hsquare.symm

end EigenbasisBound

end BoundedGaps.Maynard.CosecantHilbert
