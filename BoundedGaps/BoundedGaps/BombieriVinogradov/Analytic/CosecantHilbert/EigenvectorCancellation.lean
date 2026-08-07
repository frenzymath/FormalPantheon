import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert.FiniteCancellation
import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert.Spectral

open scoped ComplexConjugate
open Finset

noncomputable section

namespace BoundedGaps.Maynard.CosecantHilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma conjugateCosecantRow_of_source_eigenvector
    (x : ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (hu : ∀ s, sourceRowSum x u s = Complex.I * μ * u s) (r : ι) :
    conjugateCosecantRow x u r = Complex.I * μ * star (u r) := by
  have hstar := congrArg star (reverseSourceRowSum_eq_neg x u r)
  simp only [map_sum, map_mul, Complex.conj_ofReal, map_neg, Complex.star_def] at hstar
  rw [hu] at hstar
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal] at hstar
  rw [conjugateCosecantRow]
  change (∑ s ∈ Finset.univ.erase r,
    (starRingEnd ℂ) (u s) *
      (((Real.sin (Real.pi * (x r - x s)))⁻¹ : ℝ) : ℂ)) =
    Complex.I * μ * (starRingEnd ℂ) (u r)
  calc
    _ = -(-Complex.I * μ * (starRingEnd ℂ) (u r)) := hstar
    _ = Complex.I * μ * (starRingEnd ℂ) (u r) := by ring

/-- The normalized Cauchy energy is `mu^2` under the source-row eigen equation. -/
lemma cauchyEnergy_eq_eigenvalue_sq
    (x : ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (hu : ∀ s, sourceRowSum x u s = Complex.I * μ * u s)
    (hnorm : (∑ r, ‖u r‖ ^ 2) = 1) :
    (∑ r, (Complex.normSq (conjugateCosecantRow x u r) : ℂ)) = (μ ^ 2 : ℂ) := by
  have hsquare (r : ι) :
      Complex.normSq (Complex.I * (μ : ℂ) * star (u r)) = μ ^ 2 * ‖u r‖ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I,
      Complex.normSq_ofReal]
    change 1 * (μ * μ) * Complex.normSq ((starRingEnd ℂ) (u r)) =
      μ ^ 2 * ‖u r‖ ^ 2
    rw [Complex.normSq_conj, Complex.normSq_eq_norm_sq]
    ring
  simp_rw [conjugateCosecantRow_of_source_eigenvector x u μ hu, hsquare]
  have hnormC : (∑ r, (‖u r‖ : ℂ) ^ 2) = 1 := by
    exact_mod_cast hnorm
  push_cast
  rw [← Finset.mul_sum, hnormC]
  norm_num

/-- The complex form of Montgomery--Vaughan (3.3)--(3.9), including the
eigenvector cancellation in (3.6)--(3.8). -/
lemma eigenvalue_sq_eq_S1_add_two_re_S5
    (x : ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (htrig : CosecantCotangentIdentity x)
    (hu : ∀ s, sourceRowSum x u s = Complex.I * μ * u s)
    (hnorm : (∑ r, ‖u r‖ ^ 2) = 1) :
    (μ ^ 2 : ℂ) = montgomeryVaughanS1 x u +
      2 * ((montgomeryVaughanS5 x u).re : ℂ) := by
  rw [← cauchyEnergy_eq_eigenvalue_sq x u μ hu hnorm,
    cauchyEnergy_eq_S1_add_S2,
    montgomeryVaughanS2_eq_two_re_S5_of_source_eigenvector x u μ htrig hu]

/-- The real identity at the end of Montgomery--Vaughan equation (3.9). -/
lemma eigenvalue_sq_eq_re_S1_add_two_re_S5
    (x : ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (htrig : CosecantCotangentIdentity x)
    (hu : ∀ s, sourceRowSum x u s = Complex.I * μ * u s)
    (hnorm : (∑ r, ‖u r‖ ^ 2) = 1) :
    μ ^ 2 = (montgomeryVaughanS1 x u).re +
      2 * (montgomeryVaughanS5 x u).re := by
  have h := congrArg Complex.re
    (eigenvalue_sq_eq_S1_add_two_re_S5 x u μ htrig hu hnorm)
  norm_num [pow_two, Complex.mul_re] at h
  simpa [pow_two] using h

/-- A normalized-eigenvector energy estimate yields the cosecant bound for
every coefficient vector. -/
lemma norm_cosecantBilinearForm_le_of_energy_bound
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (htrig : CosecantCotangentIdentity x)
    (henergy : ∀ (μ : ℝ) (v : ι → ℂ),
      (∀ s, sourceRowSum x v s = Complex.I * μ * v s) →
      (∑ r, ‖v r‖ ^ 2) = 1 →
      (montgomeryVaughanS1 x v).re + 2 * (montgomeryVaughanS5 x v).re ≤ δ⁻¹ ^ 2)
    (u : ι → ℂ) :
    ‖cosecantBilinearForm x u‖ ≤ δ⁻¹ * ∑ i, ‖u i‖ ^ 2 := by
  apply norm_cosecantBilinearForm_le_of_normalized_eigenvector_estimate x hδ
  intro μ v hv hnorm
  rw [eigenvalue_sq_eq_re_S1_add_two_re_S5 x v μ htrig hv hnorm]
  exact henergy μ v hv hnorm

end BoundedGaps.Maynard.CosecantHilbert
