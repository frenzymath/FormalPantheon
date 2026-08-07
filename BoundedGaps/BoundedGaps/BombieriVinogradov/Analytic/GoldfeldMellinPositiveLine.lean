import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldPlateauMellinDecay

/-!
# Positive-line integrability of the Goldfeld Mellin transform

The generic inversion theorem needs the raw Mellin transform to be integrable
on its full positive vertical line.  We prove this by writing the derivative
Mellin transform as the Fourier transform of a compactly supported smooth
logarithmic kernel.

Semantic review: `SEM-553`.
-/

noncomputable section

open Complex Set MeasureTheory Real
open scoped ContDiff Topology SchwartzMap FourierTransform

namespace BoundedGaps.Maynard

private noncomputable def goldfeldPositiveLineKernel
    (alpha u : ℝ) : ℂ :=
  (Real.exp (-alpha * u) : ℂ) *
    goldfeldMellinDerivativeWeight (Real.exp (-u))

private theorem goldfeldMellinDerivativeWeight_contDiff_positiveLine :
    ContDiff ℝ ∞ goldfeldMellinDerivativeWeight := by
  have hd : ContDiff ℝ ∞ goldfeldPlateauDerivativeComplex :=
    Complex.ofRealCLM.contDiff.comp goldfeldPlateau_deriv_contDiff
  unfold goldfeldMellinDerivativeWeight
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hd

private theorem goldfeldPositiveLineKernel_contDiff (alpha : ℝ) :
    ContDiff ℝ ∞ (goldfeldPositiveLineKernel alpha) := by
  have hlinear : ContDiff ℝ ∞ (fun u : ℝ => -alpha * u) :=
    contDiff_const.mul contDiff_id
  have heReal : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-alpha * u)) :=
    hlinear.exp
  have he : ContDiff ℝ ∞ (fun u : ℝ => (Real.exp (-alpha * u) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp heReal
  have harg : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) := by
    fun_prop
  unfold goldfeldPositiveLineKernel
  exact he.mul
    (goldfeldMellinDerivativeWeight_contDiff_positiveLine.comp harg)

private theorem goldfeldPositiveLineKernel_eq_zero_of_pos
    (alpha : ℝ) {u : ℝ} (hu : 0 < u) :
    goldfeldPositiveLineKernel alpha u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd := goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one harg hlt
  simp [goldfeldPositiveLineKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem goldfeldPositiveLineKernel_eq_zero_of_lt_neg_log_two
    (alpha : ℝ) {u : ℝ} (hu : u < -Real.log 2) :
    goldfeldPositiveLineKernel alpha u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlog : Real.log 2 < -u := by linarith
  have hgt : 2 < Real.exp (-u) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (Real.exp_lt_exp).2 hlog
  have hd := goldfeldPlateau_deriv_eq_zero_of_two_lt hgt
  simp [goldfeldPositiveLineKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem goldfeldPositiveLineKernel_support_subset (alpha : ℝ) :
    Function.support (goldfeldPositiveLineKernel alpha) ⊆
      Icc (-Real.log 2) 0 := by
  intro u hu
  by_contra hnot
  have hcases : u < -Real.log 2 ∨ 0 < u := by
    by_cases hleft : u < -Real.log 2
    · exact Or.inl hleft
    · have hleft' : -Real.log 2 ≤ u := le_of_not_gt hleft
      by_cases hright : 0 < u
      · exact Or.inr hright
      · exact False.elim (hnot ⟨hleft', le_of_not_gt hright⟩)
  rcases hcases with hleft | hright
  · exact hu (goldfeldPositiveLineKernel_eq_zero_of_lt_neg_log_two alpha hleft)
  · exact hu (goldfeldPositiveLineKernel_eq_zero_of_pos alpha hright)

private theorem goldfeldPositiveLineKernel_hasCompactSupport (alpha : ℝ) :
    HasCompactSupport (goldfeldPositiveLineKernel alpha) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-Real.log 2) 0) isCompact_Icc
  exact goldfeldPositiveLineKernel_support_subset alpha

private noncomputable def goldfeldPositiveLineKernelSchwartz
    (alpha : ℝ) : 𝓢(ℝ, ℂ) :=
  (goldfeldPositiveLineKernel_hasCompactSupport alpha).toSchwartzMap
    (goldfeldPositiveLineKernel_contDiff alpha)

private theorem goldfeldDerivativeMellin_on_positiveLine
    (alpha t : ℝ) :
    goldfeldDerivativeMellin ((alpha : ℂ) + t * I) =
      𝓕 (goldfeldPositiveLineKernelSchwartz alpha) (t / (2 * π)) := by
  calc
    goldfeldDerivativeMellin ((alpha : ℂ) + t * I) =
        mellin goldfeldMellinDerivativeWeight ((alpha : ℂ) + t * I) :=
      goldfeldDerivativeMellin_eq_weight _
    _ = 𝓕 (fun u : ℝ =>
        Real.exp (-((alpha : ℂ) + t * I).re * u) •
          goldfeldMellinDerivativeWeight (Real.exp (-u)))
        (((alpha : ℂ) + t * I).im / (2 * π)) :=
      mellin_eq_fourier goldfeldMellinDerivativeWeight
    _ = 𝓕 (goldfeldPositiveLineKernelSchwartz alpha) (t / (2 * π)) := by
      norm_num
      rw [SchwartzMap.fourier_coe]
      apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * π)))
      funext u
      simp [goldfeldPositiveLineKernelSchwartz, goldfeldPositiveLineKernel]

/-- The raw Goldfeld Mellin transform is integrable on every positive
vertical line. -/
theorem goldfeldRawMellin_verticalIntegrable
    {alpha : ℝ} (halpha : 0 < alpha) :
    VerticalIntegrable goldfeldRawMellin alpha := by
  let fourierLine : ℝ → ℂ := fun t =>
    𝓕 (goldfeldPositiveLineKernelSchwartz alpha) (t / (2 * π))
  let z : ℝ → ℂ := fun t => (alpha : ℂ) + t * I
  let invFactor : ℝ → ℂ := fun t => -(z t)⁻¹
  have hfourier : Integrable fourierLine := by
    have h := (𝓕 (goldfeldPositiveLineKernelSchwartz alpha)).integrable
      |>.comp_mul_right'
        (show (2 * π : ℝ)⁻¹ ≠ 0 by positivity)
    simpa [fourierLine, div_eq_mul_inv] using h
  have hzContinuous : Continuous z := by
    fun_prop
  have hzNe (t : ℝ) : z t ≠ 0 := by
    intro ht
    have hre := congrArg Complex.re ht
    simp [z] at hre
    exact halpha.ne' hre
  have hinvContinuous : Continuous invFactor := by
    exact (hzContinuous.inv₀ hzNe).neg
  have hzNorm (t : ℝ) : alpha ≤ ‖z t‖ := by
    have h := Complex.abs_re_le_norm (z t)
    simpa [z, abs_of_pos halpha] using h
  have hinvBound : ∀ᵐ t : ℝ, ‖invFactor t‖ ≤ alpha⁻¹ :=
    ae_of_all _ fun t => by
      change ‖-(z t)⁻¹‖ ≤ alpha⁻¹
      rw [norm_neg, norm_inv]
      exact (inv_le_inv₀ (halpha.trans_le (hzNorm t)) halpha).2 (hzNorm t)
  have hproduct : Integrable fun t => fourierLine t * invFactor t :=
    hfourier.mul_bdd hinvContinuous.aestronglyMeasurable hinvBound
  rw [VerticalIntegrable]
  refine hproduct.congr (ae_of_all _ fun t => ?_)
  have hraw : goldfeldRawMellin (z t) = fourierLine t * invFactor t := by
    rw [← goldfeldMellinCandidate_eq_raw (by simp [z, halpha])]
    rw [goldfeldMellinCandidate,
      goldfeldDerivativeMellin_on_positiveLine alpha t]
    simp only [fourierLine, invFactor, div_eq_mul_inv]
    ring
  simpa [z] using hraw.symm

end BoundedGaps.Maynard
