import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldPlateauMellin
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinInversion

/-!
# Vertical decay for the Goldfeld Mellin candidate

The logarithmic substitution in the Mellin transform turns the derivative
weight into the Fourier transform of a compactly supported smooth function.
This file is intentionally separate from the cutoff/continuation contract:
the Schwartz estimate is the only remaining analytic input in SEM-552.

Semantic review: `SEM-552`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Real
open scoped ContDiff Topology SchwartzMap FourierTransform

namespace BoundedGaps.Maynard

private noncomputable def goldfeldLogKernel (u : ℝ) : ℂ :=
  (Real.exp u : ℂ) * goldfeldMellinDerivativeWeight (Real.exp (-u))

private theorem goldfeldMellinDerivativeWeight_contDiff :
    ContDiff ℝ ∞ goldfeldMellinDerivativeWeight := by
  have hd : ContDiff ℝ ∞ goldfeldPlateauDerivativeComplex :=
    Complex.ofRealCLM.contDiff.comp goldfeldPlateau_deriv_contDiff
  unfold goldfeldMellinDerivativeWeight
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hd

private theorem goldfeldLogKernel_contDiff :
    ContDiff ℝ ∞ goldfeldLogKernel := by
  have he : ContDiff ℝ ∞ (fun u : ℝ => (Real.exp u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_id.exp
  have hne : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) :=
    (contDiff_id.neg).exp
  unfold goldfeldLogKernel
  exact he.mul (goldfeldMellinDerivativeWeight_contDiff.comp hne)

private theorem goldfeldLogKernel_eq_zero_of_pos {u : ℝ} (hu : 0 < u) :
    goldfeldLogKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd := goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one harg hlt
  simp [goldfeldLogKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem goldfeldLogKernel_eq_zero_of_lt_neg_log_two
    {u : ℝ} (hu : u < -Real.log 2) : goldfeldLogKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlog : Real.log 2 < -u := by linarith
  have hgt : 2 < Real.exp (-u) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (Real.exp_lt_exp).2 hlog
  have hd := goldfeldPlateau_deriv_eq_zero_of_two_lt hgt
  simp [goldfeldLogKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem goldfeldLogKernel_support_subset :
    Function.support goldfeldLogKernel ⊆ Icc (-Real.log 2) 0 := by
  intro u hu
  by_contra hnot
  have hleft : u < -Real.log 2 ∨ 0 < u := by
    by_cases h₁ : u < -Real.log 2
    · exact Or.inl h₁
    · have h₁' : -Real.log 2 ≤ u := le_of_not_gt h₁
      by_cases h₂ : 0 < u
      · exact Or.inr h₂
      · have h₂' : u ≤ 0 := le_of_not_gt h₂
        exact False.elim (hnot ⟨h₁', h₂'⟩)
  rcases hleft with hleft | hright
  · exact hu (goldfeldLogKernel_eq_zero_of_lt_neg_log_two hleft)
  · exact hu (goldfeldLogKernel_eq_zero_of_pos hright)

private theorem goldfeldLogKernel_hasCompactSupport :
    HasCompactSupport goldfeldLogKernel := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-Real.log 2) 0)
    isCompact_Icc
  exact goldfeldLogKernel_support_subset

private noncomputable def goldfeldLogKernelSchwartz : 𝓢(ℝ, ℂ) :=
  goldfeldLogKernel_hasCompactSupport.toSchwartzMap goldfeldLogKernel_contDiff

private theorem goldfeldDerivativeMellin_on_neg_one (t : ℝ) :
    goldfeldDerivativeMellin ((-1 : ℂ) + t * I) =
      𝓕 goldfeldLogKernelSchwartz (t / (2 * π)) := by
  calc
    goldfeldDerivativeMellin ((-1 : ℂ) + t * I) =
        mellin goldfeldMellinDerivativeWeight ((-1 : ℂ) + t * I) :=
      goldfeldDerivativeMellin_eq_weight _
    _ = 𝓕 (fun u : ℝ =>
        Real.exp (-((-1 : ℂ) + t * I).re * u) •
          goldfeldMellinDerivativeWeight (Real.exp (-u)))
        (((-1 : ℂ) + t * I).im / (2 * π)) :=
      mellin_eq_fourier goldfeldMellinDerivativeWeight
    _ = 𝓕 goldfeldLogKernelSchwartz (t / (2 * π)) := by
      norm_num
      rw [SchwartzMap.fourier_coe]
      apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * π)))
      funext u
      simp [goldfeldLogKernelSchwartz, goldfeldLogKernel]

private theorem schwartz_pointwise_bound (f : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖(f : ℝ → ℂ) x‖ ≤ C / (1 + |x|) ^ A := by
  obtain ⟨C, hC, hbound⟩ := f.decay A 0
  obtain ⟨C0, hC0, hbound0⟩ := f.decay 0 0
  refine ⟨max (C * 2 ^ A) (C0 * 2 ^ A), by positivity, ?_⟩
  intro x
  by_cases hx : 1 ≤ |x|
  · have hpow : (1 + |x|) ^ A ≤ (2 * |x|) ^ A := by
      apply pow_le_pow_left₀ (by positivity) _ _
      linarith
    have hprod := hbound x
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hprod
    have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hx
    have hnorm : ‖(f : ℝ → ℂ) x‖ ≤ C / |x| ^ A := by
      apply (le_div_iff₀ (pow_pos hxpos A)).2
      simpa [mul_comm] using hprod
    calc
      ‖(f : ℝ → ℂ) x‖ ≤ C / |x| ^ A := hnorm
      _ ≤ (C * 2 ^ A) / (1 + |x|) ^ A := by
        apply (div_le_div_iff₀ (pow_pos hxpos A) (by positivity)).2
        calc
          C * (1 + |x|) ^ A ≤ C * (2 * |x|) ^ A :=
            mul_le_mul_of_nonneg_left hpow hC.le
          _ = (C * 2 ^ A) * |x| ^ A := by rw [mul_pow]; ring
      _ ≤ max (C * 2 ^ A) (C0 * 2 ^ A) / (1 + |x|) ^ A := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hx' : |x| < 1 := lt_of_not_ge hx
    have h0 := hbound0 x
    have h0' : ‖(f : ℝ → ℂ) x‖ ≤ C0 := by
      simpa [norm_iteratedFDeriv_zero] using h0
    have hsmall : C0 ≤ C0 * 2 ^ A / (1 + |x|) ^ A := by
      have hden : (1 + |x|) ^ A ≤ 2 ^ A := by
        apply pow_le_pow_left₀ (by positivity) _ _
        linarith
      have hdenpos : 0 < (1 + |x|) ^ A := by positivity
      apply (le_div_iff₀ hdenpos).2
      exact mul_le_mul_of_nonneg_left hden hC0.le
    have hmax : C0 * 2 ^ A / (1 + |x|) ^ A ≤
        max (C * 2 ^ A) (C0 * 2 ^ A) / (1 + |x|) ^ A := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    calc
      ‖(f : ℝ → ℂ) x‖ ≤ C0 := h0'
      _ ≤ C0 * 2 ^ A / (1 + |x|) ^ A := hsmall
      _ ≤ max (C * 2 ^ A) (C0 * 2 ^ A) / (1 + |x|) ^ A := hmax

theorem goldfeldMellinCandidate_decay_on_neg_one (A : ℕ) (_hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖goldfeldMellinCandidate ((-1 : ℂ) + t * I)‖ ≤ C / (1 + |t|) ^ A := by
  obtain ⟨C, hC, hpoint⟩ :=
    schwartz_pointwise_bound (𝓕 goldfeldLogKernelSchwartz) A
  refine ⟨C * (2 * π) ^ A, by positivity, ?_⟩
  intro t
  have hs : ((-1 : ℂ) + t * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hnorms : 1 ≤ ‖(-1 : ℂ) + t * I‖ := by
    have h := Complex.abs_re_le_norm ((-1 : ℂ) + t * I)
    norm_num at h ⊢
    exact h
  rw [goldfeldMellinCandidate, norm_div, norm_neg]
  calc
    ‖goldfeldDerivativeMellin ((-1 : ℂ) + t * I)‖ /
        ‖(-1 : ℂ) + t * I‖ ≤
      ‖goldfeldDerivativeMellin ((-1 : ℂ) + t * I)‖ :=
        (div_le_self (norm_nonneg _) hnorms)
    _ = ‖𝓕 goldfeldLogKernelSchwartz (t / (2 * π))‖ := by
      rw [goldfeldDerivativeMellin_on_neg_one]
    _ ≤ C / (1 + |t / (2 * π)|) ^ A := hpoint _
    _ ≤ C * (2 * π) ^ A / (1 + |t|) ^ A := by
      have hpi : 0 < (2 * π : ℝ) := by positivity
      have hpi1 : (1 : ℝ) ≤ 2 * π := by
        nlinarith [two_le_pi]
      rw [abs_div, abs_of_pos hpi]
      have hscale : 1 + |t| ≤ (2 * π) * (1 + |t| / (2 * π)) := by
        rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hpi)]
        nlinarith
      have hpowscale : (1 + |t|) ^ A ≤
          ((2 * π) * (1 + |t| / (2 * π))) ^ A :=
        pow_le_pow_left₀ (by positivity) hscale A
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      calc
        C * (1 + |t|) ^ A ≤
            C * ((2 * π) ^ A * (1 + |t| / (2 * π)) ^ A) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          simpa [mul_pow] using hpowscale
        _ = (C * (2 * π) ^ A) * (1 + |t| / (2 * π)) ^ A := by ring

/-- The complete source-facing continuation package for Goldfeld's cutoff. -/
noncomputable def goldfeldMellinContinuationData :
    GoldfeldMellinContinuationData :=
  goldfeldMellinContinuationData_of_decay
    goldfeldMellinCandidate_decay_on_neg_one

end BoundedGaps.Maynard
