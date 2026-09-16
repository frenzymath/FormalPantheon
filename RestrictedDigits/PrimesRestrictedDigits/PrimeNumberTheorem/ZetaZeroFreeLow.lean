import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaFractionalPart
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaRegularized

/-!
# Low-height nonvanishing and pole regularization for zeta

This file proves the fixed-height part of `MONTGOMERY-VAUGHAN-MNT-I`,
Chapter 6, Theorems 6.6--6.7.  Equation (6.5) excludes zeros in the
low-height rectangle.  The entire regularized zeta function then gives the
sharp coefficient-one pole bound used in the `3-4-1` argument.
-/

open Complex Set

namespace PrimesRestrictedDigits

/-- Zeta does not vanish in the fixed rectangle used for the low-height part
of Montgomery--Vaughan, Chapter 6, Theorem 6.6. -/
theorem riemannZeta_ne_zero_of_low_rectangle
    {sigma t : Real} (hSigmaLower : 8 / 9 <= sigma)
    (hSigmaUpper : sigma <= 1) (hT : |t| <= 7 / 8) :
    riemannZeta
      ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 0 := by
  let s : Complex := (sigma : Complex) + Complex.I * t
  by_cases hSigmaOne : sigma = 1
  · apply riemannZeta_ne_zero_of_one_le_re
    dsimp [s]
    norm_num [hSigmaOne]
  · have hSigmaLt : sigma < 1 := lt_of_le_of_ne hSigmaUpper hSigmaOne
    have hSigmaPos : 0 < sigma := by linarith
    have hsRe : s.re = sigma := by simp [s]
    have hsOne : s ≠ 1 := by
      intro hs
      have := congrArg Complex.re hs
      simp [s] at this
      exact hSigmaOne this
    have hTSqAbs : |t| ^ 2 <= (7 / 8 : Real) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg t) (by norm_num)).2 hT
    have hTSq : t ^ 2 <= (7 / 8 : Real) ^ 2 := by
      simpa only [sq_abs] using hTSqAbs
    have hNormSq : norm (s - 1) ^ 2 = (sigma - 1) ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [s]
      ring
    have hNormLt : norm (s - 1) < sigma := by
      have hNormNonneg : 0 <= norm (s - 1) := norm_nonneg _
      nlinarith [sq_nonneg (sigma - 8 / 9)]
    have hEstimate :=
      norm_riemannZeta_sub_self_div_sub_one_le
        (s := s) (hsRe.symm ▸ hSigmaPos) hsOne
    intro hZero
    have hsZero : s ≠ 0 := by
      intro hs
      have := congrArg Complex.re hs
      simp [s] at this
      linarith
    have hPoleNorm : norm (s / (s - 1)) = norm s / norm (s - 1) :=
      norm_div _ _
    have hStrict : norm s / sigma < norm (s / (s - 1)) := by
      rw [hPoleNorm]
      exact (div_lt_div_iff_of_pos_left (norm_pos_iff.mpr hsZero)
        hSigmaPos (norm_pos_iff.mpr (sub_ne_zero.mpr hsOne))).2 hNormLt
    rw [hZero, zero_sub, norm_neg, hsRe] at hEstimate
    exact (not_lt_of_ge hEstimate) hStrict

/-- The regularized zeta function is nonzero on the full low-height rectangle
used for the compact logarithmic-derivative bound. -/
theorem regularizedRiemannZeta_ne_zero_of_low_rectangle
    {sigma t : Real} (hSigmaLower : 8 / 9 <= sigma)
    (_hSigmaUpper : sigma <= 2) (hT : |t| <= 7 / 8) :
    regularizedRiemannZeta
      ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 0 := by
  let s : Complex := (sigma : Complex) + Complex.I * t
  by_cases hsOne : s = 1
  · change regularizedRiemannZeta s ≠ 0
    rw [hsOne]
    norm_num [regularizedRiemannZeta_one]
  · rw [show regularizedRiemannZeta
        ((sigma : Complex) + Complex.I * (t : Complex)) =
          (s - 1) * riemannZeta s by
        simpa [s] using regularizedRiemannZeta_apply_of_ne hsOne]
    apply mul_ne_zero (sub_ne_zero.mpr hsOne)
    by_cases hSigma : sigma <= 1
    · simpa [s] using
        riemannZeta_ne_zero_of_low_rectangle hSigmaLower hSigma hT
    · apply riemannZeta_ne_zero_of_one_le_re
      dsimp [s]
      norm_num
      linarith

/-- The logarithmic derivative of regularized zeta has one positive uniform
norm bound on the closed low-height rectangle. -/
theorem exists_regularizedRiemannZeta_logDeriv_bound :
    ∃ B : Real, 0 < B ∧
      ∀ sigma t : Real,
        8 / 9 <= sigma →
        sigma <= 2 →
        |t| <= 7 / 8 →
        norm
          (logDeriv regularizedRiemannZeta
            ((sigma : Complex) + Complex.I * (t : Complex))) <= B := by
  let K : Set Complex :=
    Set.Icc (8 / 9 : Real) 2 ×ℂ Set.Icc (-7 / 8 : Real) (7 / 8)
  have hKCompact : IsCompact K := by
    exact isCompact_Icc.reProdIm isCompact_Icc
  have hNonzero : ∀ s ∈ K, regularizedRiemannZeta s ≠ 0 := by
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    have hRe := hs.1
    have hIm := hs.2
    rw [Set.mem_Icc] at hRe hIm
    have hT : |s.im| <= 7 / 8 := by
      rw [abs_le]
      constructor <;> linarith [hIm.1, hIm.2]
    have hsCoord : ((s.re : Complex) + Complex.I * (s.im : Complex)) = s := by
      apply Complex.ext <;> simp
    rw [← hsCoord]
    exact regularizedRiemannZeta_ne_zero_of_low_rectangle
      hRe.1 hRe.2 hT
  have hF : AnalyticOnNhd Complex regularizedRiemannZeta K :=
    analyticOnNhd_regularizedRiemannZeta.mono (Set.subset_univ K)
  have hLogDeriv : AnalyticOnNhd Complex
      (logDeriv regularizedRiemannZeta) K := by
    change AnalyticOnNhd Complex
      (fun s : Complex => deriv regularizedRiemannZeta s /
        regularizedRiemannZeta s) K
    exact hF.deriv.div hF hNonzero
  obtain ⟨B0, hB0⟩ :=
    hKCompact.exists_bound_of_continuousOn hLogDeriv.continuousOn
  refine ⟨max B0 1, by positivity, ?_⟩
  intro sigma t hSigmaLower hSigmaUpper hT
  apply (hB0
    ((sigma : Complex) + Complex.I * (t : Complex)) ?_).trans
    (le_max_left B0 1)
  rw [Complex.mem_reProdIm]
  constructor
  · simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, zero_mul,
      I_im, one_mul,  Set.mem_Icc]
    norm_num
    exact ⟨hSigmaLower, hSigmaUpper⟩
  · simp only [add_im, ofReal_im, mul_im, I_re, zero_mul, I_im,
      ofReal_re, one_mul, zero_add, Set.mem_Icc]
    norm_num
    constructor <;> linarith [abs_le.mp hT |>.1, abs_le.mp hT |>.2]

/-- The real pole anchor supplied by the regularized logarithmic derivative.
The coefficient of `1 / delta` is exactly one. -/
theorem exists_neg_re_logDeriv_riemannZeta_le :
    ∃ B : Real, 0 < B ∧
      ∀ delta : Real, 0 < delta → delta <= 1 →
        (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex))).re <= 1 / delta + B := by
  obtain ⟨B, hBPos, hB⟩ := exists_regularizedRiemannZeta_logDeriv_bound
  refine ⟨B, hBPos, ?_⟩
  intro delta hDeltaPos hDeltaLe
  let s : Complex := ((1 + delta : Real) : Complex)
  have hsOne : s ≠ 1 := by
    intro hs
    have hRe := congrArg Complex.re hs
    dsimp [s] at hRe
    norm_num at hRe
    linarith
  have hsRe : 1 < s.re := by
    dsimp [s]
    norm_num
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hsRe
  have hBound : norm (logDeriv regularizedRiemannZeta s) <= B := by
    have hBound' := hB (1 + delta) 0 (by linarith) (by linarith) (by norm_num)
    simpa [s] using hBound'
  have hIdentity := logDeriv_regularizedRiemannZeta_eq hsOne hzeta
  have hRealIdentity := congrArg Complex.re hIdentity
  have hPoleReal : (1 / (s - 1)).re = 1 / delta := by
    dsimp [s]
    norm_num [Complex.div_re]
  have hRegRe :
      -(logDeriv regularizedRiemannZeta s).re <= B := by
    have hAbs := Complex.abs_re_le_norm (logDeriv regularizedRiemannZeta s)
    have hNormAbs :
        |(logDeriv regularizedRiemannZeta s).re| <= B :=
      hAbs.trans hBound
    have hLower : -B <= (logDeriv regularizedRiemannZeta s).re :=
      neg_le_of_abs_le hNormAbs
    linarith
  dsimp [s] at hRealIdentity hRegRe ⊢
  rw [hPoleReal] at hRealIdentity
  norm_num at hRealIdentity
  simp only [one_div] at hRealIdentity ⊢
  have hRealIdentity' :
      (logDeriv regularizedRiemannZeta
          (((1 + delta : Real) : Complex))).re =
        delta⁻¹ +
          (logDeriv riemannZeta (((1 + delta : Real) : Complex))).re := by
    simpa [Complex.ofReal_add] using hRealIdentity
  linarith [hRealIdentity', hRegRe]

end PrimesRestrictedDigits
