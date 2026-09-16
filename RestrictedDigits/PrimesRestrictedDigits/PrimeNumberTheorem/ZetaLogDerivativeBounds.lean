import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLogDerivativeHigh
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLogDerivativeLow

/-!
# Zero-free and logarithmic-derivative constants for zeta

This packages the parts of `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6,
Theorems 6.6--6.7 used in the quantitative prime number theorem. One constant
controls the zero-free region and both narrower derivative strips.
-/

open Complex

namespace PrimesRestrictedDigits

/-- There are common absolute constants for the zeta zero-free region, the
high-height logarithmic derivative, and its low-height pole regularization. -/
theorem exists_riemannZeta_logDeriv_bounds :
    ∃ c C : Real,
      IsRiemannZetaZeroFreeConstant c ∧ 0 < C ∧
      (∀ t sigma : Real,
        7 / 8 ≤ |t| →
        1 - c / (2 * Real.log (|t| + 4)) < sigma →
        norm
          (logDeriv riemannZeta
            ((sigma : Complex) + Complex.I * (t : Complex))) ≤
          C * Real.log (|t| + 4)) ∧
      ∀ t sigma : Real,
        |t| ≤ 7 / 8 →
        1 - c / (2 * Real.log (|t| + 4)) < sigma →
        sigma ≤ 2 →
        ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 1 →
        norm
          (logDeriv riemannZeta
              ((sigma : Complex) + Complex.I * (t : Complex)) +
            1 / (((sigma : Complex) + Complex.I * (t : Complex)) - 1)) ≤ C := by
  obtain ⟨c, hc⟩ := exists_isRiemannZetaZeroFreeConstant
  obtain ⟨Chigh, hChighPos, hHigh⟩ :=
    exists_riemannZeta_high_logDeriv_bound c hc
  obtain ⟨Clow, hClowPos, hLow⟩ :=
    exists_riemannZeta_low_logDeriv_bound c hc
  let C : Real := max Chigh Clow
  have hCPos : 0 < C := hChighPos.trans_le (by exact le_max_left _ _)
  refine ⟨c, C, hc, hCPos, ?_, ?_⟩
  · intro t sigma hT hSigma
    have hBound := hHigh t sigma hT hSigma
    calc
      norm
          (logDeriv riemannZeta
            ((sigma : Complex) + Complex.I * (t : Complex))) ≤
          Chigh * Real.log (|t| + 4) := hBound
      _ ≤ C * Real.log (|t| + 4) := by
        apply mul_le_mul_of_nonneg_right (le_max_left _ _)
        exact (Real.log_pos (by linarith [abs_nonneg t])).le
  · intro t sigma hT hSigma hSigmaUpper hsOne
    exact (hLow t sigma hT hSigma hSigmaUpper hsOne).trans (le_max_right _ _)

end PrimesRestrictedDigits
