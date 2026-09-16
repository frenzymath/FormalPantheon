import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFree

/-!
# The low-height logarithmic-derivative bound for zeta

This proves the low-height clause of `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6,
Theorem 6.7.  The pole at one is kept explicit, while the regularized zeta
function supplies a uniform bound on the containing closed rectangle.
-/

open Complex

namespace PrimesRestrictedDigits

/-- The pole-regularized logarithmic derivative of zeta is uniformly bounded
in the low-height half-width zero-free strip. -/
theorem exists_riemannZeta_low_logDeriv_bound
    (c : Real) (hc : IsRiemannZetaZeroFreeConstant c) :
    ∃ C : Real, 0 < C ∧
      ∀ t sigma : Real,
        |t| ≤ 7 / 8 →
        1 - c / (2 * Real.log (|t| + 4)) < sigma →
        sigma ≤ 2 →
        ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 1 →
        norm
            (logDeriv riemannZeta
                ((sigma : Complex) + Complex.I * (t : Complex)) +
              1 / (((sigma : Complex) + Complex.I * (t : Complex)) - 1)) ≤ C := by
  obtain ⟨B, hBPos, hB⟩ := exists_regularizedRiemannZeta_logDeriv_bound
  refine ⟨B, hBPos, ?_⟩
  intro t sigma hT hSigmaStrip hSigmaUpper hsOne
  have hLog : 1 < Real.log (|t| + 4) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hDenominator : 1 < 2 * Real.log (|t| + 4) := by
    linarith
  have hFractionLtC :
      c / (2 * Real.log (|t| + 4)) < c :=
    div_lt_self hc.1 hDenominator
  have hFractionLt :
      c / (2 * Real.log (|t| + 4)) < 1 / 9 :=
    hFractionLtC.trans_le hc.2.1
  have hSigmaLower : 8 / 9 ≤ sigma := by
    linarith
  have hRegularizedBound :=
    hB sigma t hSigmaLower hSigmaUpper hT
  have hRegularizedNe :=
    regularizedRiemannZeta_ne_zero_of_low_rectangle
      hSigmaLower hSigmaUpper hT
  have hZetaNe :
      riemannZeta
        ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 0 := by
    intro hZeta
    apply hRegularizedNe
    rw [regularizedRiemannZeta_apply_of_ne hsOne, hZeta, mul_zero]
  have hIdentity := logDeriv_regularizedRiemannZeta_eq hsOne hZetaNe
  have hRewrite :
      logDeriv riemannZeta
            ((sigma : Complex) + Complex.I * (t : Complex)) +
          1 / (((sigma : Complex) + Complex.I * (t : Complex)) - 1) =
        logDeriv regularizedRiemannZeta
          ((sigma : Complex) + Complex.I * (t : Complex)) := by
    rw [hIdentity]
    exact add_comm _ _
  rw [hRewrite]
  exact hRegularizedBound

end PrimesRestrictedDigits
