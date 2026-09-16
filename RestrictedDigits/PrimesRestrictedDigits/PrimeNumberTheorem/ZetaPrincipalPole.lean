import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLogDerivativeBounds

/-!
# An arbitrary-height principal pole bound for zeta

This repairs the low-height gap in the principal branch of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Lemma 11.1. The exact pole is retained,
while the high- and low-height estimates come from the independently proved
clauses of Chapter 6, Theorem 6.7.
-/

open Complex

namespace PrimesRestrictedDigits

/-- The negative real part of the zeta logarithmic derivative is bounded by
its exact coefficient-one pole plus one logarithmic height error. -/
theorem exists_neg_re_logDeriv_riemannZeta_le_pole_add_log :
    ∃ A : Real, 0 < A ∧
      ∀ delta t : Real, 0 < delta → delta ≤ 1 →
        (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex) +
            Complex.I * (t : Complex))).re ≤
          delta / (delta ^ 2 + t ^ 2) +
            A * Real.log (|t| + 4) := by
  obtain ⟨c, C, hc, hCPos, hHigh, hLow⟩ :=
    exists_riemannZeta_logDeriv_bounds
  refine ⟨C, hCPos, ?_⟩
  intro delta t hDeltaPos hDeltaLe
  let sigma : Real := 1 + delta
  let s : Complex := (sigma : Complex) + Complex.I * t
  let tau : Real := |t| + 4
  have hLogOne : 1 < Real.log tau := by
    dsimp [tau]
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hLogPos : 0 < Real.log tau := zero_lt_one.trans hLogOne
  have hSigmaOne : 1 < sigma := by
    dsimp [sigma]
    linarith
  have hSigmaTwo : sigma ≤ 2 := by
    dsimp [sigma]
    linarith
  have hStrip : 1 - c / (2 * Real.log tau) < sigma := by
    have hFractionPos : 0 < c / (2 * Real.log tau) := by
      exact div_pos hc.1 (mul_pos (by norm_num) hLogPos)
    linarith
  have hsOne : s ≠ 1 := by
    intro hs
    have hRe := congrArg Complex.re hs
    dsimp [s] at hRe
    norm_num at hRe
    linarith
  have hPoleDenomPos : 0 < delta ^ 2 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hPoleNonneg : 0 ≤ delta / (delta ^ 2 + t ^ 2) :=
    (div_pos hDeltaPos hPoleDenomPos).le
  have hPoleRe :
      (1 / (s - 1)).re = delta / (delta ^ 2 + t ^ 2) := by
    dsimp [s, sigma]
    simp [Complex.normSq_apply, pow_two]
  by_cases hT : 7 / 8 ≤ |t|
  · have hBound := hHigh t sigma hT (by simpa [tau] using hStrip)
    have hNegRe :
        (-logDeriv riemannZeta s).re ≤ C * Real.log tau := by
      calc
        (-logDeriv riemannZeta s).re ≤
            ‖-logDeriv riemannZeta s‖ := Complex.re_le_norm _
        _ = ‖logDeriv riemannZeta s‖ := norm_neg _
        _ ≤ C * Real.log tau := by simpa [s, tau] using hBound
    change (-logDeriv riemannZeta s).re ≤
      delta / (delta ^ 2 + t ^ 2) + C * Real.log tau
    linarith
  · have hTLow : |t| ≤ 7 / 8 := le_of_not_ge hT
    have hBound := hLow t sigma hTLow (by simpa [tau] using hStrip)
      hSigmaTwo (by simpa [s] using hsOne)
    have hRegularizedRe :
        -(logDeriv riemannZeta s + 1 / (s - 1)).re ≤ C := by
      calc
        -(logDeriv riemannZeta s + 1 / (s - 1)).re ≤
            |(logDeriv riemannZeta s + 1 / (s - 1)).re| :=
          neg_le_abs _
        _ ≤ ‖logDeriv riemannZeta s + 1 / (s - 1)‖ :=
          Complex.abs_re_le_norm _
        _ ≤ C := by simpa [s] using hBound
    have hCAbsorb : C ≤ C * Real.log tau := by
      nlinarith
    have hIdentity :
        (-logDeriv riemannZeta s).re =
          (1 / (s - 1)).re -
            (logDeriv riemannZeta s + 1 / (s - 1)).re := by
      simp only [Complex.neg_re, Complex.add_re]
      ring
    change (-logDeriv riemannZeta s).re ≤
      delta / (delta ^ 2 + t ^ 2) + C * Real.log tau
    rw [hIdentity, hPoleRe]
    linarith

end PrimesRestrictedDigits
