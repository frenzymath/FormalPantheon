import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLocalZeroSumReal
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLogDerivPositivity
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFreeLow

/-!
# High-height zeta-zero distance

This file proves the high-height quantitative step in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Theorem 6.6.  It combines the sharp
coefficient-one pole anchor, Lemmas 6.4 and 6.5, and positivity of the local
multiplicity-weighted zero sum.
-/

open Complex

namespace PrimesRestrictedDigits

/-- A zeta zero of height at least `7 / 8` and real part at least `5 / 6`
has an absolute logarithmic distance from the line `re s = 1`. -/
theorem exists_riemannZeta_high_zero_distance :
    ∃ K : Real, 1 ≤ K ∧
      ∀ t beta : Real,
        7 / 8 ≤ |t| →
        5 / 6 ≤ beta →
        riemannZeta
          ((beta : Complex) + Complex.I * (t : Complex)) = 0 →
        1 / (14 * K * Real.log (|t| + 4)) ≤ 1 - beta := by
  obtain ⟨B, hBPos, hPole⟩ := exists_neg_re_logDeriv_riemannZeta_le
  obtain ⟨C, hCPos, hLocal⟩ :=
    riemannZeta_logDeriv_localZeroSum_bound
  let K : Real := 3 * B + 6 * C + 1
  have hK : 1 ≤ K := by
    dsimp [K]
    nlinarith
  have hKPos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨K, hK, ?_⟩
  intro t beta hT hBeta hZero
  let L : Real := Real.log (|t| + 4)
  have hLOne : 1 < L := by
    dsimp [L]
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hLPos : 0 < L := zero_lt_one.trans hLOne
  have hBetaOne : beta < 1 := by
    by_contra hBetaOne
    exact riemannZeta_ne_zero_of_one_le_re
      (s := (beta : Complex) + Complex.I * (t : Complex))
      (by simpa using not_lt.mp hBetaOne) hZero
  let delta : Real := 1 / (2 * K * L)
  have hTwoKLPos : 0 < 2 * K * L := by positivity
  have hDeltaPos : 0 < delta := by
    dsimp [delta]
    positivity
  have hKL : 1 ≤ K * L := by
    calc
      (1 : Real) = 1 * 1 := by ring
      _ ≤ K * L := mul_le_mul hK hLOne.le (by positivity) (by positivity)
  have hDeltaLe : delta ≤ 1 := by
    dsimp [delta]
    rw [div_le_one hTwoKLPos]
    nlinarith
  have hSigmaLower : 5 / 6 ≤ 1 + delta := by linarith
  have hSigmaUpper : 1 + delta ≤ 2 := by linarith
  have hSigmaOne : 1 < 1 + delta := by linarith
  have hZetaT : riemannZeta
      (((1 + delta : Real) : Complex) + Complex.I * (t : Complex)) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simpa using hSigmaOne.le
  have hLocalT := hLocal t (1 + delta) hT hSigmaLower hSigmaUpper hZetaT
  have hSelected := one_div_sub_le_riemannZetaLocalZeroSum_re
    (t := t) (beta := beta) (sigma := 1 + delta)
    hT hBeta hZero hSigmaOne
  have hErrorT :
      -(C * L) ≤
        (logDeriv riemannZeta
            (((1 + delta : Real) : Complex) + Complex.I * (t : Complex)) -
          riemannZetaLocalZeroSum t
            (((1 + delta : Real) : Complex) +
              Complex.I * (t : Complex))).re := by
    have hAbs := Complex.abs_re_le_norm
      (logDeriv riemannZeta
          (((1 + delta : Real) : Complex) + Complex.I * (t : Complex)) -
        riemannZetaLocalZeroSum t
          (((1 + delta : Real) : Complex) +
            Complex.I * (t : Complex)))
    have hAbsBound :
        |(logDeriv riemannZeta
              (((1 + delta : Real) : Complex) + Complex.I * (t : Complex)) -
            riemannZetaLocalZeroSum t
              (((1 + delta : Real) : Complex) +
                Complex.I * (t : Complex))).re| ≤ C * L :=
      hAbs.trans (by simpa [L] using hLocalT)
    exact neg_le_of_abs_le hAbsBound
  have hAtT :
      (-logDeriv riemannZeta
        (((1 + delta : Real) : Complex) + Complex.I * (t : Complex))).re ≤
          -(1 / (1 + delta - beta)) + C * L := by
    have hIdentity :
        (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex) +
            Complex.I * (t : Complex))).re =
          -(riemannZetaLocalZeroSum t
            (((1 + delta : Real) : Complex) +
              Complex.I * (t : Complex))).re -
          (logDeriv riemannZeta
              (((1 + delta : Real) : Complex) +
                Complex.I * (t : Complex)) -
            riemannZetaLocalZeroSum t
              (((1 + delta : Real) : Complex) +
                Complex.I * (t : Complex))).re := by
      simp
      ring
    rw [hIdentity]
    linarith
  have hTDouble : 7 / 8 ≤ |2 * t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
    linarith
  have hZetaDouble : riemannZeta
      (((1 + delta : Real) : Complex) +
        Complex.I * ((2 * t : Real) : Complex)) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simpa using hSigmaOne.le
  have hLocalDouble := hLocal (2 * t) (1 + delta) hTDouble
    hSigmaLower hSigmaUpper hZetaDouble
  have hSumDouble := riemannZetaLocalZeroSum_re_nonneg
    (t := 2 * t) (sigma := 1 + delta) hTDouble hSigmaOne
  have hErrorDouble :
      -(C * Real.log (|2 * t| + 4)) ≤
        (logDeriv riemannZeta
            (((1 + delta : Real) : Complex) +
              Complex.I * ((2 * t : Real) : Complex)) -
          riemannZetaLocalZeroSum (2 * t)
            (((1 + delta : Real) : Complex) +
              Complex.I * ((2 * t : Real) : Complex))).re := by
    have hAbs := Complex.abs_re_le_norm
      (logDeriv riemannZeta
          (((1 + delta : Real) : Complex) +
            Complex.I * ((2 * t : Real) : Complex)) -
        riemannZetaLocalZeroSum (2 * t)
          (((1 + delta : Real) : Complex) +
            Complex.I * ((2 * t : Real) : Complex)))
    exact neg_le_of_abs_le (hAbs.trans hLocalDouble)
  have hAtDouble :
      (-logDeriv riemannZeta
        (((1 + delta : Real) : Complex) +
          Complex.I * ((2 * t : Real) : Complex))).re ≤
        C * Real.log (|2 * t| + 4) := by
    have hIdentity :
        (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex) +
            Complex.I * ((2 * t : Real) : Complex))).re =
          -(riemannZetaLocalZeroSum (2 * t)
            (((1 + delta : Real) : Complex) +
              Complex.I * ((2 * t : Real) : Complex))).re -
          (logDeriv riemannZeta
              (((1 + delta : Real) : Complex) +
                Complex.I * ((2 * t : Real) : Complex)) -
            riemannZetaLocalZeroSum (2 * t)
              (((1 + delta : Real) : Complex) +
                Complex.I * ((2 * t : Real) : Complex))).re := by
      simp
      ring
    rw [hIdentity]
    linarith
  have hDoubleArgument : |2 * t| + 4 ≤ (|t| + 4) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
    nlinarith [sq_nonneg |t|, abs_nonneg t]
  have hDoubleLog : Real.log (|2 * t| + 4) ≤ 2 * L := by
    calc
      Real.log (|2 * t| + 4) ≤ Real.log ((|t| + 4) ^ 2) :=
        Real.log_le_log (by positivity) hDoubleArgument
      _ = 2 * L := by simp [L, Real.log_pow]
  have hAtDoubleL :
      (-logDeriv riemannZeta
        (((1 + delta : Real) : Complex) +
          Complex.I * ((2 * t : Real) : Complex))).re ≤ 2 * C * L := by
    calc
      _ ≤ C * Real.log (|2 * t| + 4) := hAtDouble
      _ ≤ C * (2 * L) := mul_le_mul_of_nonneg_left hDoubleLog hCPos.le
      _ = 2 * C * L := by ring
  have hPoleDelta := hPole delta hDeltaPos hDeltaLe
  have hCombination :=
    riemannZeta_logDeriv_combination_re_nonneg hSigmaOne t
  have hCombination' :
      0 ≤
        3 * (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex))).re +
        4 * (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex) +
            Complex.I * (t : Complex))).re +
        (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex) +
            Complex.I * ((2 * t : Real) : Complex))).re := by
    rw [show
      (-3 * logDeriv riemannZeta (((1 + delta : Real) : Complex)) -
          4 * logDeriv riemannZeta
            (((1 + delta : Real) : Complex) + Complex.I * (t : Complex)) -
          logDeriv riemannZeta
            (((1 + delta : Real) : Complex) +
              2 * Complex.I * (t : Complex))).re =
        3 * (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex))).re +
        4 * (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex) +
            Complex.I * (t : Complex))).re +
        (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex) +
            Complex.I * ((2 * t : Real) : Complex))).re by
        simp [Complex.mul_re]
        ring_nf] at hCombination
    exact hCombination
  have hRawExpanded :
      0 ≤ 3 * (1 / delta + B) +
        4 * (-(1 / (1 + delta - beta)) + C * L) +
        2 * C * L := by
    linarith
  have hRaw :
      0 ≤ 3 / delta - 4 / (1 + delta - beta) +
        3 * B + 6 * C * L := by
    convert hRawExpanded using 1; ring
  have hBScale : 3 * B ≤ 3 * B * L := by
    exact le_mul_of_one_le_right (by positivity) hLOne.le
  have hErrorScale : 3 * B + 6 * C * L ≤ K * L := by
    dsimp [K]
    nlinarith
  have hMaster :
      0 ≤ 3 / delta - 4 / (1 + delta - beta) + K * L := by
    linarith
  have hThreeDelta : 3 / delta = 6 * K * L := by
    dsimp [delta]
    field_simp [hTwoKLPos.ne']; ring
  rw [hThreeDelta] at hMaster
  have hReciprocal :
      4 / (1 + delta - beta) ≤ 7 * K * L := by
    linarith
  have hDifferencePos : 0 < 1 + delta - beta := by linarith
  have hSevenKLPos : 0 < 7 * K * L := by positivity
  have hDistanceWithDelta :
      4 / (7 * K * L) ≤ 1 + delta - beta := by
    rw [div_le_iff₀ hSevenKLPos]
    have := (div_le_iff₀ hDifferencePos).mp hReciprocal
    nlinarith
  have hDifference :
      4 / (7 * K * L) - delta = 1 / (14 * K * L) := by
    dsimp [delta]
    field_simp [hKPos.ne', hLPos.ne']; ring
  rw [← hDifference]
  linarith

end PrimesRestrictedDigits
