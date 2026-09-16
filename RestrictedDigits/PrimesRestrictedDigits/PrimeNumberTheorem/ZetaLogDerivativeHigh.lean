import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLocalZeroComparison
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLocalZeroSumAnchor

/-!
# The high-height logarithmic-derivative bound for zeta

This proves Eq. (6.6) of `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6,
Theorem 6.7. The local-zero comparison covers the narrow strip, while the
von Mangoldt Dirichlet series covers the full right half-plane.
-/

open Complex

namespace PrimesRestrictedDigits

/-- The zeta logarithmic derivative is bounded by an absolute multiple of
`log (|t| + 4)` throughout the high-height half-width zero-free region. -/
theorem exists_riemannZeta_high_logDeriv_bound
    (c : Real) (hc : IsRiemannZetaZeroFreeConstant c) :
    ∃ C : Real, 0 < C ∧
      ∀ t sigma : Real,
        7 / 8 ≤ |t| →
        1 - c / (2 * Real.log (|t| + 4)) < sigma →
        norm
          (logDeriv riemannZeta
            ((sigma : Complex) + Complex.I * (t : Complex))) ≤
          C * Real.log (|t| + 4) := by
  obtain ⟨A, hAPos, hRight⟩ :=
    exists_riemannZeta_logDeriv_right_bound
  obtain ⟨D, hDPos, hAnchor⟩ :=
    exists_riemannZetaLocalZeroSum_anchor_bound
  obtain ⟨E, hEPos, hComparison⟩ :=
    exists_riemannZetaLocalZeroSum_sub_bound hc
  obtain ⟨C0, hC0Pos, hLocal⟩ :=
    riemannZeta_logDeriv_localZeroSum_bound
  let C : Real := A + E * D + 2 * C0
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCPos, ?_⟩
  intro t sigma hT hSigmaStrip
  let L : Real := Real.log (|t| + 4)
  let sigma1 : Real := 1 + 1 / L
  let s : Complex := (sigma : Complex) + Complex.I * t
  let s1 : Complex := (sigma1 : Complex) + Complex.I * t
  have hLOne : 1 < L := by
    dsimp [L]
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hLPos : 0 < L := zero_lt_one.trans hLOne
  have hInvPos : 0 < 1 / L := by positivity
  have hInvLe : 1 / L ≤ 1 := (div_le_one hLPos).2 hLOne.le
  have hSigma1One : 1 < sigma1 := by
    dsimp [sigma1]
    linarith
  by_cases hRightRegion : sigma1 ≤ sigma
  · have hBound := hRight t sigma (by simpa [sigma1, L] using hRightRegion)
    change norm (logDeriv riemannZeta s) ≤ C * L
    calc
      norm (logDeriv riemannZeta s) ≤ A * L := by simpa [s, L] using hBound
      _ ≤ C * L := by
        apply mul_le_mul_of_nonneg_right _ hLPos.le
        dsimp [C]
        nlinarith [mul_pos hEPos hDPos]
  · have hSigmaUpper : sigma ≤ sigma1 := (lt_of_not_ge hRightRegion).le
    have hDenominator : 1 < 2 * L := by linarith
    have hFractionLt : c / (2 * L) < 1 / 9 := by
      exact (div_lt_self hc.1 hDenominator).trans_le hc.2.1
    have hSigmaLower : 5 / 6 ≤ sigma := by
      have hStrip : 1 - c / (2 * L) < sigma := by
        simpa [L] using hSigmaStrip
      linarith
    have hSigmaUpperTwo : sigma ≤ 2 := by
      have hSigma1Two : sigma1 ≤ 2 := by
        dsimp [sigma1]
        linarith
      exact hSigmaUpper.trans hSigma1Two
    have hHalfWidth : c / (2 * L) < c / L := by
      exact (div_lt_div_iff_of_pos_left hc.1 (by positivity : 0 < 2 * L) hLPos).2
        (by linarith)
    have hsNonzero : riemannZeta s ≠ 0 := by
      apply hc.2.2 t sigma
      have hStrip : 1 - c / (2 * L) < sigma := by
        simpa [L] using hSigmaStrip
      linarith
    have hs1Nonzero : riemannZeta s1 ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simpa [s1] using hSigma1One.le
    have hSigma1Lower : 5 / 6 ≤ sigma1 := by linarith
    have hSigma1Upper : sigma1 ≤ 2 := by
      dsimp [sigma1]
      linarith
    have hError :=
      hLocal t sigma hT hSigmaLower hSigmaUpperTwo hsNonzero
    change norm
      (logDeriv riemannZeta s - riemannZetaLocalZeroSum t s) ≤ C0 * L at hError
    have hError1 :=
      hLocal t sigma1 hT hSigma1Lower hSigma1Upper hs1Nonzero
    change norm
      (logDeriv riemannZeta s1 - riemannZetaLocalZeroSum t s1) ≤ C0 * L at hError1
    have hSumComparison :=
      hComparison t sigma hT hSigmaStrip (by simpa [sigma1, L] using hSigmaUpper)
    change norm
      (riemannZetaLocalZeroSum t s - riemannZetaLocalZeroSum t s1) ≤
        E * (riemannZetaLocalZeroSum t s1).re at hSumComparison
    have hAnchorAt := hAnchor t hT
    change (riemannZetaLocalZeroSum t s1).re ≤ D * L at hAnchorAt
    have hRightAt := hRight t sigma1 (by simp [sigma1, L])
    change norm (logDeriv riemannZeta s1) ≤ A * L at hRightAt
    let e : Complex :=
      logDeriv riemannZeta s - riemannZetaLocalZeroSum t s
    let z : Complex :=
      riemannZetaLocalZeroSum t s - riemannZetaLocalZeroSum t s1
    let e1 : Complex :=
      riemannZetaLocalZeroSum t s1 - logDeriv riemannZeta s1
    let a1 : Complex := logDeriv riemannZeta s1
    have hDecomposition : logDeriv riemannZeta s = e + z + e1 + a1 := by
      dsimp [e, z, e1, a1]
      ring
    have he : norm e ≤ C0 * L := by simpa [e] using hError
    have hz : norm z ≤ E * D * L := by
      calc
        norm z ≤ E * (riemannZetaLocalZeroSum t s1).re := by
          simpa [z] using hSumComparison
        _ ≤ E * (D * L) := mul_le_mul_of_nonneg_left hAnchorAt hEPos.le
        _ = E * D * L := by ring
    have he1 : norm e1 ≤ C0 * L := by
      have : e1 = -(logDeriv riemannZeta s1 - riemannZetaLocalZeroSum t s1) := by
        dsimp [e1]
        ring
      rw [this, norm_neg]
      exact hError1
    have ha1 : norm a1 ≤ A * L := by simpa [a1] using hRightAt
    rw [hDecomposition]
    calc
      norm (e + z + e1 + a1) ≤ norm (e + z + e1) + norm a1 := norm_add_le _ _
      _ ≤ (norm (e + z) + norm e1) + norm a1 := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((norm e + norm z) + norm e1) + norm a1 := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((C0 * L + E * D * L) + C0 * L) + A * L := by
        gcongr
      _ = C * L := by
        dsimp [C]
        ring

end PrimesRestrictedDigits
