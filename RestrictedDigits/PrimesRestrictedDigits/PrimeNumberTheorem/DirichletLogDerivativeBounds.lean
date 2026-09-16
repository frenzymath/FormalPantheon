import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletLocalZeroComparison
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletLogDerivativeRight

/-!
# Logarithmic-derivative bounds for decimal-smooth Dirichlet L-functions

This proves the no-exception specialization of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.4, Eq. (11.5). The
right-half-plane series and the local-zero comparison are assembled at the
anchor `1 + 1 / log (q * (|t| + 4)) + I * t`.
-/

open Complex

namespace PrimesRestrictedDigits

private lemma one_lt_log_level_mul_abs_add_four_logDeriv
    {q : Nat} [NeZero q] (t : Real) :
    1 < Real.log ((q : Real) * (|t| + 4)) := by
  have hq : (1 : Real) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hFour : (4 : Real) ≤ |t| + 4 := by
    linarith [abs_nonneg t]
  have hArgument : (4 : Real) ≤ (q : Real) * (|t| + 4) := by
    calc
      (4 : Real) = 1 * 4 := by ring
      _ ≤ (q : Real) * (|t| + 4) :=
        mul_le_mul hq hFour (by norm_num) (Nat.cast_nonneg q)
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  exact Real.exp_one_lt_three.trans (by linarith)

/-- At the right-hand anchor, the real part of the local
multiplicity-weighted zero sum is bounded uniformly by the logarithmic
level-height scale. -/
theorem exists_dirichletLFunctionLocalZeroSum_anchor_bound :
    ∃ D : Real, 0 < D ∧
      ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        chi ≠ 1 →
          ∀ t : Real,
            (dirichletLFunctionLocalZeroSum chi t
              (((1 + 1 / Real.log
                ((q : Real) * (|t| + 4)) : Real) : Complex) +
                Complex.I * (t : Complex))).re ≤
              D * Real.log ((q : Real) * (|t| + 4)) := by
  obtain ⟨B, hBPos, hRight⟩ :=
    exists_dirichletLFunction_logDeriv_right_bound
  obtain ⟨C0, hC0Pos, hLocal⟩ :=
    dirichletLFunction_logDeriv_localZeroSum_bound
  refine ⟨B + C0, add_pos hBPos hC0Pos, ?_⟩
  intro q _ chi hchi t
  let L : Real := Real.log ((q : Real) * (|t| + 4))
  let sigma : Real := 1 + 1 / L
  let s : Complex := (sigma : Complex) + Complex.I * t
  have hLOne : 1 < L := by
    simpa [L] using
      one_lt_log_level_mul_abs_add_four_logDeriv (q := q) t
  have hLPos : 0 < L := zero_lt_one.trans hLOne
  have hInvPos : 0 < 1 / L := by positivity
  have hInvLe : 1 / L ≤ 1 := (div_le_one hLPos).2 hLOne.le
  have hSigmaOne : 1 < sigma := by
    dsimp [sigma]
    linarith
  have hSigmaLower : 5 / 6 ≤ sigma := by linarith
  have hSigmaUpper : sigma ≤ 2 := by
    dsimp [sigma]
    linarith
  have hs : chi.LFunction s ≠ 0 := by
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (.inl hchi)
    simpa [s] using hSigmaOne.le
  have hRightAt := hRight chi t sigma (by simp [sigma, L])
  change norm (logDeriv chi.LFunction s) ≤ B * L at hRightAt
  have hLocalAt :=
    hLocal chi hchi t sigma hSigmaLower hSigmaUpper hs
  change norm
      (logDeriv chi.LFunction s -
        dirichletLFunctionLocalZeroSum chi t s) ≤ C0 * L at hLocalAt
  have hAggregate :
      (dirichletLFunctionLocalZeroSum chi t s).re ≤
        norm (logDeriv chi.LFunction s) +
          norm (logDeriv chi.LFunction s -
            dirichletLFunctionLocalZeroSum chi t s) := by
    have hMainRe := Complex.re_le_norm (logDeriv chi.LFunction s)
    have hErrorRe := neg_le_of_abs_le (Complex.abs_re_le_norm
      (logDeriv chi.LFunction s -
        dirichletLFunctionLocalZeroSum chi t s))
    have hIdentity :
        (dirichletLFunctionLocalZeroSum chi t s).re =
          (logDeriv chi.LFunction s).re -
            (logDeriv chi.LFunction s -
              dirichletLFunctionLocalZeroSum chi t s).re := by
      simp
    rw [hIdentity]
    linarith
  change (dirichletLFunctionLocalZeroSum chi t s).re ≤ (B + C0) * L
  calc
    (dirichletLFunctionLocalZeroSum chi t s).re ≤
        norm (logDeriv chi.LFunction s) +
          norm (logDeriv chi.LFunction s -
            dirichletLFunctionLocalZeroSum chi t s) := hAggregate
    _ ≤ B * L + C0 * L := add_le_add hRightAt hLocalAt
    _ = (B + C0) * L := by ring

/-- For a fixed decimal-smooth nonprincipal zero-free constant, the
logarithmic derivative is bounded throughout the closed half-width strip.
This is the restricted no-exception form of Montgomery--Vaughan Eq. (11.5). -/
theorem exists_decimalSmooth_nonprincipal_LFunction_logDeriv_bound
    {c : Real}
    (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c) :
    ∃ C : Real, 0 < C ∧
      ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q → chi ≠ 1 →
          ∀ t sigma : Real,
            1 - c / (2 * Real.log
              ((q : Real) * (|t| + 4))) ≤ sigma →
            norm (logDeriv chi.LFunction
              ((sigma : Complex) + Complex.I * (t : Complex))) ≤
              C * Real.log ((q : Real) * (|t| + 4)) := by
  obtain ⟨B, hBPos, hRight⟩ :=
    exists_dirichletLFunction_logDeriv_right_bound
  obtain ⟨D, hDPos, hAnchor⟩ :=
    exists_dirichletLFunctionLocalZeroSum_anchor_bound
  obtain ⟨E, hEPos, hComparison⟩ :=
    exists_decimalSmooth_dirichletLFunctionLocalZeroSum_sub_bound hc
  obtain ⟨C0, hC0Pos, hLocal⟩ :=
    dirichletLFunction_logDeriv_localZeroSum_bound
  let C : Real := B + E * D + 2 * C0
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCPos, ?_⟩
  intro q _ chi hSmooth hchi t sigma hSigmaStrip
  let L : Real := Real.log ((q : Real) * (|t| + 4))
  let sigma1 : Real := 1 + 1 / L
  let s : Complex := (sigma : Complex) + Complex.I * t
  let s1 : Complex := (sigma1 : Complex) + Complex.I * t
  have hLOne : 1 < L := by
    simpa [L] using
      one_lt_log_level_mul_abs_add_four_logDeriv (q := q) t
  have hLPos : 0 < L := zero_lt_one.trans hLOne
  have hInvPos : 0 < 1 / L := by positivity
  have hInvLe : 1 / L ≤ 1 := (div_le_one hLPos).2 hLOne.le
  have hSigma1One : 1 < sigma1 := by
    dsimp [sigma1]
    linarith
  by_cases hRightRegion : sigma1 ≤ sigma
  · have hBound := hRight chi t sigma
      (by simpa [sigma1, L] using hRightRegion)
    change norm (logDeriv chi.LFunction s) ≤ C * L
    calc
      norm (logDeriv chi.LFunction s) ≤ B * L := by
        simpa [s, L] using hBound
      _ ≤ C * L := by
        apply mul_le_mul_of_nonneg_right _ hLPos.le
        dsimp [C]
        nlinarith [mul_pos hEPos hDPos]
  · have hSigmaUpper : sigma ≤ sigma1 := (lt_of_not_ge hRightRegion).le
    have hDenominator : 1 < 2 * L := by linarith
    have hFractionLt : c / (2 * L) < 1 / 13 :=
      (div_lt_self hc.1 hDenominator).trans_le hc.2.1
    have hSigmaLower : 5 / 6 ≤ sigma := by
      have hStrip : 1 - c / (2 * L) ≤ sigma := by
        simpa [L] using hSigmaStrip
      linarith
    have hSigmaUpperTwo : sigma ≤ 2 := by
      have hSigma1Two : sigma1 ≤ 2 := by
        dsimp [sigma1]
        linarith
      exact hSigmaUpper.trans hSigma1Two
    have hHalfWidth : c / (2 * L) < c / L := by
      exact (div_lt_div_iff_of_pos_left hc.1
        (by positivity : 0 < 2 * L) hLPos).2 (by linarith)
    have hsNonzero : chi.LFunction s ≠ 0 := by
      apply hc.2.2 chi hSmooth hchi t sigma
      change 1 - c / L ≤ sigma
      have hStrip : 1 - c / (2 * L) ≤ sigma := by
        simpa [L] using hSigmaStrip
      linarith
    have hs1Nonzero : chi.LFunction s1 ≠ 0 := by
      apply DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (.inl hchi)
      simpa [s1] using hSigma1One.le
    have hSigma1Lower : 5 / 6 ≤ sigma1 := by linarith
    have hSigma1Upper : sigma1 ≤ 2 := by
      dsimp [sigma1]
      linarith
    have hError :=
      hLocal chi hchi t sigma hSigmaLower hSigmaUpperTwo hsNonzero
    change norm
      (logDeriv chi.LFunction s -
        dirichletLFunctionLocalZeroSum chi t s) ≤ C0 * L at hError
    have hError1 :=
      hLocal chi hchi t sigma1 hSigma1Lower hSigma1Upper hs1Nonzero
    change norm
      (logDeriv chi.LFunction s1 -
        dirichletLFunctionLocalZeroSum chi t s1) ≤ C0 * L at hError1
    have hSumComparison :=
      hComparison chi hSmooth hchi t sigma hSigmaStrip
        (by simpa [sigma1, L] using hSigmaUpper)
    change norm
      (dirichletLFunctionLocalZeroSum chi t s -
        dirichletLFunctionLocalZeroSum chi t s1) ≤
          E * (dirichletLFunctionLocalZeroSum chi t s1).re at hSumComparison
    have hAnchorAt := hAnchor chi hchi t
    change (dirichletLFunctionLocalZeroSum chi t s1).re ≤ D * L at hAnchorAt
    have hRightAt := hRight chi t sigma1 (by simp [sigma1, L])
    change norm (logDeriv chi.LFunction s1) ≤ B * L at hRightAt
    let e : Complex :=
      logDeriv chi.LFunction s - dirichletLFunctionLocalZeroSum chi t s
    let z : Complex :=
      dirichletLFunctionLocalZeroSum chi t s -
        dirichletLFunctionLocalZeroSum chi t s1
    let e1 : Complex :=
      dirichletLFunctionLocalZeroSum chi t s1 - logDeriv chi.LFunction s1
    let a1 : Complex := logDeriv chi.LFunction s1
    have hDecomposition : logDeriv chi.LFunction s = e + z + e1 + a1 := by
      dsimp [e, z, e1, a1]
      ring
    have he : norm e ≤ C0 * L := by simpa [e] using hError
    have hz : norm z ≤ E * D * L := by
      calc
        norm z ≤ E * (dirichletLFunctionLocalZeroSum chi t s1).re := by
          simpa [z] using hSumComparison
        _ ≤ E * (D * L) := mul_le_mul_of_nonneg_left hAnchorAt hEPos.le
        _ = E * D * L := by ring
    have he1 : norm e1 ≤ C0 * L := by
      have : e1 =
          -(logDeriv chi.LFunction s1 -
            dirichletLFunctionLocalZeroSum chi t s1) := by
        dsimp [e1]
        ring
      rw [this, norm_neg]
      exact hError1
    have ha1 : norm a1 ≤ B * L := by simpa [a1] using hRightAt
    rw [hDecomposition]
    calc
      norm (e + z + e1 + a1) ≤ norm (e + z + e1) + norm a1 :=
        norm_add_le _ _
      _ ≤ (norm (e + z) + norm e1) + norm a1 := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((norm e + norm z) + norm e1) + norm a1 := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((C0 * L + E * D * L) + C0 * L) + B * L := by
        gcongr
      _ = C * L := by
        dsimp [C]
        ring

/-- There are jointly chosen constants for the decimal-smooth nonprincipal
zero-free region and its logarithmic-derivative bound. -/
theorem exists_decimalSmooth_nonprincipal_LFunction_logDeriv_bounds :
    ∃ c C : Real,
      IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c ∧
      0 < C ∧
      ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q → chi ≠ 1 →
          ∀ t sigma : Real,
            1 - c / (2 * Real.log
              ((q : Real) * (|t| + 4))) ≤ sigma →
            norm (logDeriv chi.LFunction
              ((sigma : Complex) + Complex.I * (t : Complex))) ≤
              C * Real.log ((q : Real) * (|t| + 4)) := by
  obtain ⟨c, hc⟩ :=
    exists_isDecimalSmoothNonprincipalLFunctionZeroFreeConstant
  obtain ⟨C, hCPos, hBound⟩ :=
    exists_decimalSmooth_nonprincipal_LFunction_logDeriv_bound hc
  exact ⟨c, C, hc, hCPos, hBound⟩

end PrimesRestrictedDigits
