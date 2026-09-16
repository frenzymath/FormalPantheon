import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletLogDerivLocalBounds
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletLogDerivPositivity
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPrincipalPole

/-!
# Dirichlet zero separation: nonquadratic and quadratic far cases

This formalizes Cases 1--2 of `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11,
Theorem 11.3. The principal estimates use the independently repaired
arbitrary-height pole bound rather than the source's unsupported low-height
invocation of Lemma 6.4.
-/

open Complex

namespace PrimesRestrictedDigits

private lemma one_lt_log_level_mul_abs_add_four
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

private lemma log_level_mul_four_le_log_level_mul_abs_add_four
    {q : Nat} [NeZero q] (t : Real) :
    Real.log ((q : Real) * 4) ≤
      Real.log ((q : Real) * (|t| + 4)) := by
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply Real.log_le_log (mul_pos hqPos (by norm_num))
  exact mul_le_mul_of_nonneg_left
    (by linarith [abs_nonneg t]) hqPos.le

private lemma log_level_mul_double_abs_add_four_le
    {q : Nat} [NeZero q] (t : Real) :
    Real.log ((q : Real) * (|2 * t| + 4)) ≤
      2 * Real.log ((q : Real) * (|t| + 4)) := by
  let Q : Real := (q : Real) * (|t| + 4)
  have hq : (1 : Real) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqPos : (0 : Real) < q := zero_lt_one.trans_le hq
  have hFour : (4 : Real) ≤ |t| + 4 := by
    linarith [abs_nonneg t]
  have hQFour : (4 : Real) ≤ Q := by
    dsimp [Q]
    calc
      (4 : Real) = 1 * 4 := by ring
      _ ≤ (q : Real) * (|t| + 4) :=
        mul_le_mul hq hFour (by norm_num) (Nat.cast_nonneg q)
  have hInner : |2 * t| + 4 ≤ 2 * (|t| + 4) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
    linarith [abs_nonneg t]
  have hFirst :
      (q : Real) * (|2 * t| + 4) ≤ 2 * Q := by
    dsimp [Q]
    calc
      (q : Real) * (|2 * t| + 4) ≤
          (q : Real) * (2 * (|t| + 4)) :=
        mul_le_mul_of_nonneg_left hInner hqPos.le
      _ = 2 * ((q : Real) * (|t| + 4)) := by ring
  have hSecond : 2 * Q ≤ Q ^ 2 := by
    nlinarith [sq_nonneg (Q - 4)]
  calc
    Real.log ((q : Real) * (|2 * t| + 4)) ≤ Real.log (Q ^ 2) :=
      Real.log_le_log (by positivity) (hFirst.trans hSecond)
    _ = 2 * Real.log ((q : Real) * (|t| + 4)) := by
      simp [Q, Real.log_pow]

private lemma neg_logDeriv_combination_re_nonneg
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    {sigma : Real} (hSigma : 1 < sigma) (t : Real) :
    0 ≤
      3 * (-logDeriv (1 : DirichletCharacter Complex q).LFunction
          (sigma : Complex)).re +
        4 * (-logDeriv chi.LFunction
          ((sigma : Complex) + Complex.I * (t : Complex))).re +
        (-logDeriv (chi ^ 2).LFunction
          ((sigma : Complex) + Complex.I * ((2 * t : Real) : Complex))).re := by
  have hCombination :=
    dirichlet_logDeriv_combination_re_nonneg chi hSigma t
  rw [show
      (-3 * logDeriv (1 : DirichletCharacter Complex q).LFunction
          (sigma : Complex) -
        4 * logDeriv chi.LFunction
          ((sigma : Complex) + Complex.I * (t : Complex)) -
        logDeriv (chi ^ 2).LFunction
          ((sigma : Complex) + 2 * Complex.I * (t : Complex))).re =
      3 * (-logDeriv (1 : DirichletCharacter Complex q).LFunction
          (sigma : Complex)).re +
        4 * (-logDeriv chi.LFunction
          ((sigma : Complex) + Complex.I * (t : Complex))).re +
        (-logDeriv (chi ^ 2).LFunction
          ((sigma : Complex) + Complex.I * ((2 * t : Real) : Complex))).re by
      simp [Complex.mul_re]
      ring_nf] at hCombination
  exact hCombination

/-- Montgomery--Vaughan, Chapter 11, Theorem 11.3, Case 1: every zero of a
decimal-smooth nonquadratic character in the candidate strip stays an
absolute logarithmic distance to the left of one. -/
theorem exists_decimalSmooth_nonquadratic_LFunction_zero_distance :
    ∃ K : Real, 1 ≤ K ∧
      ∀ {q : Nat} [NeZero q]
        (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q →
        chi ^ 2 ≠ 1 →
        ∀ beta gamma : Real,
          12 / 13 ≤ beta →
          chi.LFunction
            ((beta : Complex) + Complex.I * (gamma : Complex)) = 0 →
          1 / (K * Real.log
            ((q : Real) * (|gamma| + 4))) ≤ 1 - beta := by
  obtain ⟨A, hAPos, hPrincipal⟩ :=
    exists_decimalSmooth_principal_neg_re_logDeriv_le
  obtain ⟨C, hCPos, hUnselected, hSelected⟩ :=
    exists_nonprincipal_neg_re_logDeriv_local_bounds
  let E : Real := 3 * A + 6 * C + 1
  let K : Real := 14 * E
  have hEOne : 1 ≤ E := by
    dsimp [E]
    nlinarith
  have hKOne : 1 ≤ K := by
    dsimp [K]
    nlinarith
  refine ⟨K, hKOne, ?_⟩
  intro q _ chi hq hChiSquare beta gamma hBeta hZero
  have hchi : chi ≠ 1 := by
    intro hchi
    apply hChiSquare
    rw [hchi, one_pow]
  have hBetaOne : beta < 1 := by
    by_contra hBetaOne
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (.inl hchi)
      (s := (beta : Complex) + Complex.I * (gamma : Complex))
      (by simpa using not_lt.mp hBetaOne) hZero
  let a : Real := 1 - beta
  let delta : Real := 6 * a
  let sigma : Real := 1 + delta
  let L : Real := Real.log ((q : Real) * (|gamma| + 4))
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hDeltaPos : 0 < delta := by
    dsimp [delta]
    positivity
  have hDeltaLe : delta ≤ 1 := by
    dsimp [delta, a]
    linarith
  have hSigmaOne : 1 < sigma := by
    dsimp [sigma]
    linarith
  have hSigmaTwo : sigma ≤ 2 := by
    dsimp [sigma]
    linarith
  have hBetaFiveSixths : 5 / 6 ≤ beta := by linarith
  have hLOne : 1 < L := by
    simpa [L] using one_lt_log_level_mul_abs_add_four (q := q) gamma
  have hLPos : 0 < L := zero_lt_one.trans hLOne
  have hLogFour :
      Real.log ((q : Real) * 4) ≤ L := by
    simpa [L] using
      log_level_mul_four_le_log_level_mul_abs_add_four (q := q) gamma
  have hPrincipalRaw := hPrincipal (q := q) hq delta 0 hDeltaPos hDeltaLe
  have hPoleZero : delta / (delta ^ 2 + (0 : Real) ^ 2) = 1 / delta := by
    norm_num
    field_simp [hDeltaPos.ne']
  have hPrincipalZero :
      (-logDeriv (1 : DirichletCharacter Complex q).LFunction
        (sigma : Complex)).re ≤ 1 / delta + A * L := by
    calc
      (-logDeriv (1 : DirichletCharacter Complex q).LFunction
          (sigma : Complex)).re ≤
          delta / (delta ^ 2 + (0 : Real) ^ 2) +
            A * Real.log ((q : Real) * 4) := by
        simpa [sigma] using hPrincipalRaw
      _ = 1 / delta + A * Real.log ((q : Real) * 4) := by
        rw [hPoleZero]
      _ ≤ 1 / delta + A * L := by
        exact add_le_add (le_refl _) <|
          mul_le_mul_of_nonneg_left hLogFour hAPos.le
  have hSelectedRaw := hSelected chi hchi gamma beta sigma
    hBetaFiveSixths hZero hSigmaOne hSigmaTwo
  have hSelectedAt :
      (-logDeriv chi.LFunction
        ((sigma : Complex) + Complex.I * (gamma : Complex))).re ≤
        -(1 / (delta + a)) + C * L := by
    convert hSelectedRaw using 1; dsimp [sigma, a, L]; ring
  have hDoubleRaw := hUnselected (chi ^ 2) hChiSquare
    (2 * gamma) sigma hSigmaOne hSigmaTwo
  have hDoubleLog :=
    log_level_mul_double_abs_add_four_le (q := q) gamma
  have hDoubleAt :
      (-logDeriv (chi ^ 2).LFunction
        ((sigma : Complex) +
          Complex.I * ((2 * gamma : Real) : Complex))).re ≤
        2 * C * L := by
    calc
      _ ≤ C * Real.log ((q : Real) * (|2 * gamma| + 4)) := hDoubleRaw
      _ ≤ C * (2 * L) :=
        mul_le_mul_of_nonneg_left (by simpa [L] using hDoubleLog) hCPos.le
      _ = 2 * C * L := by ring
  have hCombination :=
    neg_logDeriv_combination_re_nonneg chi hSigmaOne gamma
  have hRaw :
      0 ≤ 3 * (1 / delta + A * L) +
        4 * (-(1 / (delta + a)) + C * L) + 2 * C * L := by
    linarith
  have hRawNormalized :
      0 ≤ 3 / delta - 4 / (delta + a) + (3 * A + 6 * C) * L := by
    convert hRaw using 1; ring
  have hErrorScale : (3 * A + 6 * C) * L ≤ E * L := by
    dsimp [E]
    nlinarith
  have hMaster :
      0 ≤ 3 / delta - 4 / (delta + a) + E * L := by
    linarith
  have hRational :
      3 / delta - 4 / (delta + a) = -(1 / (14 * a)) := by
    dsimp [delta]
    field_simp [ha.ne']; ring
  rw [hRational] at hMaster
  have hReciprocal : 1 / (14 * a) ≤ E * L := by
    linarith
  have hFourteenAPos : 0 < 14 * a := by positivity
  have hCross := (div_le_iff₀ hFourteenAPos).mp hReciprocal
  have hKPos : 0 < K := zero_lt_one.trans_le hKOne
  have hDenomPos : 0 < K * L := mul_pos hKPos hLPos
  change 1 / (K * L) ≤ a
  rw [div_le_iff₀ hDenomPos]
  dsimp [K]
  convert hCross using 1; ring

/-- Montgomery--Vaughan, Chapter 11, Theorem 11.3, Case 2: a zero of a
nonprincipal decimal-smooth quadratic character satisfying the inclusive far
condition stays an absolute logarithmic distance to the left of one. -/
theorem exists_decimalSmooth_quadratic_far_LFunction_zero_distance :
    ∃ K : Real, 1 ≤ K ∧
      ∀ {q : Nat} [NeZero q]
        (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q →
        chi ≠ 1 →
        chi.IsQuadratic →
        ∀ beta gamma : Real,
          12 / 13 ≤ beta →
          6 * (1 - beta) ≤ |gamma| →
          chi.LFunction
            ((beta : Complex) + Complex.I * (gamma : Complex)) = 0 →
          1 / (K * Real.log
            ((q : Real) * (|gamma| + 4))) ≤ 1 - beta := by
  obtain ⟨A, hAPos, hPrincipal⟩ :=
    exists_decimalSmooth_principal_neg_re_logDeriv_le
  obtain ⟨C, hCPos, _hUnselected, hSelected⟩ :=
    exists_nonprincipal_neg_re_logDeriv_local_bounds
  let E : Real := 5 * A + 4 * C + 1
  let K : Real := 27 * E
  have hEOne : 1 ≤ E := by
    dsimp [E]
    nlinarith
  have hKOne : 1 ≤ K := by
    dsimp [K]
    nlinarith
  refine ⟨K, hKOne, ?_⟩
  intro q _ chi hq hchi hQuadratic beta gamma hBeta hFar hZero
  have hBetaOne : beta < 1 := by
    by_contra hBetaOne
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (.inl hchi)
      (s := (beta : Complex) + Complex.I * (gamma : Complex))
      (by simpa using not_lt.mp hBetaOne) hZero
  let a : Real := 1 - beta
  let delta : Real := 6 * a
  let sigma : Real := 1 + delta
  let L : Real := Real.log ((q : Real) * (|gamma| + 4))
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hDeltaPos : 0 < delta := by
    dsimp [delta]
    positivity
  have hDeltaLe : delta ≤ 1 := by
    dsimp [delta, a]
    linarith
  have hSigmaOne : 1 < sigma := by
    dsimp [sigma]
    linarith
  have hSigmaTwo : sigma ≤ 2 := by
    dsimp [sigma]
    linarith
  have hBetaFiveSixths : 5 / 6 ≤ beta := by linarith
  have hLOne : 1 < L := by
    simpa [L] using one_lt_log_level_mul_abs_add_four (q := q) gamma
  have hLPos : 0 < L := zero_lt_one.trans hLOne
  have hLogFour :
      Real.log ((q : Real) * 4) ≤ L := by
    simpa [L] using
      log_level_mul_four_le_log_level_mul_abs_add_four (q := q) gamma
  have hPrincipalRaw := hPrincipal (q := q) hq delta 0 hDeltaPos hDeltaLe
  have hPoleZero : delta / (delta ^ 2 + (0 : Real) ^ 2) = 1 / delta := by
    norm_num
    field_simp [hDeltaPos.ne']
  have hPrincipalZero :
      (-logDeriv (1 : DirichletCharacter Complex q).LFunction
        (sigma : Complex)).re ≤ 1 / delta + A * L := by
    calc
      (-logDeriv (1 : DirichletCharacter Complex q).LFunction
          (sigma : Complex)).re ≤
          delta / (delta ^ 2 + (0 : Real) ^ 2) +
            A * Real.log ((q : Real) * 4) := by
        simpa [sigma] using hPrincipalRaw
      _ = 1 / delta + A * Real.log ((q : Real) * 4) := by
        rw [hPoleZero]
      _ ≤ 1 / delta + A * L := by
        exact add_le_add (le_refl _) <|
          mul_le_mul_of_nonneg_left hLogFour hAPos.le
  have hSelectedRaw := hSelected chi hchi gamma beta sigma
    hBetaFiveSixths hZero hSigmaOne hSigmaTwo
  have hSelectedAt :
      (-logDeriv chi.LFunction
        ((sigma : Complex) + Complex.I * (gamma : Complex))).re ≤
        -(1 / (delta + a)) + C * L := by
    convert hSelectedRaw using 1; dsimp [sigma, a, L]; ring
  have hChiSquare : chi ^ 2 = 1 := hQuadratic.sq_eq_one
  have hPrincipalDoubleRaw :=
    hPrincipal (q := q) hq delta (2 * gamma) hDeltaPos hDeltaLe
  have hDoubleLog :=
    log_level_mul_double_abs_add_four_le (q := q) gamma
  have hPrincipalDouble :
      (-logDeriv (chi ^ 2).LFunction
        ((sigma : Complex) +
          Complex.I * ((2 * gamma : Real) : Complex))).re ≤
        delta / (delta ^ 2 + 4 * gamma ^ 2) + 2 * A * L := by
    rw [hChiSquare]
    calc
      _ ≤ delta / (delta ^ 2 + (2 * gamma) ^ 2) +
          A * Real.log ((q : Real) * (|2 * gamma| + 4)) := by
        simpa [sigma] using hPrincipalDoubleRaw
      _ ≤ delta / (delta ^ 2 + (2 * gamma) ^ 2) + A * (2 * L) := by
        exact add_le_add (le_refl _) <|
          mul_le_mul_of_nonneg_left (by simpa [L] using hDoubleLog) hAPos.le
      _ = delta / (delta ^ 2 + 4 * gamma ^ 2) + 2 * A * L := by
        ring
  have hFarA : 6 * a ≤ |gamma| := by
    simpa [a] using hFar
  have hFarSquare : (6 * a) ^ 2 ≤ |gamma| ^ 2 :=
    (sq_le_sq₀ (by positivity) (abs_nonneg gamma)).2 hFarA
  have hGammaSquare : 36 * a ^ 2 ≤ gamma ^ 2 := by
    rw [sq_abs] at hFarSquare
    nlinarith
  have hDenominatorLower :
      180 * a ^ 2 ≤ delta ^ 2 + 4 * gamma ^ 2 := by
    dsimp [delta]
    nlinarith
  have hPoleFar :
      delta / (delta ^ 2 + 4 * gamma ^ 2) ≤ 1 / (30 * a) := by
    calc
      delta / (delta ^ 2 + 4 * gamma ^ 2) ≤
          delta / (180 * a ^ 2) :=
        div_le_div_of_nonneg_left hDeltaPos.le (by positivity)
          hDenominatorLower
      _ = 1 / (30 * a) := by
        dsimp [delta]
        field_simp [ha.ne']; ring
  have hCombination :=
    neg_logDeriv_combination_re_nonneg chi hSigmaOne gamma
  have hRaw :
      0 ≤ 3 * (1 / delta + A * L) +
        4 * (-(1 / (delta + a)) + C * L) +
        (delta / (delta ^ 2 + 4 * gamma ^ 2) + 2 * A * L) := by
    linarith
  have hRawFar :
      0 ≤ 3 * (1 / delta + A * L) +
        4 * (-(1 / (delta + a)) + C * L) +
        (1 / (30 * a) + 2 * A * L) := by
    linarith
  have hRawNormalized :
      0 ≤ 3 / delta - 4 / (delta + a) + 1 / (30 * a) +
        (5 * A + 4 * C) * L := by
    convert hRawFar using 1; ring
  have hErrorScale : (5 * A + 4 * C) * L ≤ E * L := by
    dsimp [E]
    nlinarith
  have hMaster :
      0 ≤ 3 / delta - 4 / (delta + a) + 1 / (30 * a) + E * L := by
    linarith
  have hRational :
      3 / delta - 4 / (delta + a) + 1 / (30 * a) =
        -(4 / (105 * a)) := by
    dsimp [delta]
    field_simp [ha.ne']; ring
  rw [hRational] at hMaster
  have hFourReciprocal : 4 / (105 * a) ≤ E * L := by
    linarith
  have hReciprocalComparison :
      1 / (27 * a) ≤ 4 / (105 * a) := by
    calc
      1 / (27 * a) = (1 / 27) / a := by field_simp
      _ ≤ (4 / 105) / a :=
        div_le_div_of_nonneg_right (by norm_num) ha.le
      _ = 4 / (105 * a) := by field_simp
  have hReciprocal : 1 / (27 * a) ≤ E * L :=
    hReciprocalComparison.trans hFourReciprocal
  have hTwentySevenAPos : 0 < 27 * a := by positivity
  have hCross := (div_le_iff₀ hTwentySevenAPos).mp hReciprocal
  have hKPos : 0 < K := zero_lt_one.trans_le hKOne
  have hDenomPos : 0 < K * L := mul_pos hKPos hLPos
  change 1 / (K * L) ≤ a
  rw [div_le_iff₀ hDenomPos]
  dsimp [K]
  convert hCross using 1; ring

end PrimesRestrictedDigits
