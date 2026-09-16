import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletFiniteZeroGap
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletZeroSeparation

/-!
# A zero-free region for decimal-smooth nonprincipal Dirichlet L-functions

This specializes `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.3 to
decimal-smooth levels. The finite quadratic-conductor gap removes the source's
possible exceptional real zero, at the cost of a potentially non-effective
absolute constant.
-/

open Complex

namespace PrimesRestrictedDigits

/-- A normalized zero-free-region constant for every nonprincipal Dirichlet
L-function at every positive decimal-smooth level. -/
def IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant
    (c : Real) : Prop :=
  0 < c ∧ c ≤ 1 / 13 ∧
    ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
      IsDecimalSmooth q → chi ≠ 1 →
        ∀ t sigma : Real,
          1 - c / Real.log ((q : Real) * (|t| + 4)) ≤ sigma →
            chi.LFunction
              ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 0

private lemma one_lt_log_level_mul_abs_add_four_zero_free
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

/-- Shrinking a positive decimal-smooth Dirichlet zero-free constant
preserves the normalized predicate. -/
theorem IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant.mono
    {c d : Real} (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c)
    (hdPos : 0 < d) (hdc : d ≤ c) :
    IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant d := by
  refine ⟨hdPos, hdc.trans hc.2.1, ?_⟩
  intro q _ chi hq hchi t sigma hRegion
  apply hc.2.2 chi hq hchi t sigma
  have hLogPos : 0 < Real.log ((q : Real) * (|t| + 4)) :=
    zero_lt_one.trans
      (one_lt_log_level_mul_abs_add_four_zero_free (q := q) t)
  have hDiv : d / Real.log ((q : Real) * (|t| + 4)) ≤
      c / Real.log ((q : Real) * (|t| + 4)) :=
    div_le_div_of_nonneg_right hdc hLogPos.le
  linarith

private lemma dist_sigma_add_mul_I_one_le
    (sigma t : Real) :
    dist ((sigma : Complex) + Complex.I * (t : Complex)) 1 ≤
      |sigma - 1| + |t| := by
  rw [dist_eq_norm]
  have hDifference :
      ((sigma : Complex) + Complex.I * (t : Complex)) - 1 =
        ((sigma - 1 : Real) : Complex) + Complex.I * (t : Complex) := by
    apply Complex.ext <;> simp
  rw [hDifference]
  calc
    norm (((sigma - 1 : Real) : Complex) + Complex.I * (t : Complex)) ≤
        norm ((sigma - 1 : Real) : Complex) +
          norm (Complex.I * (t : Complex)) := norm_add_le _ _
    _ = |sigma - 1| + |t| := by
      rw [norm_real, Real.norm_eq_abs, norm_mul, norm_I, norm_real,
        Real.norm_eq_abs, one_mul]

private lemma false_of_separation_and_half_constant
    {K L c a : Real} (hK : 0 < K) (hL : 0 < L)
    (hc : c ≤ 1 / (2 * K)) (ha : a ≤ c / L)
    (hDistance : 1 / (K * L) ≤ a) : False := by
  have hcDiv : c / L ≤ 1 / (2 * K * L) := by
    calc
      c / L ≤ (1 / (2 * K)) / L :=
        div_le_div_of_nonneg_right hc hL.le
      _ = 1 / (2 * K * L) := by field_simp
  have hDenomPos : 0 < K * L := mul_pos hK hL
  have hDenomLt : K * L < 2 * K * L := by nlinarith
  have hReciprocal : 1 / (2 * K * L) < 1 / (K * L) :=
    one_div_lt_one_div_of_lt hDenomPos hDenomLt
  linarith

/-- There is one possibly non-effective absolute logarithmic zero-free-region
constant for all nonprincipal characters at all decimal-smooth levels. -/
theorem exists_isDecimalSmoothNonprincipalLFunctionZeroFreeConstant :
    ∃ c : Real, IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c := by
  obtain ⟨K1, hK1One, hNonquadratic⟩ :=
    exists_decimalSmooth_nonquadratic_LFunction_zero_distance
  obtain ⟨K2, hK2One, hQuadraticFar⟩ :=
    exists_decimalSmooth_quadratic_far_LFunction_zero_distance
  obtain ⟨radius, hRadiusPos, _hRadiusLe, hQuadraticGap⟩ :=
    exists_decimalSmooth_quadratic_LFunction_zero_gap
  have hK1Pos : 0 < K1 := zero_lt_one.trans_le hK1One
  have hK2Pos : 0 < K2 := zero_lt_one.trans_le hK2One
  let c : Real := min (1 / 26)
    (min (1 / (2 * K1)) (min (1 / (2 * K2)) (radius / 14)))
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) <| lt_min (by positivity) <|
      lt_min (by positivity) (by positivity)
  have hcThirteen : c ≤ 1 / 13 := by
    exact (min_le_left _ _).trans (by norm_num)
  have hcK1 : c ≤ 1 / (2 * K1) := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcK2 : c ≤ 1 / (2 * K2) := by
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hcRadius : c ≤ radius / 14 := by
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hcPos, hcThirteen, ?_⟩
  intro q _ chi hq hchi t sigma hRegion
  have hLOne : 1 < Real.log ((q : Real) * (|t| + 4)) :=
    one_lt_log_level_mul_abs_add_four_zero_free (q := q) t
  have hLPos : 0 < Real.log ((q : Real) * (|t| + 4)) :=
    zero_lt_one.trans hLOne
  by_cases hSigma : 1 ≤ sigma
  · apply DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (.inl hchi)
    simpa using hSigma
  have hSigmaLt : sigma < 1 := lt_of_not_ge hSigma
  have hRegionUpper :
      1 - sigma ≤ c / Real.log ((q : Real) * (|t| + 4)) := by
    linarith
  have hcDivLt :
      c / Real.log ((q : Real) * (|t| + 4)) < c :=
    div_lt_self hcPos hLOne
  have hSigmaTwelveThirteenths : 12 / 13 ≤ sigma := by
    have hcDivThirteen :
        c / Real.log ((q : Real) * (|t| + 4)) ≤ 1 / 13 :=
      (le_of_lt hcDivLt).trans hcThirteen
    linarith
  intro hZero
  by_cases hQuadratic : chi.IsQuadratic
  · by_cases hFar : 6 * (1 - sigma) ≤ |t|
    · have hDistance := hQuadraticFar chi hq hchi hQuadratic sigma t
        hSigmaTwelveThirteenths hFar hZero
      exact false_of_separation_and_half_constant
        hK2Pos hLPos hcK2 hRegionUpper hDistance
    · have hNear : |t| < 6 * (1 - sigma) := lt_of_not_ge hFar
      have hsOne :
          ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 1 := by
        intro hs
        have hRe := congrArg Complex.re hs
        simp at hRe
        linarith
      have hDistanceUpper := dist_sigma_add_mul_I_one_le sigma t
      have hAbs : |sigma - 1| = 1 - sigma := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [hAbs] at hDistanceUpper
      have hdist :
          dist ((sigma : Complex) + Complex.I * (t : Complex)) 1 ≤
            radius := by
        nlinarith
      exact (hQuadraticGap chi hq hQuadratic hsOne hdist) hZero
  · have hChiSquare : chi ^ 2 ≠ 1 := by
      intro hChiSquare
      exact hQuadratic (MulChar.isQuadratic_iff_sq_eq_one.mpr hChiSquare)
    have hDistance := hNonquadratic chi hq hChiSquare sigma t
      hSigmaTwelveThirteenths hZero
    exact false_of_separation_and_half_constant
      hK1Pos hLPos hcK1 hRegionUpper hDistance

end PrimesRestrictedDigits
