import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletZeroFree
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletLocalZeroSumReal

/-!
# Comparing local Dirichlet zero sums inside the zero-free strip

This is the own-height denominator comparison used in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.4. Each supported zero is
controlled by the decimal-smooth zero-free region at its own imaginary part;
the closed radius-`5 / 6` support then compares that scale with the evaluation
height.
-/

open Complex Metric Set

namespace PrimesRestrictedDigits

private lemma one_lt_log_level_mul_abs_add_four_comparison
    {q : Nat} [NeZero q] (t : Real) :
    1 < Real.log ((q : Real) * (|t| + 4)) := by
  have hq : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hFour : (4 : Real) <= |t| + 4 := by
    linarith [abs_nonneg t]
  have hArgument : (4 : Real) <= (q : Real) * (|t| + 4) := by
    calc
      (4 : Real) = 1 * 4 := by ring
      _ <= (q : Real) * (|t| + 4) :=
        mul_le_mul hq hFour (by norm_num) (Nat.cast_nonneg q)
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  exact Real.exp_one_lt_three.trans (by linarith)

/-- A point in the closed local divisor support differs from the center height
by at most the full closed radius. -/
theorem dirichletLFunctionLocalDivisor_support_im_sub_le
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    {t : Real} {rho : Complex}
    (hRho : rho ∈ (dirichletLFunctionLocalDivisor chi t).support) :
    |rho.im - t| <= 5 / 6 := by
  have hBall := (dirichletLFunctionLocalDivisor chi t).supportWithinDomain hRho
  have hIm := Complex.abs_im_le_norm
    (rho - (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex)))
  have hImEq :
      (rho - (((3 / 2 : Real) : Complex) +
        Complex.I * (t : Complex))).im = rho.im - t := by
    simp
  rw [hImEq] at hIm
  exact hIm.trans (by simpa [mem_closedBall, dist_eq_norm] using hBall)

private lemma localDirichletZeroReciprocal_sub_norm_le
    {c : Real} {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} {t sigma : Real} {rho : Complex}
    (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c)
    (hq : IsDecimalSmooth q) (hchi : chi ≠ 1)
    (hSigmaLower :
      1 - c / (2 * Real.log ((q : Real) * (|t| + 4))) <= sigma)
    (hSigmaUpper :
      sigma <= 1 + 1 / Real.log ((q : Real) * (|t| + 4)))
    (hRho : rho ∈ (dirichletLFunctionLocalDivisor chi t).support) :
    norm
        (1 / (((sigma : Complex) + Complex.I * (t : Complex)) - rho) -
          1 / ((((1 + 1 / Real.log
              ((q : Real) * (|t| + 4)) : Real) : Complex) +
            Complex.I * (t : Complex)) - rho)) <=
      (2 / (c / (4 * c + 6))) *
        (1 / ((((1 + 1 / Real.log
            ((q : Real) * (|t| + 4)) : Real) : Complex) +
          Complex.I * (t : Complex)) - rho)).re := by
  let L : Real := Real.log ((q : Real) * (|t| + 4))
  let Lrho : Real := Real.log ((q : Real) * (|rho.im| + 4))
  let d : Real := 1 - rho.re
  let x : Real := sigma - rho.re
  let x1 : Real := 1 + 1 / L - rho.re
  let kappa : Real := c / (4 * c + 6)
  let s : Complex := (sigma : Complex) + Complex.I * t
  let s1 : Complex := ((1 + 1 / L : Real) : Complex) + Complex.I * t
  have hcPos : 0 < c := hc.1
  have hcUpper : c <= 1 / 13 := hc.2.1
  have hLOne : 1 < L := by
    simpa [L] using
      one_lt_log_level_mul_abs_add_four_comparison (q := q) t
  have hLPos : 0 < L := zero_lt_one.trans hLOne
  have hLrhoOne : 1 < Lrho := by
    simpa [Lrho] using
      one_lt_log_level_mul_abs_add_four_comparison (q := q) rho.im
  have hLrhoPos : 0 < Lrho := zero_lt_one.trans hLrhoOne
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hHeight : |rho.im - t| <= 5 / 6 :=
    dirichletLFunctionLocalDivisor_support_im_sub_le hRho
  have hAbsRho : |rho.im| <= |t| + 5 / 6 := by
    calc
      |rho.im| = |(rho.im - t) + t| := by ring_nf
      _ <= |rho.im - t| + |t| := abs_add_le _ _
      _ <= |t| + 5 / 6 := by linarith
  have hHeightArgument : |rho.im| + 4 <= 2 * (|t| + 4) := by
    linarith [abs_nonneg t]
  have hArgUpper :
      (q : Real) * (|rho.im| + 4) <=
        2 * ((q : Real) * (|t| + 4)) := by
    calc
      (q : Real) * (|rho.im| + 4) <=
          (q : Real) * (2 * (|t| + 4)) :=
        mul_le_mul_of_nonneg_left hHeightArgument hqPos.le
      _ = 2 * ((q : Real) * (|t| + 4)) := by ring
  have hLogArgUpper :
      Lrho <= Real.log (2 * ((q : Real) * (|t| + 4))) := by
    dsimp [Lrho]
    exact Real.log_le_log (mul_pos hqPos (by positivity)) hArgUpper
  have hLogMul :
      Real.log (2 * ((q : Real) * (|t| + 4))) = Real.log 2 + L := by
    rw [Real.log_mul (by norm_num)
      (mul_pos hqPos (by linarith [abs_nonneg t])).ne']
  have hArgumentFour : (4 : Real) <= (q : Real) * (|t| + 4) := by
    have hqOne : (1 : Real) <= q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hFour : (4 : Real) <= |t| + 4 := by
      linarith [abs_nonneg t]
    calc
      (4 : Real) = 1 * 4 := by ring
      _ <= (q : Real) * (|t| + 4) :=
        mul_le_mul hqOne hFour (by norm_num) (Nat.cast_nonneg q)
  have hTwiceLogTwo : 2 * Real.log 2 <= L := by
    have hLogFour : Real.log 4 <= L := by
      dsimp [L]
      exact Real.log_le_log (by norm_num) hArgumentFour
    have hEq : Real.log (4 : Real) = 2 * Real.log 2 := by
      rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hLrhoUpper : Lrho <= 3 * L / 2 := by
    rw [hLogMul] at hLogArgUpper
    linarith
  have hRhoZero : chi.LFunction rho = 0 :=
    dirichletLFunctionLocalDivisor_support_zero hchi hRho
  have hRhoCoordinates :
      ((rho.re : Real) : Complex) + Complex.I * (rho.im : Complex) = rho := by
    apply Complex.ext <;> simp
  have hOwnHeight : 1 - c / Lrho > rho.re := by
    by_contra hNot
    have hRegion : 1 - c / Lrho <= rho.re := not_lt.mp hNot
    have hNonzero := hc.2.2 chi hq hchi rho.im rho.re
      (by simpa [Lrho] using hRegion)
    rw [hRhoCoordinates] at hNonzero
    exact hNonzero hRhoZero
  have hDistanceOwn : c / Lrho < d := by
    dsimp [d]
    linarith
  have hdPos : 0 < d := (div_pos hcPos hLrhoPos).trans hDistanceOwn
  have hDistanceScaled : 2 * c / (3 * L) < d := by
    have hOwnMul : c < d * Lrho :=
      (div_lt_iff₀ hLrhoPos).mp hDistanceOwn
    have hMulUpper : d * Lrho <= d * (3 * L / 2) :=
      mul_le_mul_of_nonneg_left hLrhoUpper hdPos.le
    apply (div_lt_iff₀ (by positivity : 0 < 3 * L)).2
    nlinarith
  have hTwoCMul : 2 * c < 3 * L * d := by
    have := (div_lt_iff₀ (by positivity : 0 < 3 * L)).mp hDistanceScaled
    nlinarith
  have hCOver : c / (2 * L) < 3 * d / 4 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * L)).2
    nlinarith
  have hxQuarter : d / 4 < x := by
    dsimp [x, d] at *
    linarith
  have hInvL : 1 / L < 3 * d / (2 * c) := by
    apply (div_lt_div_iff₀ hLPos (by positivity : 0 < 2 * c)).2
    nlinarith
  have hx1Identity : x1 = d + 1 / L := by
    simp [x1, d]
    ring_nf
  have hx1Pos : 0 < x1 := by
    rw [hx1Identity]
    positivity
  have hx1Upper : x1 < (1 + 3 / (2 * c)) * d := by
    calc
      x1 = d + 1 / L := hx1Identity
      _ < d + 3 * d / (2 * c) := by linarith
      _ = (1 + 3 / (2 * c)) * d := by ring_nf
  have hkappaPos : 0 < kappa := by
    dsimp [kappa]
    positivity
  have hkappaLtOne : kappa < 1 := by
    dsimp [kappa]
    apply (div_lt_one (by positivity : 0 < 4 * c + 6)).2
    nlinarith
  have hkappaFactor : kappa * (1 + 3 / (2 * c)) = 1 / 4 := by
    dsimp [kappa]
    field_simp [hcPos.ne']
    ring_nf
  have hxCompare : kappa * x1 < x := by
    calc
      kappa * x1 < kappa * ((1 + 3 / (2 * c)) * d) :=
        mul_lt_mul_of_pos_left hx1Upper hkappaPos
      _ = (kappa * (1 + 3 / (2 * c))) * d := by ring_nf
      _ = (1 / 4) * d := by rw [hkappaFactor]
      _ = d / 4 := by ring_nf
      _ < x := hxQuarter
  have hsRe : (s - rho).re = x := by simp [s, x]
  have hsIm : (s - rho).im = t - rho.im := by simp [s]
  have hs1Re : (s1 - rho).re = x1 := by simp [s1, x1]
  have hs1Im : (s1 - rho).im = t - rho.im := by simp [s1]
  have hsNormSq : norm (s - rho) ^ 2 = x ^ 2 + (t - rho.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hsRe, hsIm]
    ring_nf
  have hs1NormSq : norm (s1 - rho) ^ 2 = x1 ^ 2 + (t - rho.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hs1Re, hs1Im]
    ring_nf
  have hxPos : 0 < x := (div_pos hdPos (by norm_num)).trans hxQuarter
  have hNormCompare : kappa * norm (s1 - rho) <= norm (s - rho) := by
    rw [<- sq_le_sq₀ (by positivity) (norm_nonneg _), mul_pow,
      hsNormSq, hs1NormSq]
    have hkappaSq : kappa ^ 2 <= 1 :=
      (sq_le_sq₀ hkappaPos.le zero_le_one).2 hkappaLtOne.le |>.trans_eq
        (one_pow 2)
    have hxSq : (kappa * x1) ^ 2 <= x ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hkappaPos.le hx1Pos.le) hxPos.le).2 hxCompare.le
    have hySq :
        kappa ^ 2 * (t - rho.im) ^ 2 <= (t - rho.im) ^ 2 := by
      exact mul_le_of_le_one_left (sq_nonneg _) hkappaSq
    calc
      kappa ^ 2 * (x1 ^ 2 + (t - rho.im) ^ 2) =
          (kappa * x1) ^ 2 + kappa ^ 2 * (t - rho.im) ^ 2 := by ring_nf
      _ <= x ^ 2 + (t - rho.im) ^ 2 := add_le_add hxSq hySq
  have hsNe : s - rho ≠ 0 := by
    intro hZero
    have : (s - rho).re = 0 := congrArg Complex.re hZero
    rw [hsRe] at this
    linarith [hxCompare, hx1Pos, hkappaPos]
  have hs1Ne : s1 - rho ≠ 0 := by
    intro hZero
    have : (s1 - rho).re = 0 := congrArg Complex.re hZero
    rw [hs1Re] at this
    linarith
  have hSigmaGap : 0 <= 1 + 1 / L - sigma := by
    simpa [L] using sub_nonneg.mpr hSigmaUpper
  have hcTwo : c <= 2 := hcUpper.trans (by norm_num)
  have hCOverLe : c / (2 * L) <= 1 / L := by
    calc
      c / (2 * L) <= 2 / (2 * L) :=
        div_le_div_of_nonneg_right hcTwo (by positivity)
      _ = 1 / L := by field_simp [hLPos.ne']
  have hSigmaGapUpper : 1 + 1 / L - sigma <= 2 / L := by
    have hLower : 1 - c / (2 * L) <= sigma := by
      simpa [L] using hSigmaLower
    calc
      1 + 1 / L - sigma <= 1 / L + c / (2 * L) := by linarith
      _ <= 1 / L + 1 / L := by linarith
      _ = 2 / L := by ring_nf
  have hsSubNorm : norm (s1 - s) <= 2 / L := by
    have hDiff : s1 - s = ((1 + 1 / L - sigma : Real) : Complex) := by
      apply Complex.ext <;> simp [s1, s]
    rw [hDiff, norm_real, Real.norm_eq_abs, abs_of_nonneg hSigmaGap]
    exact hSigmaGapUpper
  have hInvDifference :
      1 / (s - rho) - 1 / (s1 - rho) =
        (s1 - s) / ((s - rho) * (s1 - rho)) := by
    rw [one_div, one_div]
    simpa only [sub_sub_sub_cancel_right] using inv_sub_inv hsNe hs1Ne
  have hsNormPos : 0 < norm (s - rho) := norm_pos_iff.mpr hsNe
  have hs1NormPos : 0 < norm (s1 - rho) := norm_pos_iff.mpr hs1Ne
  have hInvLLeX1 : 1 / L <= x1 := by
    rw [hx1Identity]
    linarith
  have hProduct :
      (1 / L) * (kappa * norm (s1 - rho)) <=
        x1 * norm (s - rho) :=
    mul_le_mul hInvLLeX1 hNormCompare (by positivity) (by positivity)
  have hCore :
      norm (1 / (s - rho) - 1 / (s1 - rho)) <=
        (2 / kappa) * (1 / (s1 - rho)).re := by
    rw [hInvDifference, Complex.norm_div, Complex.norm_mul]
    rw [one_div, Complex.inv_re, hs1Re, <- Complex.sq_norm]
    apply (div_le_iff₀ (mul_pos hsNormPos hs1NormPos)).2
    have hRightIdentity :
        (2 / kappa) * (x1 / norm (s1 - rho) ^ 2) *
            (norm (s - rho) * norm (s1 - rho)) =
          (2 * x1 * norm (s - rho)) /
            (kappa * norm (s1 - rho)) := by
      field_simp [hkappaPos.ne', hs1NormPos.ne']
    rw [hRightIdentity]
    apply hsSubNorm.trans
    apply (le_div_iff₀ (mul_pos hkappaPos hs1NormPos)).2
    calc
      2 / L * (kappa * norm (s1 - rho)) =
          2 * ((1 / L) * (kappa * norm (s1 - rho))) := by ring_nf
      _ <= 2 * (x1 * norm (s - rho)) :=
        mul_le_mul_of_nonneg_left hProduct (by norm_num)
      _ = 2 * x1 * norm (s - rho) := by ring_nf
  simpa [L, s, s1, kappa] using hCore

private lemma localDirichletZeroTerm_sub_norm_le
    {c : Real} {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} {t sigma : Real} {rho : Complex}
    (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c)
    (hq : IsDecimalSmooth q) (hchi : chi ≠ 1)
    (hSigmaLower :
      1 - c / (2 * Real.log ((q : Real) * (|t| + 4))) <= sigma)
    (hSigmaUpper :
      sigma <= 1 + 1 / Real.log ((q : Real) * (|t| + 4))) :
    norm
        (((dirichletLFunctionLocalDivisor chi t rho : Int) : Complex) /
            (((sigma : Complex) + Complex.I * (t : Complex)) - rho) -
          ((dirichletLFunctionLocalDivisor chi t rho : Int) : Complex) /
            ((((1 + 1 / Real.log
                ((q : Real) * (|t| + 4)) : Real) : Complex) +
              Complex.I * (t : Complex)) - rho)) <=
      (2 / (c / (4 * c + 6))) *
        (((dirichletLFunctionLocalDivisor chi t rho : Int) : Complex) /
          ((((1 + 1 / Real.log
              ((q : Real) * (|t| + 4)) : Real) : Complex) +
            Complex.I * (t : Complex)) - rho)).re := by
  by_cases hRho : rho ∈ (dirichletLFunctionLocalDivisor chi t).support
  · have hCoeffInt : 0 <= dirichletLFunctionLocalDivisor chi t rho :=
      dirichletLFunctionLocalDivisor_nonneg hchi t rho
    have hCoeffReal :
        (0 : Real) <= (dirichletLFunctionLocalDivisor chi t rho : Int) := by
      exact_mod_cast hCoeffInt
    have hRecip := localDirichletZeroReciprocal_sub_norm_le
      hc hq hchi hSigmaLower hSigmaUpper hRho
    simp only [div_eq_mul_inv]
    rw [<- mul_sub]
    rw [norm_mul, Complex.norm_int_of_nonneg hCoeffInt]
    have hScaled := mul_le_mul_of_nonneg_left hRecip hCoeffReal
    calc
      (dirichletLFunctionLocalDivisor chi t rho : Int) *
          norm
            ((↑sigma + Complex.I * ↑t - rho)⁻¹ -
              (↑(1 + 1 / Real.log ((q : Real) * (|t| + 4))) +
                Complex.I * ↑t - rho)⁻¹) <=
          (dirichletLFunctionLocalDivisor chi t rho : Int) *
            ((2 / (c / (4 * c + 6))) *
              (1 / (↑(1 + 1 / Real.log ((q : Real) * (|t| + 4))) +
                Complex.I * ↑t - rho)).re) := by
        simpa only [one_div] using hScaled
      _ = (2 / (c / (4 * c + 6))) *
          (((dirichletLFunctionLocalDivisor chi t rho : Int) : Complex) *
            (↑(1 + 1 / Real.log ((q : Real) * (|t| + 4))) +
              Complex.I * ↑t - rho)⁻¹).re := by
        simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
          zero_mul, sub_zero]
        ring_nf
  · have hCoeff : dirichletLFunctionLocalDivisor chi t rho = 0 := by
      simpa [Function.mem_support] using hRho
    simp [hCoeff]

/-- In the closed half-width zero-free strip, the local zero sum differs from
its right-hand anchor by at most a constant (depending only on the fixed
zero-free constant) times the anchor sum's real part. -/
theorem exists_decimalSmooth_dirichletLFunctionLocalZeroSum_sub_bound
    {c : Real} (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c) :
    exists A : Real, 0 < A ∧
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q -> chi ≠ 1 ->
          forall t sigma : Real,
            1 - c / (2 * Real.log ((q : Real) * (|t| + 4))) <= sigma ->
            sigma <= 1 + 1 / Real.log ((q : Real) * (|t| + 4)) ->
            norm
                (dirichletLFunctionLocalZeroSum chi t
                    ((sigma : Complex) + Complex.I * (t : Complex)) -
                  dirichletLFunctionLocalZeroSum chi t
                    (((1 + 1 / Real.log
                      ((q : Real) * (|t| + 4)) : Real) : Complex) +
                      Complex.I * (t : Complex))) <=
              A *
                (dirichletLFunctionLocalZeroSum chi t
                  (((1 + 1 / Real.log
                    ((q : Real) * (|t| + 4)) : Real) : Complex) +
                    Complex.I * (t : Complex))).re := by
  let kappa : Real := c / (4 * c + 6)
  have hcPos : 0 < c := hc.1
  have hkappaPos : 0 < kappa := by
    dsimp [kappa]
    positivity
  refine ⟨2 / kappa, by positivity, ?_⟩
  intro q _ chi hq hchi t sigma hSigmaLower hSigmaUpper
  let D := dirichletLFunctionLocalDivisor chi t
  let evalTerm : Complex -> Complex := fun rho =>
    ((D rho : Int) : Complex) /
      (((sigma : Complex) + Complex.I * (t : Complex)) - rho)
  let differenceTerm : Complex -> Complex := fun rho =>
    ((D rho : Int) : Complex) /
        (((sigma : Complex) + Complex.I * (t : Complex)) - rho) -
      ((D rho : Int) : Complex) /
        ((((1 + 1 / Real.log
            ((q : Real) * (|t| + 4)) : Real) : Complex) +
          Complex.I * (t : Complex)) - rho)
  let anchorTerm : Complex -> Complex := fun rho =>
    ((D rho : Int) : Complex) /
      ((((1 + 1 / Real.log
          ((q : Real) * (|t| + 4)) : Real) : Complex) +
        Complex.I * (t : Complex)) - rho)
  have hD : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
      (5 / 6 : Real))
  have hEvalSupp : evalTerm.support ⊆ D.support := by
    intro rho hRho
    contrapose! hRho
    have : D rho = 0 := by simpa [Function.mem_support] using hRho
    simp [evalTerm, this]
  have hAnchorSupp : anchorTerm.support ⊆ D.support := by
    intro rho hRho
    contrapose! hRho
    have : D rho = 0 := by simpa [Function.mem_support] using hRho
    simp [anchorTerm, this]
  have hEval : (∑ᶠ rho : Complex, evalTerm rho) =
      ∑ rho ∈ hD.toFinset, evalTerm rho :=
    finsum_eq_sum_of_support_subset _
      (hEvalSupp.trans (fun rho hRho => hD.mem_toFinset.mpr hRho))
  have hAnchor : (∑ᶠ rho : Complex, anchorTerm rho) =
      ∑ rho ∈ hD.toFinset, anchorTerm rho :=
    finsum_eq_sum_of_support_subset _
      (hAnchorSupp.trans (fun rho hRho => hD.mem_toFinset.mpr hRho))
  rw [dirichletLFunctionLocalZeroSum, dirichletLFunctionLocalZeroSum]
  change norm
      ((∑ᶠ rho : Complex, evalTerm rho) -
        ∑ᶠ rho : Complex, anchorTerm rho) <=
    (2 / kappa) * (∑ᶠ rho : Complex, anchorTerm rho).re
  rw [hEval, hAnchor, <- Finset.sum_sub_distrib]
  change norm (∑ rho ∈ hD.toFinset, differenceTerm rho) <=
    (2 / kappa) * (∑ rho ∈ hD.toFinset, anchorTerm rho).re
  calc
    norm (∑ rho ∈ hD.toFinset, differenceTerm rho) <=
        ∑ rho ∈ hD.toFinset, norm (differenceTerm rho) := norm_sum_le _ _
    _ <= ∑ rho ∈ hD.toFinset,
        (2 / kappa) * (anchorTerm rho).re := by
      gcongr with rho hRho
      simpa [D, differenceTerm, anchorTerm, kappa] using
        localDirichletZeroTerm_sub_norm_le hc hq hchi hSigmaLower
          hSigmaUpper (rho := rho)
    _ = (2 / kappa) *
        (∑ rho ∈ hD.toFinset, anchorTerm rho).re := by
      change (∑ rho ∈ hD.toFinset, (2 / kappa) * (anchorTerm rho).re) =
        (2 / kappa) *
          Complex.reCLM (∑ rho ∈ hD.toFinset, anchorTerm rho)
      simp only [map_sum]
      exact (Finset.mul_sum _ _ _).symm

end PrimesRestrictedDigits
