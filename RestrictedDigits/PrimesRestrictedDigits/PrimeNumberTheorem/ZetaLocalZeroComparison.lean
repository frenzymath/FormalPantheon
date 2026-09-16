import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFree
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLocalZeroSumReal

/-!
# Comparing local zeta-zero sums inside the zero-free strip

This is the own-height denominator comparison used in the proof of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Theorem 6.7.  Each zero is first
controlled at its own imaginary part; the closed radius-`5 / 6` support then
compares its logarithmic height with the evaluation height.
-/

open Complex Metric Set

namespace PrimesRestrictedDigits

private lemma one_lt_log_abs_add_four_comparison (t : Real) :
    1 < Real.log (|t| + 4) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])

/-- A zero in the closed local divisor disk differs from its center height by
at most the full closed radius. -/
theorem riemannZetaLocalDivisor_support_im_sub_le
    {t : Real} {rho : Complex}
    (hRho : rho ∈ (riemannZetaLocalDivisor t).support) :
    |rho.im - t| <= 5 / 6 := by
  have hBall := (riemannZetaLocalDivisor t).supportWithinDomain hRho
  have hIm := Complex.abs_im_le_norm
    (rho - (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex)))
  have hImEq :
      (rho - (((3 / 2 : Real) : Complex) +
        Complex.I * (t : Complex))).im = rho.im - t := by
    simp
  rw [hImEq] at hIm
  exact hIm.trans (by simpa [mem_closedBall, dist_eq_norm] using hBall)

private lemma localZeroReciprocal_sub_norm_le
    {c t sigma : Real} {rho : Complex}
    (hc : IsRiemannZetaZeroFreeConstant c)
    (hT : 7 / 8 <= |t|)
    (hSigmaLower :
      1 - c / (2 * Real.log (|t| + 4)) < sigma)
    (hSigmaUpper :
      sigma <= 1 + 1 / Real.log (|t| + 4))
    (hRho : rho ∈ (riemannZetaLocalDivisor t).support) :
    norm
        (1 / (((sigma : Complex) + Complex.I * (t : Complex)) - rho) -
          1 / ((((1 + 1 / Real.log (|t| + 4) : Real) : Complex) +
            Complex.I * (t : Complex)) - rho)) <=
      (2 / (c / (4 * c + 6))) *
        (1 / ((((1 + 1 / Real.log (|t| + 4) : Real) : Complex) +
          Complex.I * (t : Complex)) - rho)).re := by
  let L : Real := Real.log (|t| + 4)
  let Lrho : Real := Real.log (|rho.im| + 4)
  let d : Real := 1 - rho.re
  let x : Real := sigma - rho.re
  let x1 : Real := 1 + 1 / L - rho.re
  let kappa : Real := c / (4 * c + 6)
  let s : Complex := (sigma : Complex) + Complex.I * t
  let s1 : Complex := ((1 + 1 / L : Real) : Complex) + Complex.I * t
  have hcPos : 0 < c := hc.1
  have hcUpper : c <= 1 / 9 := hc.2.1
  have hLOne : 1 < L := by
    simpa [L] using one_lt_log_abs_add_four_comparison t
  have hLPos : 0 < L := zero_lt_one.trans hLOne
  have hLrhoOne : 1 < Lrho := by
    simpa [Lrho] using one_lt_log_abs_add_four_comparison rho.im
  have hLrhoPos : 0 < Lrho := zero_lt_one.trans hLrhoOne
  have hHeight : |rho.im - t| <= 5 / 6 :=
    riemannZetaLocalDivisor_support_im_sub_le hRho
  have hAbsRho : |rho.im| <= |t| + 5 / 6 := by
    calc
      |rho.im| = |(rho.im - t) + t| := by ring_nf
      _ <= |rho.im - t| + |t| := abs_add_le _ _
      _ <= |t| + 5 / 6 := by linarith
  have hTauFour : (4 : Real) <= |t| + 4 := by
    linarith [abs_nonneg t]
  have hArgUpper : |rho.im| + 4 <= 2 * (|t| + 4) := by
    linarith
  have hLogArgUpper :
      Lrho <= Real.log (2 * (|t| + 4)) := by
    dsimp [Lrho]
    exact Real.log_le_log (by positivity) hArgUpper
  have hLogMul :
      Real.log (2 * (|t| + 4)) = Real.log 2 + L := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have hTwiceLogTwo : 2 * Real.log 2 <= L := by
    have hLogFour : Real.log 4 <= L := by
      dsimp [L]
      exact Real.log_le_log (by norm_num) hTauFour
    have hEq : Real.log (4 : Real) = 2 * Real.log 2 := by
      rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hLrhoUpper : Lrho <= 3 * L / 2 := by
    rw [hLogMul] at hLogArgUpper
    linarith
  have hRhoZero : riemannZeta rho = 0 :=
    riemannZetaLocalDivisor_support_mem_riemannZetaZeros hT hRho
  have hRhoCoordinates :
      ((rho.re : Real) : Complex) + Complex.I * (rho.im : Complex) = rho := by
    apply Complex.ext <;> simp
  have hOwnHeight : 1 - c / Lrho > rho.re := by
    by_contra hNot
    have hRegion : 1 - c / Lrho <= rho.re := not_lt.mp hNot
    have hNonzero := hc.2.2 rho.im rho.re (by simpa [Lrho] using hRegion)
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
    have hLower : 1 - c / (2 * L) < sigma := by
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
        (2 / kappa) *
          (1 / (s1 - rho)).re := by
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

private lemma localZeroTerm_sub_norm_le
    {c t sigma : Real} {rho : Complex}
    (hc : IsRiemannZetaZeroFreeConstant c)
    (hT : 7 / 8 <= |t|)
    (hSigmaLower :
      1 - c / (2 * Real.log (|t| + 4)) < sigma)
    (hSigmaUpper :
      sigma <= 1 + 1 / Real.log (|t| + 4)) :
    norm
        (((riemannZetaLocalDivisor t rho : Int) : Complex) /
            (((sigma : Complex) + Complex.I * (t : Complex)) - rho) -
          ((riemannZetaLocalDivisor t rho : Int) : Complex) /
            ((((1 + 1 / Real.log (|t| + 4) : Real) : Complex) +
              Complex.I * (t : Complex)) - rho)) <=
      (2 / (c / (4 * c + 6))) *
        (((riemannZetaLocalDivisor t rho : Int) : Complex) /
          ((((1 + 1 / Real.log (|t| + 4) : Real) : Complex) +
            Complex.I * (t : Complex)) - rho)).re := by
  by_cases hRho : rho ∈ (riemannZetaLocalDivisor t).support
  · have hCoeffInt : 0 <= riemannZetaLocalDivisor t rho :=
      riemannZetaLocalDivisor_nonneg hT rho
    have hCoeffReal :
        (0 : Real) <= (riemannZetaLocalDivisor t rho : Int) := by
      exact_mod_cast hCoeffInt
    have hRecip := localZeroReciprocal_sub_norm_le
      hc hT hSigmaLower hSigmaUpper hRho
    simp only [div_eq_mul_inv]
    rw [<- mul_sub]
    rw [norm_mul, Complex.norm_int_of_nonneg hCoeffInt]
    have hScaled := mul_le_mul_of_nonneg_left hRecip hCoeffReal
    calc
      (riemannZetaLocalDivisor t rho : Int) *
          norm
            ((↑sigma + Complex.I * ↑t - rho)⁻¹ -
              (↑(1 + 1 / Real.log (|t| + 4)) +
                Complex.I * ↑t - rho)⁻¹) <=
          (riemannZetaLocalDivisor t rho : Int) *
            ((2 / (c / (4 * c + 6))) *
              (1 / (↑(1 + 1 / Real.log (|t| + 4)) +
                Complex.I * ↑t - rho)).re) := by
        simpa only [one_div] using hScaled
      _ = (2 / (c / (4 * c + 6))) *
          (((riemannZetaLocalDivisor t rho : Int) : Complex) *
            (↑(1 + 1 / Real.log (|t| + 4)) +
              Complex.I * ↑t - rho)⁻¹).re := by
        simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
          zero_mul, sub_zero]
        ring_nf
  · have hCoeff : riemannZetaLocalDivisor t rho = 0 := by
      simpa [Function.mem_support] using hRho
    simp [hCoeff]

/-- In the narrow high-height strip, the local zero sum differs from its
right-hand anchor by at most an absolute multiple (for the fixed zero-free
constant) of the anchor sum's real part. -/
theorem exists_riemannZetaLocalZeroSum_sub_bound
    {c : Real} (hc : IsRiemannZetaZeroFreeConstant c) :
    exists A : Real, 0 < A ∧
      forall t sigma : Real,
        7 / 8 <= |t| ->
        1 - c / (2 * Real.log (|t| + 4)) < sigma ->
        sigma <= 1 + 1 / Real.log (|t| + 4) ->
        norm
            (riemannZetaLocalZeroSum t
                ((sigma : Complex) + Complex.I * (t : Complex)) -
              riemannZetaLocalZeroSum t
                (((1 + 1 / Real.log (|t| + 4) : Real) : Complex) +
                  Complex.I * (t : Complex))) <=
          A *
            (riemannZetaLocalZeroSum t
              (((1 + 1 / Real.log (|t| + 4) : Real) : Complex) +
                Complex.I * (t : Complex))).re := by
  let kappa : Real := c / (4 * c + 6)
  have hcPos : 0 < c := hc.1
  have hkappaPos : 0 < kappa := by
    dsimp [kappa]
    positivity
  refine ⟨2 / kappa, by positivity, ?_⟩
  intro t sigma hT hSigmaLower hSigmaUpper
  let D := riemannZetaLocalDivisor t
  let chi : Complex -> Complex := fun rho =>
    ((D rho : Int) : Complex) /
      (((sigma : Complex) + Complex.I * (t : Complex)) - rho)
  let phi : Complex -> Complex := fun rho =>
    ((D rho : Int) : Complex) /
        (((sigma : Complex) + Complex.I * (t : Complex)) - rho) -
      ((D rho : Int) : Complex) /
        ((((1 + 1 / Real.log (|t| + 4) : Real) : Complex) +
          Complex.I * (t : Complex)) - rho)
  let psi : Complex -> Complex := fun rho =>
    ((D rho : Int) : Complex) /
      ((((1 + 1 / Real.log (|t| + 4) : Real) : Complex) +
        Complex.I * (t : Complex)) - rho)
  have hD : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall
      (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
      (5 / 6 : Real))
  have hChiSupp : chi.support ⊆ D.support := by
    intro rho hRho
    contrapose! hRho
    have : D rho = 0 := by simpa [Function.mem_support] using hRho
    simp [chi, this]
  have hPsiSupp : psi.support ⊆ D.support := by
    intro rho hRho
    contrapose! hRho
    have : D rho = 0 := by simpa [Function.mem_support] using hRho
    simp [psi, this]
  have hChi : (∑ᶠ rho : Complex, chi rho) =
      ∑ rho ∈ hD.toFinset, chi rho :=
    finsum_eq_sum_of_support_subset _
      (hChiSupp.trans (fun rho hRho => hD.mem_toFinset.mpr hRho))
  have hPsi : (∑ᶠ rho : Complex, psi rho) =
      ∑ rho ∈ hD.toFinset, psi rho :=
    finsum_eq_sum_of_support_subset _
      (hPsiSupp.trans (fun rho hRho => hD.mem_toFinset.mpr hRho))
  rw [riemannZetaLocalZeroSum, riemannZetaLocalZeroSum]
  change norm ((∑ᶠ rho : Complex, chi rho) - ∑ᶠ rho : Complex, psi rho) <=
    (2 / kappa) * (∑ᶠ rho : Complex, psi rho).re
  rw [hChi, hPsi, <- Finset.sum_sub_distrib]
  change norm (∑ rho ∈ hD.toFinset, phi rho) <=
    (2 / kappa) * (∑ rho ∈ hD.toFinset, psi rho).re
  calc
    norm (∑ rho ∈ hD.toFinset, phi rho) <=
        ∑ rho ∈ hD.toFinset, norm (phi rho) := norm_sum_le _ _
    _ <= ∑ rho ∈ hD.toFinset,
        (2 / kappa) * (psi rho).re := by
      gcongr with rho hRho
      simpa [D, phi, psi, kappa] using
        localZeroTerm_sub_norm_le hc hT hSigmaLower hSigmaUpper (rho := rho)
    _ = (2 / kappa) *
        (∑ rho ∈ hD.toFinset, psi rho).re := by
      change (∑ rho ∈ hD.toFinset, (2 / kappa) * (psi rho).re) =
        (2 / kappa) * Complex.reCLM (∑ rho ∈ hD.toFinset, psi rho)
      simp only [map_sum]
      exact (Finset.mul_sum _ _ _).symm

end PrimesRestrictedDigits
