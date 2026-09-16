import PrimesRestrictedDigits.PrimeNumberTheorem.PerronVonMangoldtRemainder
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLogDerivativeBounds
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronEdgeBounds
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronOptimizedParameters
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronOptimizedPower

/-!
# The optimized zeta Perron error

This combines the right-line Perron remainder and the three shifted contour
edges at the height chosen for `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6,
Theorem 6.9, p. 181.
-/

namespace PrimesRestrictedDigits

/-- At the optimized contour height, the Chebyshev error is bounded by one
absolute coefficient times `x * (log x)^2 / T`. -/
theorem exists_abs_psi_sub_self_le_log_sq_div_zetaPerronHeight :
    ∃ c K : Real,
      IsRiemannZetaZeroFreeConstant c ∧ 0 < K ∧
      ∀ x : Real, 4 <= x ->
        zetaPerronLogThreshold c <= Real.log x ->
        |Chebyshev.psi x - x| <=
          K * x * Real.log x ^ 2 / zetaPerronHeight c x := by
  obtain ⟨c, C, hc, hC, hHigh, hLow⟩ := exists_riemannZeta_logDeriv_bounds
  obtain ⟨P, hP, hPerron⟩ :=
    exists_norm_psi_sub_zetaPerronIntegral_rightLine_le
  let K : Real := P + 26 * C + 16 / c
  refine ⟨c, K, hc, ?_, ?_⟩
  · dsimp [K]
    have hcInv : 0 < 16 / c := div_pos (by norm_num) hc.1
    nlinarith
  intro x hx hLarge
  let L : Real := Real.log x
  let T : Real := zetaPerronHeight c x
  let Q : Real := x * L ^ 2 / T
  have hxPos : 0 < x := by linarith
  have hLOne : 1 <= L := by
    dsimp [L]
    exact (one_le_zetaPerronLogThreshold c).trans hLarge
  have hLSqOne : 1 <= L ^ 2 := by nlinarith
  have hTBounds : 4 <= T ∧ T <= x := by
    dsimp [T]
    exact zetaPerronHeight_bounds hc hxPos hLarge
  have hTTwo : 2 <= T := (by linarith [hTBounds.1])
  have hTPos : 0 < T := by linarith [hTBounds.1]
  have hxDivTNonneg : 0 <= x / T := div_nonneg hxPos.le hTPos.le
  have hCInvPos : 0 < C + 1 / c :=
    add_pos hC (one_div_pos.mpr hc.1)
  have hPerronBound :
      ‖(Chebyshev.psi x : Complex) -
          zetaPerronIntegral x (1 + 1 / Real.log x) T‖ <= P * Q := by
    calc
      ‖(Chebyshev.psi x : Complex) -
          zetaPerronIntegral x (1 + 1 / Real.log x) T‖ <=
          P * x * Real.log x ^ 2 / T :=
        hPerron x T hx hTTwo hTBounds.2
      _ = P * Q := by
        dsimp [Q, L]
        ring
  have hHorizontalScale : x / T <= Q := by
    calc
      x / T = (x / T) * 1 := by ring
      _ <= (x / T) * L ^ 2 :=
        mul_le_mul_of_nonneg_left hLSqOne hxDivTNonneg
      _ = Q := by
        dsimp [Q]
        ring
  have hLeftPower :
      x ^ zetaPerronLeftLine c T <= x / T := by
    simpa only [T] using
      (zetaPerronLeftPower_le_div_height hc hxPos hLarge)
  have hLogSq :
      Real.log (T + 4) ^ 2 <= L ^ 2 := by
    simpa only [T, L] using
      (log_zetaPerronHeight_add_four_sq_le_log_sq hc hxPos hLarge)
  have hLeftProduct :
      x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 <= Q := by
    calc
      x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 <=
          (x / T) * Real.log (T + 4) ^ 2 :=
        mul_le_mul_of_nonneg_right hLeftPower (sq_nonneg _)
      _ <= (x / T) * L ^ 2 :=
        mul_le_mul_of_nonneg_left hLogSq hxDivTNonneg
      _ = Q := by
        dsimp [Q]
        ring
  have hHorizontalTerm :
      10 * C * x / T <= 10 * C * Q := by
    calc
      10 * C * x / T = (10 * C) * (x / T) := by ring
      _ <= (10 * C) * Q :=
        mul_le_mul_of_nonneg_left hHorizontalScale (by positivity)
      _ = 10 * C * Q := by ring
  have hLeftTerm :
      16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
          Real.log (T + 4) ^ 2 <=
        16 * (C + 1 / c) * Q := by
    calc
      16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
          Real.log (T + 4) ^ 2 =
          (16 * (C + 1 / c)) *
            (x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2) := by
        ring
      _ <= (16 * (C + 1 / c)) * Q :=
        mul_le_mul_of_nonneg_left hLeftProduct
          (mul_nonneg (by norm_num) hCInvPos.le)
      _ = 16 * (C + 1 / c) * Q := by ring
  have hBracket :
      10 * C * x / T +
          16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
            Real.log (T + 4) ^ 2 <=
        (26 * C + 16 / c) * Q := by
    calc
      10 * C * x / T +
          16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
            Real.log (T + 4) ^ 2 <=
          10 * C * Q + 16 * (C + 1 / c) * Q :=
        add_le_add hHorizontalTerm hLeftTerm
      _ = (26 * C + 16 / c) * Q := by ring
  have hBracketNonneg :
      0 <= 10 * C * x / T +
        16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
          Real.log (T + 4) ^ 2 := by
    have hLeftCoeff : 0 <= 16 * (C + 1 / c) :=
      mul_nonneg (by norm_num) hCInvPos.le
    positivity
  have hScaleLeOne : 1 / (2 * Real.pi) <= 1 := by
    rw [div_le_one (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.pi_gt_three]
  have hEdgeBound :
      ‖zetaPerronIntegral x (1 + 1 / Real.log x) T - (x : Complex)‖ <=
        (26 * C + 16 / c) * Q := by
    calc
      ‖zetaPerronIntegral x (1 + 1 / Real.log x) T - (x : Complex)‖ <=
          (1 / (2 * Real.pi)) *
            (10 * C * x / T +
              16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
                Real.log (T + 4) ^ 2) :=
        norm_zetaPerronIntegral_sub_self_le
          hc hC hHigh hLow hx hTTwo hTBounds.2
      _ <= 1 *
            (10 * C * x / T +
              16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
                Real.log (T + 4) ^ 2) :=
        mul_le_mul_of_nonneg_right hScaleLeOne hBracketNonneg
      _ <= (26 * C + 16 / c) * Q := by
        simpa only [one_mul] using hBracket
  have hTriangle :
      ‖(Chebyshev.psi x : Complex) - (x : Complex)‖ <=
        ‖(Chebyshev.psi x : Complex) -
            zetaPerronIntegral x (1 + 1 / Real.log x) T‖ +
          ‖zetaPerronIntegral x (1 + 1 / Real.log x) T - (x : Complex)‖ := by
    calc
      ‖(Chebyshev.psi x : Complex) - (x : Complex)‖ =
          ‖((Chebyshev.psi x : Complex) -
              zetaPerronIntegral x (1 + 1 / Real.log x) T) +
            (zetaPerronIntegral x (1 + 1 / Real.log x) T -
              (x : Complex))‖ := by
        congr 1
        ring
      _ <= _ := norm_add_le _ _
  have hCombined :
      ‖(Chebyshev.psi x : Complex) - (x : Complex)‖ <= K * Q := by
    calc
      ‖(Chebyshev.psi x : Complex) - (x : Complex)‖ <=
          ‖(Chebyshev.psi x : Complex) -
              zetaPerronIntegral x (1 + 1 / Real.log x) T‖ +
            ‖zetaPerronIntegral x (1 + 1 / Real.log x) T -
              (x : Complex)‖ := hTriangle
      _ <= P * Q + (26 * C + 16 / c) * Q :=
        add_le_add hPerronBound hEdgeBound
      _ = K * Q := by
        dsimp [K]
        ring
  have hNormReal :
      ‖(Chebyshev.psi x : Complex) - (x : Complex)‖ =
        |Chebyshev.psi x - x| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    |Chebyshev.psi x - x| =
        ‖(Chebyshev.psi x : Complex) - (x : Complex)‖ := hNormReal.symm
    _ <= K * Q := hCombined
    _ = K * x * Real.log x ^ 2 / zetaPerronHeight c x := by
      dsimp [Q, L, T]
      ring

end PrimesRestrictedDigits
