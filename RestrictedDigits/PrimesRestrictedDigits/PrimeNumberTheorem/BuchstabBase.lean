import PrimesRestrictedDigits.BasicEstimates.BuchstabBaseCount
import PrimesRestrictedDigits.PrimeNumberTheorem.PrimeCountingLogSquare

/-!
# The Buchstab estimate on the base range

The finite form of Montgomery--Vaughan Eq. (7.35) is combined with the global
log-square prime number theorem.  This supplies the `1 <= u <= 2` seed for the
later Buchstab induction, before reparameterization by `u = log x / log y`.
-/

open MeasureTheory

namespace PrimesRestrictedDigits

/-- There is one absolute log-square coefficient for the Buchstab rough count
throughout the square-root base range. -/
theorem exists_buchstabPhi_base_error :
    ∃ C : Real, 0 < C ∧
      ∀ x y : Real, 2 <= y -> Real.sqrt x <= y -> y <= x ->
        |(buchstabPhi x y : Real) -
            (x / Real.log x - y / Real.log y)| <=
          C * x / Real.log x ^ 2 := by
  obtain ⟨C0, hC0, hPNT⟩ := primeCounting_log_sq_error
  refine ⟨5 * C0 + 16, by positivity, ?_⟩
  intro x y hy hroot hyx
  have hy0 : 0 <= y := by linarith
  have hx : 2 <= x := hy.trans hyx
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hlogyPos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogxPos : 0 < Real.log x := Real.log_pos (by linarith)
  let scale : Real := x / Real.log x ^ 2
  have hlogRoot : Real.log x / 2 <= Real.log y := by
    calc
      Real.log x / 2 = Real.log (Real.sqrt x) :=
        (Real.log_sqrt hx0).symm
      _ <= Real.log y :=
        Real.log_le_log (Real.sqrt_pos.2 hxpos) hroot
  have hlogCompare : Real.log x <= 2 * Real.log y := by linarith
  have hlogSqCompare : Real.log x ^ 2 <= 4 * Real.log y ^ 2 := by
    nlinarith
  have hscaleY : y / Real.log y ^ 2 <= 4 * scale := by
    dsimp [scale]
    rw [show 4 * (x / Real.log x ^ 2) =
      (4 * x) / Real.log x ^ 2 by ring]
    rw [div_le_div_iff₀ (sq_pos_of_pos hlogyPos)
      (sq_pos_of_pos hlogxPos)]
    calc
      y * Real.log x ^ 2 <= x * Real.log x ^ 2 :=
        mul_le_mul_of_nonneg_right hyx (sq_nonneg _)
      _ <= x * (4 * Real.log y ^ 2) :=
        mul_le_mul_of_nonneg_left hlogSqCompare hx0
      _ = 4 * x * Real.log y ^ 2 := by ring
  have hIntTwoY : IntervalIntegrable
      (fun t : Real => 1 / Real.log t ^ 2) volume 2 y :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hIntYX : IntervalIntegrable
      (fun t : Real => 1 / Real.log t ^ 2) volume y x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by linarith) (by linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hIntTwoY hIntYX
  have hcorrectionEq :
      (logarithmicIntegral x - logarithmicIntegral y) -
          (x / Real.log x - y / Real.log y) =
        ∫ t in y..x, 1 / Real.log t ^ 2 := by
    rw [logarithmicIntegral_eq_div_add_integral hx,
      logarithmicIntegral_eq_div_add_integral hy]
    linarith
  have hIntNonneg : 0 <= ∫ t in y..x, 1 / Real.log t ^ 2 :=
    intervalIntegral.integral_nonneg hyx fun t _ => by positivity
  have hIntUpper : (∫ t in y..x, 1 / Real.log t ^ 2) <= 4 * scale := by
    have hmono : (∫ t in y..x, 1 / Real.log t ^ 2) <=
        ∫ _t in y..x, 4 / Real.log x ^ 2 := by
      apply intervalIntegral.integral_mono_on hyx hIntYX intervalIntegrable_const
      intro t ht
      have hyt : y <= t := ht.1
      have htpos : 0 < t := lt_of_lt_of_le (by linarith) hyt
      have hlogtPos : 0 < Real.log t := Real.log_pos (by linarith)
      have hlogyt : Real.log y <= Real.log t :=
        Real.log_le_log (by linarith) hyt
      have hlogxt : Real.log x / 2 <= Real.log t :=
        hlogRoot.trans hlogyt
      have hlogSq : Real.log x ^ 2 <= 4 * Real.log t ^ 2 := by
        nlinarith
      rw [div_le_div_iff₀ (sq_pos_of_pos hlogtPos)
        (sq_pos_of_pos hlogxPos)]
      simpa using hlogSq
    calc
      (∫ t in y..x, 1 / Real.log t ^ 2) <=
          ∫ _t in y..x, 4 / Real.log x ^ 2 := hmono
      _ = (x - y) * (4 / Real.log x ^ 2) := by simp; ring
      _ <= x * (4 / Real.log x ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 4 * scale := by dsimp [scale]; ring
  have hcorrection :
      |(logarithmicIntegral x - logarithmicIntegral y) -
          (x / Real.log x - y / Real.log y)| <= 4 * scale := by
    rw [hcorrectionEq, abs_of_nonneg hIntNonneg]
    exact hIntUpper
  have hlogSqrt : Real.log x <= 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div (x := x) (ε := (1 / 2 : Real)) hx0 (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    norm_num at h ⊢
    linarith
  have hlogSqSelf : Real.log x ^ 2 <= 4 * x := by
    nlinarith [Real.sq_sqrt hx0]
  have hscaleLower : (1 : Real) / 4 <= scale := by
    dsimp [scale]
    rw [div_le_div_iff₀ (by norm_num : (0 : Real) < 4)
      (sq_pos_of_pos hlogxPos)]
    nlinarith
  have hthree : (3 : Real) <= 12 * scale := by nlinarith
  have hfinite := abs_buchstabPhi_sub_prime_counts_le_three hy hroot hyx
  have hPNTx : |realPrimeCounting x - logarithmicIntegral x| <= C0 * scale := by
    convert hPNT x hx using 1; dsimp [scale]; ring
  have hPNTy : |realPrimeCounting y - logarithmicIntegral y| <=
      4 * C0 * scale := by
    calc
      |realPrimeCounting y - logarithmicIntegral y| <=
          C0 * (y / Real.log y ^ 2) := by
            simpa only [mul_div_assoc] using hPNT y hy
      _ <= C0 * (4 * scale) :=
        mul_le_mul_of_nonneg_left hscaleY hC0.le
      _ = 4 * C0 * scale := by ring
  let A : Real := (buchstabPhi x y : Real) -
    (realPrimeCounting x - realPrimeCounting y)
  let B : Real := realPrimeCounting x - logarithmicIntegral x
  let D : Real := realPrimeCounting y - logarithmicIntegral y
  let Q : Real := (logarithmicIntegral x - logarithmicIntegral y) -
    (x / Real.log x - y / Real.log y)
  have hdecomp :
      (buchstabPhi x y : Real) -
          (x / Real.log x - y / Real.log y) = A + B - D + Q := by
    dsimp [A, B, D, Q]
    ring
  have htriangle : |A + B - D + Q| <= |A| + |B| + |D| + |Q| := by
    calc
      |A + B - D + Q| <= |A + B - D| + |Q| := abs_add_le _ _
      _ <= (|A + B| + |D|) + |Q| := by
        gcongr
        simpa [sub_eq_add_neg] using abs_add_le (A + B) (-D)
      _ <= ((|A| + |B|) + |D|) + |Q| := by
        gcongr
        exact abs_add_le A B
      _ = |A| + |B| + |D| + |Q| := by ring
  rw [hdecomp]
  calc
    |A + B - D + Q| <= |A| + |B| + |D| + |Q| := htriangle
    _ <= 3 + C0 * scale + 4 * C0 * scale + 4 * scale := by
      exact add_le_add
        (add_le_add (add_le_add (by simpa [A] using hfinite)
          (by simpa [B] using hPNTx)) (by simpa [D] using hPNTy))
        (by simpa [Q] using hcorrection)
    _ = (5 * C0 + 4) * scale + 3 := by ring
    _ <= (5 * C0 + 4) * scale + 12 * scale :=
      by linarith
    _ = (5 * C0 + 16) * x / Real.log x ^ 2 := by
      dsimp [scale]
      ring

end PrimesRestrictedDigits
