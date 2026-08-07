import BoundedGaps.Maynard.MaynardS2OuterCoefficientBounds
import BoundedGaps.Maynard.MaynardS2OuterMainTerm
import BoundedGaps.Maynard.WeightedSmoothAbel

noncomputable section

/-!
# All-endpoint cumulative estimate for the S2 outer weight

SEM-271 supplies the logarithmic main term beyond the primorial.  The
pointwise bounds from SEM-280 control the initial range, yielding one explicit
estimate for every real endpoint used by Abel summation.
-/

namespace BoundedGaps.Maynard

open ArithmeticFunction Finset Nat Real
open scoped BigOperators

noncomputable def maynardS2OuterCumulativeError (D : ℕ) : ℝ :=
  (2 * (Real.exp 16 + 8 * maynardS2OuterCorrectionQuarterConstant) +
      (1 + 8 / (D : ℝ)) * primorial D +
      (1 + 8 / (D : ℝ)) *
        (primeLogPredecessorSum D + Real.log 2)) +
    ((primorial D : ℝ) +
      (1 + 8 / (D : ℝ)) * Real.log (primorial D))

theorem primeLogPredecessorSum_nonneg (D : ℕ) :
    0 ≤ primeLogPredecessorSum D := by
  unfold primeLogPredecessorSum
  exact Finset.sum_nonneg fun p hp => by positivity

theorem maynardS2OuterSquarefreeMean_nonneg (W Q : ℕ) :
    0 ≤ maynardS2OuterSquarefreeMean W Q := by
  unfold maynardS2OuterSquarefreeMean
  exact Finset.sum_nonneg fun n hn =>
    maynardS2OuterSquarefreeAF_nonneg W n

theorem maynardS2OuterSquarefreeMean_le (W Q : ℕ) :
    maynardS2OuterSquarefreeMean W Q ≤ Q := by
  unfold maynardS2OuterSquarefreeMean
  calc
    (∑ n ∈ Finset.Icc 1 Q, maynardS2OuterSquarefreeAF W n) ≤
        ∑ n ∈ Finset.Icc 1 Q, (1 : ℝ) := by
      exact Finset.sum_le_sum fun n hn =>
        maynardS2OuterSquarefreeAF_le_one W n
    _ = Q := by simp

theorem abelCumulative_maynardS2OuterSquarefreeAF_eq_mean
    (W : ℕ) (t : ℝ) :
    abelCumulative (maynardS2OuterSquarefreeAF W) t =
      maynardS2OuterSquarefreeMean W ⌊t⌋₊ := by
  unfold abelCumulative maynardS2OuterSquarefreeMean
  have hinterval : Finset.Icc 0 ⌊t⌋₊ =
      {0} ∪ Finset.Icc 1 ⌊t⌋₊ := by
    ext n
    simp
    omega
  have hdisjoint : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 ⌊t⌋₊) := by
    simp
  rw [hinterval, Finset.sum_union hdisjoint]
  simp [(maynardS2OuterSquarefreeAF W).map_zero]

theorem preSieveSingularSeries_le_one (D : ℕ) :
    preSieveSingularSeries D ≤ 1 := by
  rw [preSieveSingularSeries_eq_totient_div]
  have hW : (0 : ℝ) < primorial D := by exact_mod_cast primorial_pos D
  apply (div_le_one hW).2
  exact_mod_cast Nat.totient_le (primorial D)

theorem abs_maynardS2OuterSingularSeries_le
    {D : ℕ} (hD : 2 ≤ D) :
    |maynardS2OuterSingularSeries D| ≤ 1 + 8 / (D : ℝ) := by
  unfold maynardS2OuterSingularSeries
  rw [abs_mul, abs_of_pos (preSieveSingularSeries_pos_from_totient D)]
  calc
    preSieveSingularSeries D *
        |maynardS2OuterInfiniteSingularTail D| ≤
        1 * |maynardS2OuterInfiniteSingularTail D| := by
      exact mul_le_mul_of_nonneg_right (preSieveSingularSeries_le_one D)
        (abs_nonneg _)
    _ ≤ 1 + 8 / (D : ℝ) := by
      simpa using abs_maynardS2OuterInfiniteSingularTail_le hD

private theorem abs_log_natFloor_sub_log_le_log_two
    {t : ℝ} (ht : 1 ≤ t) :
    |Real.log (⌊t⌋₊ : ℕ) - Real.log t| ≤ Real.log 2 := by
  let q : ℕ := ⌊t⌋₊
  have hqOne : 1 ≤ q := by
    exact (Nat.one_le_floor_iff t).2 ht
  have hqPos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hqOne
  have htPos : 0 < t := zero_lt_one.trans_le ht
  have hqt : (q : ℝ) ≤ t := by
    exact Nat.floor_le htPos.le
  have htSucc : t < (q : ℝ) + 1 := by
    simpa [q, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  have hsuccTwo : (q : ℝ) + 1 ≤ 2 * q := by
    exact_mod_cast (show q + 1 ≤ 2 * q by omega)
  have htTwo : t ≤ 2 * (q : ℝ) := htSucc.le.trans hsuccTwo
  have hlogLower : Real.log q ≤ Real.log t :=
    Real.strictMonoOn_log.monotoneOn hqPos htPos hqt
  have htwoPos : (0 : ℝ) < 2 * q := mul_pos (by norm_num) hqPos
  have hlogUpper : Real.log t ≤ Real.log q + Real.log 2 := by
    have hmono := Real.strictMonoOn_log.monotoneOn htPos htwoPos htTwo
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hqPos.ne'] at hmono
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hlogLower)]
  linarith

theorem maynardS2OuterCumulativeError_nonneg
    {D : ℕ} (hD : 2 ≤ D) :
    0 ≤ maynardS2OuterCumulativeError D := by
  have hfactor : 0 ≤ 1 + 8 / (D : ℝ) := by positivity
  have hB := primeLogPredecessorSum_nonneg D
  have hlogW : 0 ≤ Real.log (primorial D) :=
    Real.log_natCast_nonneg (primorial D)
  have hCq : 0 ≤ maynardS2OuterCorrectionQuarterConstant := by
    unfold maynardS2OuterCorrectionQuarterConstant
    positivity
  have hC0 : 0 ≤ 2 * (Real.exp 16 +
      8 * maynardS2OuterCorrectionQuarterConstant) := by
    exact mul_nonneg (by norm_num)
      (add_nonneg (by positivity) (mul_nonneg (by norm_num) hCq))
  have hW : 0 ≤ (primorial D : ℝ) := by positivity
  have hB2 : 0 ≤ primeLogPredecessorSum D + Real.log 2 :=
    add_nonneg hB (Real.log_natCast_nonneg 2)
  unfold maynardS2OuterCumulativeError
  exact add_nonneg
    (add_nonneg (add_nonneg hC0 (mul_nonneg hfactor hW))
      (mul_nonneg hfactor hB2))
    (add_nonneg hW (mul_nonneg hfactor hlogW))

set_option maxHeartbeats 1200000 in
theorem abs_abelCumulative_maynardS2OuterSquarefreeAF_sub_log_le
    {D : ℕ} (hD : 2 ≤ D) {t : ℝ} (ht : 1 ≤ t) :
    |abelCumulative (maynardS2OuterSquarefreeAF (primorial D)) t -
        maynardS2OuterSingularSeries D * Real.log t| ≤
      maynardS2OuterCumulativeError D := by
  let q : ℕ := ⌊t⌋₊
  let W : ℕ := primorial D
  let S : ℝ := maynardS2OuterSingularSeries D
  let B : ℝ := primeLogPredecessorSum D
  let F : ℝ := 1 + 8 / (D : ℝ)
  have hAeq :
      abelCumulative (maynardS2OuterSquarefreeAF W) t =
        maynardS2OuterSquarefreeMean W q := by
    exact abelCumulative_maynardS2OuterSquarefreeAF_eq_mean W t
  have hF : 0 ≤ F := by unfold F; positivity
  have hS : |S| ≤ F := by
    exact abs_maynardS2OuterSingularSeries_le hD
  have hB : 0 ≤ B := primeLogPredecessorSum_nonneg D
  have hlogFloor : |Real.log q - Real.log t| ≤ Real.log 2 := by
    exact abs_log_natFloor_sub_log_le_log_two ht
  rw [hAeq]
  by_cases hWq : W ≤ q
  · have hMain :
        |maynardS2OuterSquarefreeMean W q -
            S * (Real.log q + B)| ≤
          2 * (Real.exp 16 +
            8 * maynardS2OuterCorrectionQuarterConstant) + F * W := by
      simpa [W, S, B, F] using
        abs_maynardS2OuterSquarefreeMean_sub_singularSeries_mul_logMainTerm_le
          hD hWq
    have hlogCorrection :
        |(Real.log q + B) - Real.log t| ≤ B + Real.log 2 := by
      calc
        |(Real.log q + B) - Real.log t| =
            |B + (Real.log q - Real.log t)| := by ring_nf
        _ ≤ |B| + |Real.log q - Real.log t| := abs_add_le _ _
        _ ≤ B + Real.log 2 := by
          rw [abs_of_nonneg hB]
          simpa [add_comm] using add_le_add_left hlogFloor B
    have hScaled :
        |S * ((Real.log q + B) - Real.log t)| ≤
          F * (B + Real.log 2) := by
      rw [abs_mul]
      calc
        |S| * |(Real.log q + B) - Real.log t| ≤
            F * |(Real.log q + B) - Real.log t| :=
          mul_le_mul_of_nonneg_right hS (abs_nonneg _)
        _ ≤ F * (B + Real.log 2) :=
          mul_le_mul_of_nonneg_left hlogCorrection hF
    have hHigh :
        |maynardS2OuterSquarefreeMean W q - S * Real.log t| ≤
          2 * (Real.exp 16 +
            8 * maynardS2OuterCorrectionQuarterConstant) + F * W +
              F * (B + Real.log 2) := by
      rw [show maynardS2OuterSquarefreeMean W q - S * Real.log t =
          (maynardS2OuterSquarefreeMean W q -
            S * (Real.log q + B)) +
            S * ((Real.log q + B) - Real.log t) by ring]
      exact (abs_add_le _ _).trans (add_le_add hMain hScaled)
    calc
      |maynardS2OuterSquarefreeMean W q - S * Real.log t| ≤
          2 * (Real.exp 16 +
            8 * maynardS2OuterCorrectionQuarterConstant) + F * W +
              F * (B + Real.log 2) := hHigh
      _ ≤ maynardS2OuterCumulativeError D := by
        simp only [maynardS2OuterCumulativeError, W, F]
        apply le_add_of_nonneg_right
        positivity
  · have hqW : q < W := Nat.lt_of_not_ge hWq
    have hmeanNonneg := maynardS2OuterSquarefreeMean_nonneg W q
    have hmeanLe : maynardS2OuterSquarefreeMean W q ≤ (W : ℝ) := by
      exact (maynardS2OuterSquarefreeMean_le W q).trans
        (by exact_mod_cast hqW.le)
    have htW : t < (W : ℝ) := by
      exact (Nat.floor_lt' (primorial_ne_zero D)).1 (by simpa [q, W] using hqW)
    have htPos : 0 < t := zero_lt_one.trans_le ht
    have hWPos : (0 : ℝ) < W := by exact_mod_cast primorial_pos D
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
    have hlogW : 0 ≤ Real.log W := Real.log_natCast_nonneg W
    have hlogLe : Real.log t ≤ Real.log W :=
      Real.strictMonoOn_log.monotoneOn htPos hWPos htW.le
    have hLow :
        |maynardS2OuterSquarefreeMean W q - S * Real.log t| ≤
          (W : ℝ) + F * Real.log W := by
      calc
        |maynardS2OuterSquarefreeMean W q - S * Real.log t| ≤
            |maynardS2OuterSquarefreeMean W q| +
              |S * Real.log t| := abs_sub _ _
        _ = maynardS2OuterSquarefreeMean W q + |S| * Real.log t := by
          rw [abs_of_nonneg hmeanNonneg, abs_mul, abs_of_nonneg hlogt]
        _ ≤ (W : ℝ) + F * Real.log W := by
          apply add_le_add hmeanLe
          calc
            |S| * Real.log t ≤ F * Real.log t :=
              mul_le_mul_of_nonneg_right hS hlogt
            _ ≤ F * Real.log W :=
              mul_le_mul_of_nonneg_left hlogLe hF
    calc
      |maynardS2OuterSquarefreeMean W q - S * Real.log t| ≤
          (W : ℝ) + F * Real.log W := hLow
      _ ≤ maynardS2OuterCumulativeError D := by
        simp only [maynardS2OuterCumulativeError, W, F]
        have hB' := primeLogPredecessorSum_nonneg D
        have hCq : 0 ≤ maynardS2OuterCorrectionQuarterConstant := by
          unfold maynardS2OuterCorrectionQuarterConstant
          positivity
        have hC0 : 0 ≤ 2 * (Real.exp 16 +
            8 * maynardS2OuterCorrectionQuarterConstant) := by
          exact mul_nonneg (by norm_num)
            (add_nonneg (by positivity) (mul_nonneg (by norm_num) hCq))
        have hF : 0 ≤ 1 + 8 / (D : ℝ) := by positivity
        have hW : 0 ≤ (primorial D : ℝ) := by positivity
        have hB2 : 0 ≤ primeLogPredecessorSum D + Real.log 2 :=
          add_nonneg hB' (Real.log_natCast_nonneg 2)
        apply le_add_of_nonneg_left
        exact add_nonneg
          (add_nonneg hC0 (mul_nonneg hF hW)) (mul_nonneg hF hB2)

end BoundedGaps.Maynard
