import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayRapidDecay

/-!
# Logarithmic lower shift and rapid envelope

This derives the explicit Corollary to Iwaniec's Lemma 16, transfers it to both delay
functions, and records a source-independent rapid upper envelope. See
`IWANIEC-ROSSER-SIEVE-1980`, printed pp. 191--193.
-/

open Set

namespace PrimesRestrictedDigits

/-- Explicit global form of the logarithmic reverse shift for the corrected
dimension-one sum. -/
theorem dimensionOneDelaySum_log_shift_lt {s : Real} (hs : 2 <= s) :
    s * Real.log s * dimensionOneDelaySum s <
      16 * dimensionOneDelaySum (s - 1) := by
  have hs0 : 0 < s := by linarith
  have haPos : 0 < dimensionOneDelaySum s := dimensionOneDelaySum_pos hs0
  have hPrevPos : 0 < dimensionOneDelaySum (s - 1) :=
    dimensionOneDelaySum_pos (by linarith)
  by_cases hs3 : s < 3
  · have hLog := Real.log_le_sub_one_of_pos hs0
    have hCoeff : s * Real.log s < 16 := by
      nlinarith [sq_nonneg (s - 2)]
    have hAnti : dimensionOneDelaySum s < dimensionOneDelaySum (s - 1) :=
      dimensionOneDelaySum_strictAntiOn
        (by change 0 < s - 1; linarith)
        (by change 0 < s; exact hs0) (by linarith)
    calc
      s * Real.log s * dimensionOneDelaySum s <
          16 * dimensionOneDelaySum s :=
        mul_lt_mul_of_pos_right hCoeff haPos
      _ < 16 * dimensionOneDelaySum (s - 1) :=
        mul_lt_mul_of_pos_left hAnti (by norm_num)
  have hs3' : 3 <= s := le_of_not_gt hs3
  by_cases hs4 : s < 4
  · have hLog : Real.log s < s := by
      have h := Real.log_lt_sub_one_of_pos hs0 (by linarith : s ≠ 1)
      linarith
    have hCoeff : s * Real.log s < 16 * (s - 2) := by
      have hMul := mul_lt_mul_of_pos_left hLog hs0
      nlinarith
    have hLinear := dimensionOneDelaySum_linear_shift_lt hs3'
    calc
      s * Real.log s * dimensionOneDelaySum s <
          (16 * (s - 2)) * dimensionOneDelaySum s :=
        mul_lt_mul_of_pos_right hCoeff haPos
      _ = 16 * ((s - 2) * dimensionOneDelaySum s) := by ring
      _ < 16 * dimensionOneDelaySum (s - 1) :=
        mul_lt_mul_of_pos_left hLinear (by norm_num)
  have hLogTwo : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : Real)) (by norm_num)
      (by norm_num)
    norm_num at h
    exact h
  by_cases hs256 : s < 256
  · have hLog256 : Real.log (256 : Real) = 8 * Real.log 2 := by
      rw [show (256 : Real) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    have hLogLt : Real.log s < 8 := by
      have hMono := Real.strictMonoOn_log
        (show s ∈ Ioi (0 : Real) by exact hs0)
        (show (256 : Real) ∈ Ioi 0 by norm_num) hs256
      rw [hLog256] at hMono
      linarith
    have hCoeff : s * Real.log s < 16 * (s - 2) := by
      have hMul := mul_lt_mul_of_pos_left hLogLt hs0
      nlinarith
    have hLinear := dimensionOneDelaySum_linear_shift_lt hs3'
    calc
      s * Real.log s * dimensionOneDelaySum s <
          (16 * (s - 2)) * dimensionOneDelaySum s :=
        mul_lt_mul_of_pos_right hCoeff haPos
      _ = 16 * ((s - 2) * dimensionOneDelaySum s) := by ring
      _ < 16 * dimensionOneDelaySum (s - 1) :=
        mul_lt_mul_of_pos_left hLinear (by norm_num)
  by_cases hs16384 : s < 16384
  · have hLog16384 : Real.log (16384 : Real) = 14 * Real.log 2 := by
      rw [show (16384 : Real) = 2 ^ 14 by norm_num, Real.log_pow]
      norm_num
    have hLogLt : Real.log s < 14 := by
      have hMono := Real.strictMonoOn_log
        (show s ∈ Ioi (0 : Real) by exact hs0)
        (show (16384 : Real) ∈ Ioi 0 by norm_num) hs16384
      rw [hLog16384] at hMono
      linarith
    have hCoeff : s * Real.log s < 16 * (s - 2) := by
      have hMul := mul_lt_mul_of_pos_left hLogLt hs0
      nlinarith
    have hLinear := dimensionOneDelaySum_linear_shift_lt hs3'
    calc
      s * Real.log s * dimensionOneDelaySum s <
          (16 * (s - 2)) * dimensionOneDelaySum s :=
        mul_lt_mul_of_pos_right hCoeff haPos
      _ = 16 * ((s - 2) * dimensionOneDelaySum s) := by ring
      _ < 16 * dimensionOneDelaySum (s - 1) :=
        mul_lt_mul_of_pos_left hLinear (by norm_num)
  · have hsBig : (16384 : Real) <= s := le_of_not_gt hs16384
    have hLog128Sq : Real.log ((128 : Real) ^ 2) =
        2 * Real.log 128 := by
      rw [Real.log_pow]
      norm_num
    have hLogLower : 2 * Real.log 128 <= Real.log s := by
      have hMono := Real.strictMonoOn_log.monotoneOn
        (show (128 : Real) ^ 2 ∈ Ioi 0 by
          change 0 < (128 : Real) ^ 2
          positivity)
        (show s ∈ Ioi 0 by exact hs0)
        (by norm_num at hsBig ⊢; exact hsBig)
      rw [hLog128Sq] at hMono
      exact hMono
    have hLogCompare : Real.log s <=
        2 * dimensionOneDelayLogWeight s := by
      unfold dimensionOneDelayLogWeight
      rw [Real.log_div hs0.ne' (by norm_num : (128 : Real) ≠ 0)]
      linarith
    have hD := dimensionOneDelayRapidDefect_neg hs3'
    unfold dimensionOneDelayRapidDefect at hD
    have hLogScale := mul_le_mul_of_nonneg_left hLogCompare
      (mul_nonneg hs0.le haPos.le)
    have hScale :
        s * Real.log s * dimensionOneDelaySum s <=
          2 * (s * dimensionOneDelaySum s *
            dimensionOneDelayLogWeight s) := by
      calc
        s * Real.log s * dimensionOneDelaySum s =
            (s * dimensionOneDelaySum s) * Real.log s := by ring
        _ <= (s * dimensionOneDelaySum s) *
            (2 * dimensionOneDelayLogWeight s) := hLogScale
        _ = 2 * (s * dimensionOneDelaySum s *
            dimensionOneDelayLogWeight s) := by ring
    calc
      s * Real.log s * dimensionOneDelaySum s <=
          2 * (s * dimensionOneDelaySum s *
            dimensionOneDelayLogWeight s) := hScale
      _ < 2 * dimensionOneDelaySum (s - 1) :=
        mul_lt_mul_of_pos_left (by linarith :
          s * dimensionOneDelaySum s * dimensionOneDelayLogWeight s <
            dimensionOneDelaySum (s - 1)) (by norm_num)
      _ < 16 * dimensionOneDelaySum (s - 1) := by nlinarith

private theorem dimensionOneDelayQ_log_shift_lt
    (QCurrent QPrevious : Real)
    {s : Real} (hs : 2 <= s)
    (hCurrent : QCurrent < 3 * dimensionOneDelaySum s / 4)
    (hPrevious : dimensionOneDelaySum (s - 1) / 4 < QPrevious) :
    s * Real.log s * QCurrent < 48 * QPrevious := by
  have hCoeff : 0 < s * Real.log s :=
    mul_pos (by linarith) (Real.log_pos (by linarith))
  have hSum := dimensionOneDelaySum_log_shift_lt hs
  calc
    s * Real.log s * QCurrent <
        s * Real.log s * (3 * dimensionOneDelaySum s / 4) :=
      mul_lt_mul_of_pos_left hCurrent hCoeff
    _ = (3 / 4 : Real) *
        (s * Real.log s * dimensionOneDelaySum s) := by ring
    _ < (3 / 4 : Real) * (16 * dimensionOneDelaySum (s - 1)) :=
      mul_lt_mul_of_pos_left hSum (by norm_num)
    _ = 48 * (dimensionOneDelaySum (s - 1) / 4) := by ring
    _ < 48 * QPrevious := mul_lt_mul_of_pos_left hPrevious (by norm_num)

/-- Additional same-sign logarithmic shift for the upper delay function. -/
theorem dimensionOneDelayQPlus_log_shift_lt {s : Real} (hs : 2 <= s) :
    s * Real.log s * dimensionOneDelayQPlus s <
      48 * dimensionOneDelayQPlus (s - 1) :=
  dimensionOneDelayQ_log_shift_lt _ _ hs
    (dimensionOneDelayQPlus_bounds (by linarith)).2
    (dimensionOneDelayQPlus_bounds (by linarith)).1

/-- Additional same-sign logarithmic shift for the lower delay function. -/
theorem dimensionOneDelayQMinus_log_shift_lt {s : Real} (hs : 2 <= s) :
    s * Real.log s * dimensionOneDelayQMinus s <
      48 * dimensionOneDelayQMinus (s - 1) :=
  dimensionOneDelayQ_log_shift_lt _ _ hs
    (dimensionOneDelayQMinus_bounds (by linarith)).2
    (dimensionOneDelayQMinus_bounds (by linarith)).1

/-- Explicit lower half of Eq. (6.4) with upper current and lower shifted
functions. -/
theorem dimensionOneDelayQPlus_to_QMinus_log_shift_lt
    {s : Real} (hs : 2 <= s) :
    s * Real.log s * dimensionOneDelayQPlus s <
      48 * dimensionOneDelayQMinus (s - 1) :=
  dimensionOneDelayQ_log_shift_lt _ _ hs
    (dimensionOneDelayQPlus_bounds (by linarith)).2
    (dimensionOneDelayQMinus_bounds (by linarith)).1

/-- Explicit lower half of Eq. (6.4) with lower current and upper shifted
functions. -/
theorem dimensionOneDelayQMinus_to_QPlus_log_shift_lt
    {s : Real} (hs : 2 <= s) :
    s * Real.log s * dimensionOneDelayQMinus s <
      48 * dimensionOneDelayQPlus (s - 1) :=
  dimensionOneDelayQ_log_shift_lt _ _ hs
    (dimensionOneDelayQMinus_bounds (by linarith)).2
    (dimensionOneDelayQPlus_bounds (by linarith)).1

private theorem nine_mul_dimensionOneDelaySum_three :
    9 * dimensionOneDelaySum 3 = 5 / 4 - Real.log 2 / 2 := by
  unfold dimensionOneDelaySum dimensionOneDelayQPlus
    dimensionOneDelayQMinus
  rw [dimensionOneDelayScaledPlus_eq_half_of_le (s := 3) (by norm_num),
    dimensionOneDelayScaledMinus_first_formula
      (s := 3) (by norm_num) (by norm_num)]
  norm_num
  ring

private theorem dimensionOneDelayRapidWeightedSum_three_lt_one :
    dimensionOneDelayRapidWeightedSum 3 < 1 := by
  have hLogRatio : Real.log ((3 : Real) / 128) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have hExponent : 3 * (dimensionOneDelayLogWeight 3 - 1) < -3 := by
    unfold dimensionOneDelayLogWeight
    linarith
  have hWeightExp : dimensionOneDelayRapidWeight 3 < Real.exp (-3) := by
    unfold dimensionOneDelayRapidWeight
    exact Real.exp_lt_exp.mpr hExponent
  have hExpThree : (4 : Real) < Real.exp 3 := by
    convert Real.add_one_lt_exp (x := (3 : Real)) (by norm_num) using 1;
      norm_num
  have hExpNegThree : Real.exp (-3) < (1 / 4 : Real) := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 4) hExpThree)
  have hWeight : dimensionOneDelayRapidWeight 3 < (1 / 4 : Real) :=
    hWeightExp.trans hExpNegThree
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hSumUpper : 9 * dimensionOneDelaySum 3 < (5 / 4 : Real) := by
    rw [nine_mul_dimensionOneDelaySum_three]
    linarith
  have hSumPos : 0 < 9 * dimensionOneDelaySum 3 :=
    mul_pos (by norm_num) (dimensionOneDelaySum_pos (by norm_num))
  have hProduct : dimensionOneDelayRapidWeight 3 *
      (9 * dimensionOneDelaySum 3) < (1 / 4 : Real) * (5 / 4) :=
    mul_lt_mul hWeight hSumUpper.le hSumPos (by norm_num)
  unfold dimensionOneDelayRapidWeightedSum
  norm_num at hProduct ⊢
  nlinarith

/-- Explicit rapid upper envelope implied by the repaired Lemma 16. -/
theorem dimensionOneDelaySum_lt_rapid_envelope
    {s : Real} (hs : 3 <= s) :
    dimensionOneDelaySum s <
      Real.exp (s * (1 - dimensionOneDelayLogWeight s)) / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hA : dimensionOneDelayRapidWeightedSum s <=
      dimensionOneDelayRapidWeightedSum 3 :=
    dimensionOneDelayRapidWeightedSum_strictAntiOn.antitoneOn
      (show (3 : Real) ∈ Ici 3 by norm_num)
      (show s ∈ Ici 3 by exact hs) hs
  have hALt : dimensionOneDelayRapidWeightedSum s < 1 :=
    hA.trans_lt dimensionOneDelayRapidWeightedSum_three_lt_one
  have hWeightPos : 0 < dimensionOneDelayRapidWeight s :=
    dimensionOneDelayRapidWeight_pos s
  have hScaled : s ^ 2 * dimensionOneDelaySum s <
      (dimensionOneDelayRapidWeight s)⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hWeightPos).mpr
    unfold dimensionOneDelayRapidWeightedSum at hALt
    calc
      (s ^ 2 * dimensionOneDelaySum s) * dimensionOneDelayRapidWeight s =
          dimensionOneDelayRapidWeight s *
            (s ^ 2 * dimensionOneDelaySum s) := by ring
      _ < 1 := hALt
  have hInv : (dimensionOneDelayRapidWeight s)⁻¹ =
      Real.exp (s * (1 - dimensionOneDelayLogWeight s)) := by
    unfold dimensionOneDelayRapidWeight
    rw [<- Real.exp_neg]
    congr 1
    ring
  rw [hInv] at hScaled
  exact (lt_div_iff₀ (sq_pos_of_pos hs0)).mpr (by
    calc
      dimensionOneDelaySum s * s ^ 2 =
          s ^ 2 * dimensionOneDelaySum s := by ring
      _ < Real.exp (s * (1 - dimensionOneDelayLogWeight s)) := hScaled)

/-- Beyond an exact analytic threshold, the scaled delay sum is bounded by
the elementary exponential tail. -/
theorem dimensionOneDelaySum_scaled_lt_exp_neg
    {s : Real} (hs : 128 * Real.exp 2 <= s) :
    s ^ 2 * dimensionOneDelaySum s < Real.exp (-s) := by
  have hExpTwo : 1 <= Real.exp 2 := Real.one_le_exp (by norm_num)
  have hs3 : 3 <= s := by nlinarith
  have hs0 : 0 < s := by linarith
  have hRatio : Real.exp 2 <= s / 128 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 128)]
    nlinarith
  have hLog : 2 <= dimensionOneDelayLogWeight s := by
    unfold dimensionOneDelayLogWeight
    have hMono := Real.strictMonoOn_log.monotoneOn
      (show Real.exp 2 ∈ Ioi 0 by exact Real.exp_pos 2)
      (show s / 128 ∈ Ioi 0 by exact div_pos hs0 (by norm_num)) hRatio
    simpa using hMono
  have hExponent : s * (1 - dimensionOneDelayLogWeight s) <= -s := by
    have h := mul_le_mul_of_nonneg_left (show
      1 - dimensionOneDelayLogWeight s <= -1 by linarith) hs0.le
    linarith
  have hEnvelope := dimensionOneDelaySum_lt_rapid_envelope hs3
  have hScaled : s ^ 2 * dimensionOneDelaySum s <
      Real.exp (s * (1 - dimensionOneDelayLogWeight s)) := by
    have := (lt_div_iff₀ (sq_pos_of_pos hs0)).mp hEnvelope
    nlinarith
  exact hScaled.trans_le (Real.exp_le_exp.mpr hExponent)

private theorem dimensionOneDelayQ_scaled_lt_exp_neg
    (Q : Real -> Real)
    (hBounds : ∀ {t : Real}, 0 < t ->
      Q t < 3 * dimensionOneDelaySum t / 4)
    {s : Real} (hs : 128 * Real.exp 2 <= s) :
    s ^ 2 * Q s < Real.exp (-s) := by
  have hExpTwo : 1 <= Real.exp 2 := Real.one_le_exp (by norm_num)
  have hs0 : 0 < s := by nlinarith
  have hQ : Q s < dimensionOneDelaySum s := by
    have h := hBounds hs0
    have ha := dimensionOneDelaySum_pos hs0
    nlinarith
  have hSq : 0 < s ^ 2 := sq_pos_of_pos hs0
  exact (mul_lt_mul_of_pos_left hQ hSq).trans
    (dimensionOneDelaySum_scaled_lt_exp_neg hs)

theorem dimensionOneDelayQPlus_scaled_lt_exp_neg
    {s : Real} (hs : 128 * Real.exp 2 <= s) :
    s ^ 2 * dimensionOneDelayQPlus s < Real.exp (-s) :=
  dimensionOneDelayQ_scaled_lt_exp_neg dimensionOneDelayQPlus
    (fun h => (dimensionOneDelayQPlus_bounds h).2) hs

theorem dimensionOneDelayQMinus_scaled_lt_exp_neg
    {s : Real} (hs : 128 * Real.exp 2 <= s) :
    s ^ 2 * dimensionOneDelayQMinus s < Real.exp (-s) :=
  dimensionOneDelayQ_scaled_lt_exp_neg dimensionOneDelayQMinus
    (fun h => (dimensionOneDelayQMinus_bounds h).2) hs

end PrimesRestrictedDigits
