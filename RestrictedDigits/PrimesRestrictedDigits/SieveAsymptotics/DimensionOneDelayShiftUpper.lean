import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayMonotonicity

/-!
# Upper shifted comparisons for the dimension-one delay functions

This proves Iwaniec's Lemma 15 with explicit constants, including the compact range suppressed
in the source, and transfers it to the upper half of Eq. (6.4). See
`IWANIEC-ROSSER-SIEVE-1980`, printed pp. 189 and 191.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

/-- Keeping the left half of the averaging window gives an explicit
half-step comparison. -/
theorem dimensionOneDelaySum_half_shift_le {s : Real} (hs : 3 <= s) :
    dimensionOneDelaySum (s - 1 / 2) <=
      2 * s * dimensionOneDelaySum s := by
  have hLeftMid : s - 1 <= s - 1 / 2 := by linarith
  have hMidRight : s - 1 / 2 <= s := by norm_num
  have hMid0 : 0 < s - 1 / 2 := by linarith
  have hGPos : 0 < dimensionOneDelayConjugateWeight s :=
    dimensionOneDelayConjugateWeight_pos (by linarith)
  have hWindowPositive : Icc (s - 1) s ⊆ Ioi (0 : Real) := by
    intro x hx
    change 0 < x
    linarith [hx.1]
  have hGShiftContinuous : Continuous (fun x : Real =>
      dimensionOneDelayConjugateWeight (x + 1)) :=
    dimensionOneDelayConjugateWeight_continuous.comp
      (continuous_id.add continuous_const)
  have hFContinuous : ContinuousOn (fun x : Real =>
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1))
      (Icc (s - 1) s) :=
    (dimensionOneDelaySum_continuousOn.mono hWindowPositive).mul
      hGShiftContinuous.continuousOn
  have hFInt : IntervalIntegrable (fun x : Real =>
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1))
      volume (s - 1) s :=
    hFContinuous.intervalIntegrable_of_Icc (by linarith)
  have hFFirstInt : IntervalIntegrable (fun x : Real =>
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1))
      volume (s - 1) (s - 1 / 2) :=
    (hFContinuous.mono (Icc_subset_Icc_right hMidRight))
      |>.intervalIntegrable_of_Icc hLeftMid
  have hPointwise : ∀ x ∈ Icc (s - 1) (s - 1 / 2),
      dimensionOneDelaySum (s - 1 / 2) *
          dimensionOneDelayConjugateWeight s <=
        dimensionOneDelaySum x *
          dimensionOneDelayConjugateWeight (x + 1) := by
    intro x hx
    have hx0 : x ∈ Ioi (0 : Real) := by
      change 0 < x
      linarith [hx.1]
    have hSum : dimensionOneDelaySum (s - 1 / 2) <=
        dimensionOneDelaySum x :=
      dimensionOneDelaySum_strictAntiOn.antitoneOn hx0 hMid0 hx.2
    have hWeight : dimensionOneDelayConjugateWeight s <=
        dimensionOneDelayConjugateWeight (x + 1) :=
      dimensionOneDelayConjugateWeight_monoOn
        (by change 1 <= s; linarith)
        (by change 1 <= x + 1; linarith [hx.1])
        (by linarith [hx.1])
    exact mul_le_mul hSum hWeight hGPos.le
      (dimensionOneDelaySum_pos hx0).le
  have hFirstLower :
      (dimensionOneDelaySum (s - 1 / 2) / 2) *
          dimensionOneDelayConjugateWeight s <=
        ∫ x in s - 1..s - 1 / 2,
          dimensionOneDelaySum x *
            dimensionOneDelayConjugateWeight (x + 1) := by
    have hIntegral := intervalIntegral.integral_mono_on
      (f := fun _ : Real =>
        dimensionOneDelaySum (s - 1 / 2) *
          dimensionOneDelayConjugateWeight s)
      (g := fun x : Real =>
        dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1))
      hLeftMid intervalIntegrable_const hFFirstInt hPointwise
    calc
      (dimensionOneDelaySum (s - 1 / 2) / 2) *
          dimensionOneDelayConjugateWeight s =
          ∫ _x in s - 1..s - 1 / 2,
            dimensionOneDelaySum (s - 1 / 2) *
              dimensionOneDelayConjugateWeight s := by
            rw [intervalIntegral.integral_const]
            ring
      _ <= ∫ x in s - 1..s - 1 / 2,
          dimensionOneDelaySum x *
            dimensionOneDelayConjugateWeight (x + 1) := hIntegral
  have hFirstFull :
      (∫ x in s - 1..s - 1 / 2,
        dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1)) <=
      ∫ x in s - 1..s,
        dimensionOneDelaySum x *
          dimensionOneDelayConjugateWeight (x + 1) := by
    apply intervalIntegral.integral_mono_interval le_rfl hLeftMid hMidRight
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
        fun x hx => by
          have hx0 : 0 < x := by linarith [hx.1]
          have hxG : (2 : Real) <= x + 1 := by linarith [hx.1]
          exact mul_nonneg (dimensionOneDelaySum_pos hx0).le
            (dimensionOneDelayConjugateWeight_pos hxG).le
    · exact hFInt
  have hWeighted :
      (dimensionOneDelaySum (s - 1 / 2) / 2) *
          dimensionOneDelayConjugateWeight s <=
        (s * dimensionOneDelaySum s) *
          dimensionOneDelayConjugateWeight s := by
    calc
      (dimensionOneDelaySum (s - 1 / 2) / 2) *
          dimensionOneDelayConjugateWeight s <=
          ∫ x in s - 1..s - 1 / 2,
            dimensionOneDelaySum x *
              dimensionOneDelayConjugateWeight (x + 1) := hFirstLower
      _ <= ∫ x in s - 1..s,
          dimensionOneDelaySum x *
            dimensionOneDelayConjugateWeight (x + 1) := hFirstFull
      _ = (s * dimensionOneDelaySum s) *
          dimensionOneDelayConjugateWeight s := by
            rw [<- dimensionOneDelaySum_averaging hs]
  have hHalf : dimensionOneDelaySum (s - 1 / 2) / 2 <=
      s * dimensionOneDelaySum s :=
    le_of_mul_le_mul_right hWeighted hGPos
  linarith

/-- Repeating the half-step estimate gives the explicit high-range form of
Iwaniec's Lemma 15. -/
theorem dimensionOneDelaySum_shift_le_of_seven_halves_le
    {s : Real} (hs : 7 / 2 <= s) :
    dimensionOneDelaySum (s - 1) <=
      4 * s ^ 2 * dimensionOneDelaySum s := by
  have hFirst := dimensionOneDelaySum_half_shift_le
    (s := s - 1 / 2) (by linarith)
  rw [show (s - 1 / 2) - 1 / 2 = s - 1 by ring] at hFirst
  have hSecond := dimensionOneDelaySum_half_shift_le
    (s := s) (by linarith)
  have hCoeff : 0 <= 2 * (s - 1 / 2) := by linarith
  have hs0 : 0 < s := by linarith
  have hsa : 0 <= s * dimensionOneDelaySum s :=
    mul_nonneg hs0.le (dimensionOneDelaySum_pos hs0).le
  calc
    dimensionOneDelaySum (s - 1) <=
        2 * (s - 1 / 2) * dimensionOneDelaySum (s - 1 / 2) := hFirst
    _ <= 2 * (s - 1 / 2) *
        (2 * s * dimensionOneDelaySum s) :=
      mul_le_mul_of_nonneg_left hSecond hCoeff
    _ = 4 * s ^ 2 * dimensionOneDelaySum s -
        2 * (s * dimensionOneDelaySum s) := by ring
    _ <= 4 * s ^ 2 * dimensionOneDelaySum s :=
      sub_le_self _ (mul_nonneg (by norm_num) hsa)

private theorem dimensionOneDelaySum_one :
    dimensionOneDelaySum 1 = 3 / 2 := by
  unfold dimensionOneDelaySum dimensionOneDelayQPlus
    dimensionOneDelayQMinus
  rw [dimensionOneDelayScaledPlus_eq_half_of_le (s := 1) (by norm_num),
    dimensionOneDelayScaledMinus_eq_one_of_le (s := 1) (by norm_num)]
  norm_num

private theorem one_twelfth_lt_dimensionOneDelaySum_three :
    (1 / 12 : Real) < dimensionOneDelaySum 3 := by
  have hLogTwo : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : Real)) (by norm_num)
      (by norm_num)
    norm_num at h
    exact h
  have hMinusFormula := dimensionOneDelayScaledMinus_first_formula
    (s := (3 : Real)) (by norm_num) (by norm_num)
  have hMinus : (1 / 36 : Real) < dimensionOneDelayQMinus 3 := by
    unfold dimensionOneDelayQMinus
    rw [hMinusFormula]
    norm_num
    linarith
  have hPlus : dimensionOneDelayQPlus 3 = 1 / 18 := by
    unfold dimensionOneDelayQPlus
    rw [dimensionOneDelayScaledPlus_eq_half_of_le (s := 3) (by norm_num)]
    norm_num
  unfold dimensionOneDelaySum
  rw [hPlus]
  linarith

private theorem one_eighty_four_lt_dimensionOneDelaySum_seven_halves :
    (1 / 84 : Real) < dimensionOneDelaySum (7 / 2) := by
  have hShift := dimensionOneDelaySum_half_shift_le
    (s := (7 / 2 : Real)) (by norm_num)
  norm_num at hShift
  linarith [one_twelfth_lt_dimensionOneDelaySum_three]

/-- Explicit source-domain form of Iwaniec's Lemma 15. The constant `32`
also covers the compact range omitted from the printed proof. -/
theorem dimensionOneDelaySum_shift_le {s : Real} (hs : 2 <= s) :
    dimensionOneDelaySum (s - 1) <=
      32 * s ^ 2 * dimensionOneDelaySum s := by
  by_cases hLarge : 7 / 2 <= s
  · have hFour := dimensionOneDelaySum_shift_le_of_seven_halves_le hLarge
    have hs0 : 0 < s := by linarith
    have hProduct : 0 <= s ^ 2 * dimensionOneDelaySum s :=
      mul_nonneg (sq_nonneg s) (dimensionOneDelaySum_pos hs0).le
    calc
      dimensionOneDelaySum (s - 1) <=
          4 * s ^ 2 * dimensionOneDelaySum s := hFour
      _ = 4 * (s ^ 2 * dimensionOneDelaySum s) := by ring
      _ <= 32 * (s ^ 2 * dimensionOneDelaySum s) :=
        mul_le_mul_of_nonneg_right (by norm_num) hProduct
      _ = 32 * s ^ 2 * dimensionOneDelaySum s := by ring
  · have hUpper : s <= 7 / 2 := (lt_of_not_ge hLarge).le
    have hs0 : 0 < s := by linarith
    have hShiftOne : dimensionOneDelaySum (s - 1) <=
        dimensionOneDelaySum 1 :=
      dimensionOneDelaySum_strictAntiOn.antitoneOn
        (by norm_num)
        (by change 0 < s - 1; linarith)
        (by linarith)
    rw [dimensionOneDelaySum_one] at hShiftOne
    have hLowerS : (1 / 84 : Real) < dimensionOneDelaySum s := by
      have hMono : dimensionOneDelaySum (7 / 2) <=
          dimensionOneDelaySum s :=
        dimensionOneDelaySum_strictAntiOn.antitoneOn
          (by change 0 < s; exact hs0)
          (by change 0 < (7 / 2 : Real); norm_num)
          hUpper
      linarith [one_eighty_four_lt_dimensionOneDelaySum_seven_halves]
    have hSq : (4 : Real) <= s ^ 2 := by
      nlinarith [sq_nonneg (s - 2)]
    have hProduct : (1 / 21 : Real) <
        s ^ 2 * dimensionOneDelaySum s := by
      calc
        (1 / 21 : Real) = 4 * (1 / 84 : Real) := by norm_num
        _ < 4 * dimensionOneDelaySum s :=
          mul_lt_mul_of_pos_left hLowerS (by norm_num)
        _ <= s ^ 2 * dimensionOneDelaySum s :=
          mul_le_mul_of_nonneg_right hSq
            (dimensionOneDelaySum_pos hs0).le
    nlinarith

private theorem dimensionOneDelayQ_shift_le
    (Q : Real -> Real)
    (hBounds : ∀ {t : Real}, 0 < t ->
      dimensionOneDelaySum t / 4 < Q t ∧
        Q t < 3 * dimensionOneDelaySum t / 4)
    {s : Real} (hs : 2 <= s) :
    Q (s - 1) <= 96 * s ^ 2 * Q s := by
  have hSum := dimensionOneDelaySum_shift_le hs
  have hUpper := (hBounds (by linarith : 0 < s - 1)).2
  have hLower := (hBounds (by linarith : 0 < s)).1
  calc
    Q (s - 1) <= 3 * dimensionOneDelaySum (s - 1) / 4 := hUpper.le
    _ = (3 / 4 : Real) * dimensionOneDelaySum (s - 1) := by ring
    _ <= (3 / 4 : Real) *
        (32 * s ^ 2 * dimensionOneDelaySum s) :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ = 24 * s ^ 2 * dimensionOneDelaySum s := by ring
    _ = (96 * s ^ 2) * (dimensionOneDelaySum s / 4) := by ring
    _ <= (96 * s ^ 2) * Q s :=
      mul_le_mul_of_nonneg_left hLower.le
        (mul_nonneg (by norm_num) (sq_nonneg s))
    _ = 96 * s ^ 2 * Q s := by ring

/-- Explicit upper shifted comparison for the upper dimension-one delay
function, specializing the upper half of Iwaniec's Eq. (6.4). -/
theorem dimensionOneDelayQPlus_shift_le {s : Real} (hs : 2 <= s) :
    dimensionOneDelayQPlus (s - 1) <=
      96 * s ^ 2 * dimensionOneDelayQPlus s :=
  dimensionOneDelayQ_shift_le dimensionOneDelayQPlus
    (fun h => dimensionOneDelayQPlus_bounds h) hs

/-- Explicit upper shifted comparison for the lower dimension-one delay
function, specializing the upper half of Iwaniec's Eq. (6.4). -/
theorem dimensionOneDelayQMinus_shift_le {s : Real} (hs : 2 <= s) :
    dimensionOneDelayQMinus (s - 1) <=
      96 * s ^ 2 * dimensionOneDelayQMinus s :=
  dimensionOneDelayQ_shift_le dimensionOneDelayQMinus
    (fun h => dimensionOneDelayQMinus_bounds h) hs

end PrimesRestrictedDigits
