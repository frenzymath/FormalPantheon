import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayImproperTails

/-!
# Finite tails of the dimension-one delay functions

This subtracts the improper-tail identities at finite endpoints and records the resulting
positivity and antitonicity on the natural sign domains.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

/-- The finite upper-delay tail identity, including the seam at three. -/
theorem integral_dimensionOneDelayPlusKernel_eq_sub
    {s u : Real} (hs : 3 <= s) (hsu : s <= u) :
    (∫ t in s..u, t * dimensionOneDelayQMinus (t - 1)) =
      dimensionOneDelayScaledPlus s - dimensionOneDelayScaledPlus u := by
  have hu : 3 <= u := hs.trans hsu
  rw [dimensionOneDelayScaledPlus_eq_integral_Ioi hs,
    dimensionOneDelayScaledPlus_eq_integral_Ioi hu]
  exact (intervalIntegral.integral_Ioi_sub_Ioi
    (dimensionOneDelayPlusTail_integrableOn hs) hsu).symm

/-- The finite lower-delay tail identity, including the seam at two. -/
theorem integral_dimensionOneDelayMinusKernel_eq_sub
    {s u : Real} (hs : 2 <= s) (hsu : s <= u) :
    (∫ t in s..u, t * dimensionOneDelayQPlus (t - 1)) =
      dimensionOneDelayScaledMinus s - dimensionOneDelayScaledMinus u := by
  have hu : 2 <= u := hs.trans hsu
  rw [dimensionOneDelayScaledMinus_eq_integral_Ioi hs,
    dimensionOneDelayScaledMinus_eq_integral_Ioi hu]
  exact (intervalIntegral.integral_Ioi_sub_Ioi
    (dimensionOneDelayMinusTail_integrableOn hs) hsu).symm

/-- Positivity of the scaled upper delay function on the positive half-line. -/
theorem dimensionOneDelayScaledPlus_pos {s : Real} (hs : 0 < s) :
    0 < dimensionOneDelayScaledPlus s := by
  rw [<- sq_mul_dimensionOneDelayQPlus hs.ne']
  exact mul_pos (sq_pos_of_pos hs) (dimensionOneDelayQPlus_pos hs)

/-- Positivity of the scaled lower delay function on the positive half-line. -/
theorem dimensionOneDelayScaledMinus_pos {s : Real} (hs : 0 < s) :
    0 < dimensionOneDelayScaledMinus s := by
  rw [<- sq_mul_dimensionOneDelayQMinus hs.ne']
  exact mul_pos (sq_pos_of_pos hs) (dimensionOneDelayQMinus_pos hs)

private theorem dimensionOneDelayScaledPlus_antitoneOn_Ici_three :
    AntitoneOn dimensionOneDelayScaledPlus (Ici 3) := by
  intro s hs u hu hsu
  change 3 <= s at hs
  change 3 <= u at hu
  have htail := integral_dimensionOneDelayPlusKernel_eq_sub hs hsu
  have hnonneg : 0 <=
      ∫ t in s..u, t * dimensionOneDelayQMinus (t - 1) := by
    apply intervalIntegral.integral_nonneg hsu
    intro t ht
    exact mul_nonneg (by linarith [hs, ht.1])
      (dimensionOneDelayQMinus_pos (by linarith [hs, ht.1])).le
  linarith

/-- The scaled upper delay function is antitone from its constant branch
through its proper tail. -/
theorem dimensionOneDelayScaledPlus_antitoneOn :
    AntitoneOn dimensionOneDelayScaledPlus (Ici 1) := by
  intro x hx y hy hxy
  change 1 <= x at hx
  change 1 <= y at hy
  by_cases hy3 : y <= 3
  · rw [dimensionOneDelayScaledPlus_eq_half_of_le hy3,
      dimensionOneDelayScaledPlus_eq_half_of_le (hxy.trans hy3)]
  have hy3' : 3 <= y := (lt_of_not_ge hy3).le
  by_cases hx3 : 3 <= x
  · exact dimensionOneDelayScaledPlus_antitoneOn_Ici_three
      (show x ∈ Ici (3 : Real) by exact hx3)
      (show y ∈ Ici (3 : Real) by exact hy3') hxy
  have hx3' : x <= 3 := le_of_not_ge hx3
  calc
    dimensionOneDelayScaledPlus y <= dimensionOneDelayScaledPlus 3 :=
      dimensionOneDelayScaledPlus_antitoneOn_Ici_three
        (show (3 : Real) ∈ Ici (3 : Real) by norm_num)
        (show y ∈ Ici (3 : Real) by exact hy3') hy3'
    _ = dimensionOneDelayScaledPlus x := by
      rw [dimensionOneDelayScaledPlus_eq_half_of_le (s := (3 : Real)) le_rfl,
        dimensionOneDelayScaledPlus_eq_half_of_le hx3']

/-- The scaled lower delay function is antitone on its natural tail domain. -/
theorem dimensionOneDelayScaledMinus_antitoneOn :
    AntitoneOn dimensionOneDelayScaledMinus (Ici 2) := by
  intro s hs u hu hsu
  change 2 <= s at hs
  change 2 <= u at hu
  have htail := integral_dimensionOneDelayMinusKernel_eq_sub hs hsu
  have hnonneg : 0 <=
      ∫ t in s..u, t * dimensionOneDelayQPlus (t - 1) := by
    apply intervalIntegral.integral_nonneg hsu
    intro t ht
    exact mul_nonneg (by linarith [hs, ht.1])
      (dimensionOneDelayQPlus_pos (by linarith [hs, ht.1])).le
  linarith

end PrimesRestrictedDigits
