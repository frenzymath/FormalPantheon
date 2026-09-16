import Waring.Analytic.ChenTenAnalyticAverage
import Waring.Analytic.ChenTenShiftCountBridge
import Waring.Analytic.ChenTenSingularIntegralNumerics

/-!
# Source lower bound for Chen's singular integral

This file combines the analytic shift-average estimate with the cumulative
count estimate and the explicit error absorption. The result is the real-part
and norm lower bound used by the positive major-arc estimate.
-/

set_option autoImplicit false

namespace Waring.Analytic

noncomputable section

/-- The source hypotheses give the analytic shift-average approximation at the chosen length. -/
theorem chenTen_analytic_average_source
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real)) :
    ‖(scratchShiftSquareCount P N (chenTenAverageLength P) : Complex) -
        chenTenSingularIntegral P N *
          (chenTenAverageLength P : Complex) ^ 2‖ ≤
      3 * (10 : Real) ^ 4 * (P : Real) ^ (49 / 5 : Real) *
        (chenTenAverageLength P : Real) ^ 2 := by
  have hroom := chenTenAverageLength_room hPbig hNlower
  have hMN : 2 * chenTenAverageLength P ≤ N := by omega
  rw [scratchShiftSquareCount_cast_eq_fin_sum]
  exact chenTen_analytic_average_eq35 hPbig
    (two_le_chenTenAverageLength hPbig) hMN
    (twice_chenTenAverageLength_le_rpow P)
    (rpow_le_four_mul_chenTenAverageLength hPbig)

/-- The analytic and cumulative estimates give the explicit real-part
singular-integral lower bound. -/
theorem chenTen_singularIntegral_re_lower_source
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real))
    (hNupper : N ≤ (P + 1) ^ 5) :
    (2999 / 1000 : Real) * chenTenT15 * (N : Real) ^ 2 ≤
      (chenTenSingularIntegral P N).re := by
  have hM := chenTenAverageLength_pos hPbig
  have hanalytic := chenTen_analytic_average_source hPbig hNlower
  have hcumulative :=
    chenTen_shiftSquareCount_cumulative_error_source hPbig hNlower hNupper
  have hlower := scratch_singularIntegral_re_lower_of_shift_average
    (mainTerm := 3 * chenTenT15 * (N : Real) ^ 2)
    (analyticError := 3 * (10 : Real) ^ 4 *
      (P : Real) ^ (49 / 5 : Real))
    (countError := 3000 * chenTenT15 * (N : Real) ^ 2 *
      (P : Real) ^ (-1 / 5 : Real))
    hM hanalytic hcumulative
  have herrors := chenTen_source_errors_absorbed hPbig hNlower
  linarith

/-- The real-part estimate yields the corresponding norm lower bound for the singular integral. -/
theorem chenTen_singularIntegral_norm_lower_source
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real))
    (hNupper : N ≤ (P + 1) ^ 5) :
    (2999 / 1000 : Real) * chenTenT15 * (N : Real) ^ 2 ≤
      ‖chenTenSingularIntegral P N‖ := by
  have hre := chenTen_singularIntegral_re_lower_source
    hPbig hNlower hNupper
  have hT : (0 : Real) ≤ chenTenT15 :=
    (by norm_num : (0 : Real) ≤ 1 / 100).trans
      one_hundredth_le_chenTenT15
  have hmain :
      0 ≤ (2999 / 1000 : Real) * chenTenT15 * (N : Real) ^ 2 := by
    positivity
  have hR : 0 ≤ (chenTenSingularIntegral P N).re := hmain.trans hre
  rw [scratch_norm_chenTenSingularIntegral_eq_re_of_nonneg hR]
  exact hre

end

end Waring.Analytic
