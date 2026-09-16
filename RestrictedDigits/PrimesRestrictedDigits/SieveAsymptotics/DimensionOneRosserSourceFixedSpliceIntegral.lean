import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondBoundedIntegral
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceCutoffSlope

/-!
# Cap-free fixed-splice source second integrals

This file replaces the old capped high call in the bounded continuation by the source-cutoff
W6/W7 bridge.
-/

open MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

theorem integral_dimensionOneRosserPlusSecondKernel_div_lt_sourceCutoff
    {L s s0 : Real} (hs : 3 <= s) (hss0 : s < s0)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    (∫ t in s..s0, dimensionOneRosserPlusSecondKernel L t / t) <
      (1 - 1 / s0) ^ (2 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledPlus s := by
  have hL : 0 < L := (Real.exp_pos 1).trans_le hLExp
  by_cases hlarge : Real.exp 5000 + 1 <= s
  · exact integral_dimensionOneRosserPlusSecondKernel_div_lt_of_margin
      hL hlarge hss0 (fun t ht =>
        dimensionOneRosserSourceCutoffSlopeMargin hLExp hlarge hss0
          hsource hgate ht)
  · have hu : Real.exp 5000 + 1 <= dimensionOneRosserSecondSplice := by
      unfold dimensionOneRosserSecondSplice
      linarith [Real.exp_pos (5000 : Real)]
    have hsu : s + 2 <= dimensionOneRosserSecondSplice := by
      unfold dimensionOneRosserSecondSplice
      have hslt : s < Real.exp 5000 + 1 := lt_of_not_ge hlarge
      linarith
    have hu0 : 2 * dimensionOneRosserSecondSplice <= s0 := hsplice
    have hgrowth' : 9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
      simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
    have huS0 : dimensionOneRosserSecondSplice < s0 := by
      have huOne := one_le_dimensionOneRosserSecondSplice
      linarith
    have hs0One : 1 < s0 := by
      have hsPos : 0 < s := by linarith
      linarith
    have hhighRaw :=
      integral_dimensionOneRosserPlusSecondKernel_div_lt_of_margin
        hL hu huS0 (fun t ht =>
          dimensionOneRosserSourceCutoffSlopeMargin hLExp hu huS0
            hsource hgate ht)
    have hhigh :
        (∫ t in dimensionOneRosserSecondSplice..s0,
            dimensionOneRosserPlusSecondKernel L t / t) <
          dimensionOneRosserSecondEndpointFactor s0 *
            dimensionOneRosserArtificialFactor L 0
              dimensionOneRosserSecondSplice *
            dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice := by
      rw [dimensionOneRosserSecondEndpointFactor_eq_rpow hs0One,
        dimensionOneRosserArtificialFactor_eq_rpow hL]
      simp only [dimensionOneRosserArtificialBase, add_zero]
      exact hhighRaw
    have h := dimensionOneRosserIntegralSecondKernelDivLtBoundedOfHigh
      dimensionOneRosserPlusSecondKernel dimensionOneDelayQMinus
      dimensionOneDelayScaledPlus
      dimensionOneRosserPlusSecondKernel_div_eq
      dimensionOneRosserPlusSecondKernel_continuousOn
      dimensionOneDelayQMinus_continuousOn dimensionOneDelayQMinus_pos
      dimensionOneDelayScaledPlus_pos (lower := (3 : Real)) (by norm_num) hs hu
      hsu hu0 hgrowth'
      (integral_dimensionOneDelayPlusKernel_eq_sub hs (by linarith))
      (dimensionOneDelayScaledPlus_two_shift_lt hs hu hsu) hhigh
    rw [dimensionOneRosserSecondEndpointFactor_eq_rpow hs0One,
      dimensionOneRosserArtificialFactor_eq_rpow hL] at h
    simp only [dimensionOneRosserArtificialBase, add_zero] at h
    exact h

theorem integral_dimensionOneRosserMinusSecondKernel_div_lt_sourceCutoff
    {L s s0 : Real} (hs : 2 <= s) (hss0 : s < s0)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    (∫ t in s..s0, dimensionOneRosserMinusSecondKernel L t / t) <
      (1 - 1 / s0) ^ (2 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledMinus s := by
  have hL : 0 < L := (Real.exp_pos 1).trans_le hLExp
  by_cases hlarge : Real.exp 5000 + 1 <= s
  · exact integral_dimensionOneRosserMinusSecondKernel_div_lt_of_margin
      hL hlarge hss0 (fun t ht =>
        dimensionOneRosserSourceCutoffSlopeMargin hLExp hlarge hss0
          hsource hgate ht)
  · have hu : Real.exp 5000 + 1 <= dimensionOneRosserSecondSplice := by
      unfold dimensionOneRosserSecondSplice
      linarith [Real.exp_pos (5000 : Real)]
    have hsu : s + 2 <= dimensionOneRosserSecondSplice := by
      unfold dimensionOneRosserSecondSplice
      have hslt : s < Real.exp 5000 + 1 := lt_of_not_ge hlarge
      linarith
    have hu0 : 2 * dimensionOneRosserSecondSplice <= s0 := hsplice
    have hgrowth' : 9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
      simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
    have huS0 : dimensionOneRosserSecondSplice < s0 := by
      have huOne := one_le_dimensionOneRosserSecondSplice
      linarith
    have hs0One : 1 < s0 := by
      have hsPos : 0 < s := by linarith
      linarith
    have hhighRaw :=
      integral_dimensionOneRosserMinusSecondKernel_div_lt_of_margin
        hL hu huS0 (fun t ht =>
          dimensionOneRosserSourceCutoffSlopeMargin hLExp hu huS0
            hsource hgate ht)
    have hhigh :
        (∫ t in dimensionOneRosserSecondSplice..s0,
            dimensionOneRosserMinusSecondKernel L t / t) <
          dimensionOneRosserSecondEndpointFactor s0 *
            dimensionOneRosserArtificialFactor L 0
              dimensionOneRosserSecondSplice *
            dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice := by
      rw [dimensionOneRosserSecondEndpointFactor_eq_rpow hs0One,
        dimensionOneRosserArtificialFactor_eq_rpow hL]
      simp only [dimensionOneRosserArtificialBase, add_zero]
      exact hhighRaw
    have h := dimensionOneRosserIntegralSecondKernelDivLtBoundedOfHigh
      dimensionOneRosserMinusSecondKernel dimensionOneDelayQPlus
      dimensionOneDelayScaledMinus
      dimensionOneRosserMinusSecondKernel_div_eq
      dimensionOneRosserMinusSecondKernel_continuousOn
      dimensionOneDelayQPlus_continuousOn dimensionOneDelayQPlus_pos
      dimensionOneDelayScaledMinus_pos (lower := (2 : Real)) (by norm_num) hs hu
      hsu hu0 hgrowth'
      (integral_dimensionOneDelayMinusKernel_eq_sub hs (by linarith))
      (dimensionOneDelayScaledMinus_two_shift_lt hs hu hsu) hhigh
    rw [dimensionOneRosserSecondEndpointFactor_eq_rpow hs0One,
      dimensionOneRosserArtificialFactor_eq_rpow hL] at h
    simp only [dimensionOneRosserArtificialBase, add_zero] at h
    exact h

end PrimesRestrictedDigits
