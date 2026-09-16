import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondBoundedWeight
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceShiftedLayer

/-!
# Cap-free fixed-splice source second weights

This file glues the bounded second-kernel regularity to W8 at the fixed splice under the
literal source cutoff.
-/

open Set

namespace PrimesRestrictedDigits

/-- The source assumptions place twice the fixed splice below a positive
current cutoff. -/
theorem dimensionOneRosserSourceSplice_twice_le
    {L s s0 : Real} (hs : 2 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    2 * dimensionOneRosserSecondSplice <= s0 := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hU : 1 <= Real.log L :=
    (Real.le_log_iff_exp_le hLPos).2 hLExp
  have hUlarge : 124800 <= Real.log L := by
    have hV : 0 <= Real.log (Real.log L) := Real.log_nonneg hU
    linarith
  have huOne : 1 <= dimensionOneRosserSecondSplice :=
    one_le_dimensionOneRosserSecondSplice
  have huPos : 0 < dimensionOneRosserSecondSplice :=
    zero_lt_one.trans_le huOne
  have hUcube : (124800 : Real) ^ 3 <= (Real.log L) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hUlarge 3
  have hcoef : (2 : Real) ^ 50 <= 9792 * (Real.log L) ^ 3 := by
    norm_num at hUcube ⊢
    nlinarith
  have huPow : 0 <= dimensionOneRosserSecondSplice ^ 50 :=
    pow_nonneg huPos.le 50
  have hfirst :
      (2 : Real) ^ 50 * dimensionOneRosserSecondSplice ^ 50 <=
        9792 * (Real.log L) ^ 3 * dimensionOneRosserSecondSplice ^ 50 :=
    mul_le_mul_of_nonneg_right hcoef huPow
  have huSq : 1 <= dimensionOneRosserSecondSplice ^ 2 := by
    nlinarith [sq_nonneg (dimensionOneRosserSecondSplice - 1)]
  have hu50le52 : dimensionOneRosserSecondSplice ^ 50 <=
      dimensionOneRosserSecondSplice ^ 52 := by
    calc
      dimensionOneRosserSecondSplice ^ 50 =
          dimensionOneRosserSecondSplice ^ 50 * 1 := by ring
      _ <= dimensionOneRosserSecondSplice ^ 50 *
          dimensionOneRosserSecondSplice ^ 2 :=
        mul_le_mul_of_nonneg_left huSq (pow_nonneg huPos.le 50)
      _ = dimensionOneRosserSecondSplice ^ 52 := by ring
  have hsecond :
      9792 * (Real.log L) ^ 3 * dimensionOneRosserSecondSplice ^ 50 <=
        9792 * (Real.log L) ^ 3 * dimensionOneRosserSecondSplice ^ 52 :=
    mul_le_mul_of_nonneg_left hu50le52 (by positivity)
  have hgrowth' : 9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
    simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
  have hpow : (2 * dimensionOneRosserSecondSplice) ^ 50 <= s0 ^ 50 := by
    calc
      (2 * dimensionOneRosserSecondSplice) ^ 50 =
          (2 : Real) ^ 50 * dimensionOneRosserSecondSplice ^ 50 := by ring
      _ <= 9792 * (Real.log L) ^ 3 *
          dimensionOneRosserSecondSplice ^ 52 := hfirst.trans hsecond
      _ <= L * (Real.log L) ^ 3 := by
        have hU3 : 0 <= (Real.log L) ^ 3 := by positivity
        nlinarith [hgrowth']
      _ = s0 ^ 50 := hsource.symm
  have hs0Pos : 0 < s0 := by linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) hs0Pos.le hpow

/-- Full source-cutoff antitonicity of the target-plus second kernel. -/
theorem dimensionOneRosserPlusSecondKernel_antitoneOn_sourceCutoff
    {L s0 : Real} (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    AntitoneOn (dimensionOneRosserPlusSecondKernel L) (Icc 3 s0) := by
  have hu : Real.exp 5000 + 1 <= dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserSecondSplice
    linarith [Real.exp_pos (5000 : Real)]
  have hu3 : 3 <= dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserSecondSplice
    nlinarith [Real.exp_pos (5000 : Real)]
  have hlocalGrowth : 9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
    simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
  have hlow :=
    dimensionOneRosserPlusSecondKernel_antitoneOn_bounded hu3 hlocalGrowth
  by_cases huS0 : dimensionOneRosserSecondSplice < s0
  · apply dimensionOneRosserAntitoneOn_Icc_of_split hu3 huS0.le hlow
    exact dimensionOneRosserSourcePlusSecondKernel_antitoneOn
      hLExp hu huS0 hsource hgate
  · exact hlow.mono (by
      intro t ht
      exact ⟨ht.1, ht.2.trans (le_of_not_gt huS0)⟩)

/-- Full source-cutoff antitonicity of the target-minus second kernel. -/
theorem dimensionOneRosserMinusSecondKernel_antitoneOn_sourceCutoff
    {L s0 : Real} (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    AntitoneOn (dimensionOneRosserMinusSecondKernel L) (Icc 2 s0) := by
  have hu : Real.exp 5000 + 1 <= dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserSecondSplice
    linarith [Real.exp_pos (5000 : Real)]
  have hu2 : 2 <= dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserSecondSplice
    nlinarith [Real.exp_pos (5000 : Real)]
  have hlocalGrowth : 9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
    simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
  have hlow :=
    dimensionOneRosserMinusSecondKernel_antitoneOn_bounded hu2 hlocalGrowth
  by_cases huS0 : dimensionOneRosserSecondSplice < s0
  · apply dimensionOneRosserAntitoneOn_Icc_of_split hu2 huS0.le hlow
    exact dimensionOneRosserSourceMinusSecondKernel_antitoneOn
      hLExp hu huS0 hsource hgate
  · exact hlow.mono (by
      intro t ht
      exact ⟨ht.1, ht.2.trans (le_of_not_gt huS0)⟩)

/-- Full source-domain regularity of the target-plus composed second weight. -/
theorem dimensionOneRosserPlusSecondWeight_properties_sourceCutoff
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0)
    (hsource : s0 ^ 50 = Real.log level *
      (Real.log (Real.log level)) ^ 3)
    (hLExp : Real.exp 1 <= Real.log level)
    (hgate : 124800 + 14400 * Real.log (Real.log (Real.log level)) <=
      Real.log (Real.log level))
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
        0 <= dimensionOneRosserPlusSecondWeight level x) ∧
      ContinuousOn (dimensionOneRosserPlusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn (dimensionOneRosserPlusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) := by
  have hanti :=
    (dimensionOneRosserPlusSecondKernel_antitoneOn_sourceCutoff
      (by simpa using hsource) hLExp (by simpa using hgate) hgrowth).mono
      (show Icc s s0 ⊆ Icc (3 : Real) s0 by
        intro t ht
        exact ⟨hsLower.trans ht.1, ht.2⟩)
  change (∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserPlusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) ∧
    ContinuousOn
      (fun x => dimensionOneRosserPlusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) (Icc (level ^ (1 / s0)) z) ∧
    MonotoneOn
      (fun x => dimensionOneRosserPlusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) (Icc (level ^ (1 / s0)) z)
  exact dimensionOneRosserSecondWeight_properties_of_antitoneOn
    dimensionOneRosserPlusSecondKernel
    dimensionOneRosserPlusSecondKernel_pos
    dimensionOneRosserPlusSecondKernel_continuousOn hlevel hz hs
    (by linarith) hss0 hanti

/-- Full source-domain regularity of the target-minus composed second weight. -/
theorem dimensionOneRosserMinusSecondWeight_properties_sourceCutoff
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0)
    (hsource : s0 ^ 50 = Real.log level *
      (Real.log (Real.log level)) ^ 3)
    (hLExp : Real.exp 1 <= Real.log level)
    (hgate : 124800 + 14400 * Real.log (Real.log (Real.log level)) <=
      Real.log (Real.log level))
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
        0 <= dimensionOneRosserMinusSecondWeight level x) ∧
      ContinuousOn (dimensionOneRosserMinusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn (dimensionOneRosserMinusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) := by
  have hanti :=
    (dimensionOneRosserMinusSecondKernel_antitoneOn_sourceCutoff
      (by simpa using hsource) hLExp (by simpa using hgate) hgrowth).mono
      (show Icc s s0 ⊆ Icc (2 : Real) s0 by
        intro t ht
        exact ⟨hsLower.trans ht.1, ht.2⟩)
  change (∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserMinusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) ∧
    ContinuousOn
      (fun x => dimensionOneRosserMinusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) (Icc (level ^ (1 / s0)) z) ∧
    MonotoneOn
      (fun x => dimensionOneRosserMinusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) (Icc (level ^ (1 / s0)) z)
  exact dimensionOneRosserSecondWeight_properties_of_antitoneOn
    dimensionOneRosserMinusSecondKernel
    dimensionOneRosserMinusSecondKernel_pos
    dimensionOneRosserMinusSecondKernel_continuousOn hlevel hz hs
    (by linarith) hss0 hanti

end PrimesRestrictedDigits
