import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceCutoffSlope
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceFixedSpliceWeight
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedScalars
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayFiniteTails

/-!
# Source epsilon-zero profile endpoint comparison

This module compares the source endpoint profile with the current profile on both fixed-splice
branches. It is the profile bridge needed after the three-term ledger, not the final joint Eq.
(8.14) reserve.
-/

open Set

namespace PrimesRestrictedDigits

/- The literal source cutoff also implies the useful scalar `s0 <= L`. -/
theorem dimensionOneRosserSourceCutoff_s0_le_log
    {L s0 : Real} (_hs0 : 1 <= s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    s0 <= L := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hLOne : 1 <= L := by
    exact (Real.one_le_exp (by norm_num : (0 : Real) <= 1)).trans hLExp
  have hlogCube := dimensionOneRosserSourceGate_log_cube_le hLExp hgate
  have hsourceLe : s0 ^ 50 <= L ^ 2 := by
    rw [hsource]
    have hLnonneg : 0 <= L := hLPos.le
    nlinarith [hlogCube]
  have hLpow48 : 1 <= L ^ 48 := one_le_pow₀ hLOne
  have hLpow : L ^ 2 <= L ^ 50 := by
    calc
      L ^ 2 = L ^ 2 * 1 := by ring
      _ <= L ^ 2 * L ^ 48 :=
        mul_le_mul_of_nonneg_left hLpow48 (by positivity)
      _ = L ^ 50 := by ring
  have hpow : s0 ^ 50 <= L ^ 50 := hsourceLe.trans hLpow
  exact le_of_pow_le_pow_left₀ (by norm_num) (by linarith) hpow

private theorem sourceProfilePlus_strictAntiOn
    {L a b : Real} (hL : 0 < L) (ha : 3 <= a)
    (haLarge : Real.exp 5000 + 1 <= a) (hab : a < b)
    (hsource : b ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    StrictAntiOn (dimensionOneRosserPlusArtificialAux L 0) (Icc a b) := by
  apply dimensionOneRosserPlusArtificialAux_strictAntiOn_of_slope hL
    ha hab.le
  intro t ht
  have hm := dimensionOneRosserSourceCutoffSlopeMargin
    (L := L) (s := a) (s0 := b) (t := t) hLExp haLarge hab hsource hgate
      ⟨ht.1.le, ht.2.le⟩
  have hbase : 0 < dimensionOneRosserArtificialBase L 0 t :=
    dimensionOneRosserArtificialBase_pos hL
  have hinv : 0 <= (dimensionOneRosserArtificialBase L 0 t)⁻¹ :=
    inv_nonneg.mpr hbase.le
  have htOne : 1 <= t := by
    have : 0 < a := by linarith
    linarith [ht.1]
  have hlog : 0 <= Real.log t := Real.log_nonneg htOne
  have hfac : 1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹ <= 1 := by
    linarith
  have hweak := mul_le_mul_of_nonneg_right hfac hlog
  nlinarith [hm, hweak]

private theorem sourceProfileMinus_strictAntiOn
    {L a b : Real} (hL : 0 < L) (ha : 2 <= a)
    (haLarge : Real.exp 5000 + 1 <= a) (hab : a < b)
    (hsource : b ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    StrictAntiOn (dimensionOneRosserMinusArtificialAux L 0) (Icc a b) := by
  apply dimensionOneRosserMinusArtificialAux_strictAntiOn_of_slope hL
    ha hab.le
  intro t ht
  have hm := dimensionOneRosserSourceCutoffSlopeMargin
    (L := L) (s := a) (s0 := b) (t := t) hLExp haLarge hab hsource hgate
      ⟨ht.1.le, ht.2.le⟩
  have hbase : 0 < dimensionOneRosserArtificialBase L 0 t :=
    dimensionOneRosserArtificialBase_pos hL
  have hinv : 0 <= (dimensionOneRosserArtificialBase L 0 t)⁻¹ :=
    inv_nonneg.mpr hbase.le
  have htOne : 1 <= t := by
    have : 0 < a := by linarith
    linarith [ht.1]
  have hlog : 0 <= Real.log t := Real.log_nonneg htOne
  have hfac : 1 - (dimensionOneRosserArtificialBase L 0 t)⁻¹ <= 1 := by
    linarith
  have hweak := mul_le_mul_of_nonneg_right hfac hlog
  nlinarith [hm, hweak]

theorem dimensionOneRosserPlusArtificialAux_sourceEndpoint_le_two
    {L s s0 : Real} (hs : 3 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    dimensionOneRosserPlusArtificialAux L 0 s0 <=
      2 * dimensionOneRosserPlusArtificialAux L 0 s := by
  have hL : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hU : Real.exp 5000 + 1 <= dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserSecondSplice
    linarith [Real.exp_pos (5000 : Real)]
  have hU3 : 3 <= dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserSecondSplice
    nlinarith [Real.exp_pos (5000 : Real)]
  have hU1 : 1 <= dimensionOneRosserSecondSplice :=
    one_le_dimensionOneRosserSecondSplice
  have hUpos : 0 < dimensionOneRosserSecondSplice :=
    zero_lt_one.trans_le hU1
  have hgrowth' : 9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
    simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
  have hsplice := dimensionOneRosserSourceSplice_twice_le (by linarith : 2 <= s)
    hss0 hsource hLExp hgate hgrowth
  have hUs0 : dimensionOneRosserSecondSplice < s0 := by linarith
  have hantiU := sourceProfilePlus_strictAntiOn hL hU3 hU hUs0
    hsource hLExp hgate
  have hfactorU := dimensionOneRosserArtificialFactor_zero_le_one_add
    hU1 (by positivity : 0 <= dimensionOneRosserSecondSplice)
      le_rfl hgrowth'
  have hfactorU2 : dimensionOneRosserArtificialFactor L 0
      dimensionOneRosserSecondSplice <= 2 := by
    have hden : 0 < 12 * dimensionOneRosserSecondSplice := by positivity
    have hone : 1 / (12 * dimensionOneRosserSecondSplice) <= (1 : Real) := by
      exact (div_le_one hden).2 (by linarith)
    linarith
  have hqUpos : 0 < dimensionOneDelayScaledPlus
      dimensionOneRosserSecondSplice :=
    dimensionOneDelayScaledPlus_pos hUpos
  have hqSpos : 0 < dimensionOneDelayScaledPlus s :=
    dimensionOneDelayScaledPlus_pos (by linarith : 0 < s)
  have hA_s : 1 <= dimensionOneRosserArtificialFactor L 0 s :=
    one_le_dimensionOneRosserArtificialFactor_zero hL (by linarith)
  by_cases hsU : s <= dimensionOneRosserSecondSplice
  · have hqmono := dimensionOneDelayScaledPlus_antitoneOn
      (show s ∈ Ici (1 : Real) by change 1 <= s; linarith)
      (show dimensionOneRosserSecondSplice ∈ Ici (1 : Real) by exact hU1)
      hsU
    have hauxU : dimensionOneRosserPlusArtificialAux L 0 s0 <
        dimensionOneRosserPlusArtificialAux L 0 dimensionOneRosserSecondSplice :=
      hantiU ⟨le_rfl, hUs0.le⟩ ⟨hUs0.le, le_rfl⟩ hUs0
    have hauxUle : dimensionOneRosserPlusArtificialAux L 0
        dimensionOneRosserSecondSplice <=
        2 * dimensionOneRosserPlusArtificialAux L 0 s := by
      unfold dimensionOneRosserPlusArtificialAux at *
      have h1 := mul_le_mul_of_nonneg_right hfactorU2 hqUpos.le
      have h2 := mul_le_mul_of_nonneg_left hqmono
        (mul_nonneg (le_trans (by norm_num) hA_s) hqSpos.le)
      have h3 := mul_le_mul_of_nonneg_right hA_s hqSpos.le
      nlinarith [h1, h2, h3]
    exact hauxU.le.trans hauxUle
  · have hsU' : dimensionOneRosserSecondSplice < s := lt_of_not_ge hsU
    have hsLarge : Real.exp 5000 + 1 <= s := hU.trans hsU'.le
    have hantiS := sourceProfilePlus_strictAntiOn hL hs hsLarge hss0
      hsource hLExp hgate
    have hauxSpos : 0 < dimensionOneRosserPlusArtificialAux L 0 s :=
      dimensionOneRosserPlusArtificialAux_pos hL (by linarith)
    have hauxSle := (hantiS ⟨le_rfl, hss0.le⟩
      ⟨hss0.le, le_rfl⟩ hss0).le
    nlinarith

theorem dimensionOneRosserMinusArtificialAux_sourceEndpoint_le_two
    {L s s0 : Real} (hs : 2 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    dimensionOneRosserMinusArtificialAux L 0 s0 <=
      2 * dimensionOneRosserMinusArtificialAux L 0 s := by
  have hL : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hU : Real.exp 5000 + 1 <= dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserSecondSplice
    linarith [Real.exp_pos (5000 : Real)]
  have hU2 : 2 <= dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserSecondSplice
    nlinarith [Real.exp_pos (5000 : Real)]
  have hU1 : 1 <= dimensionOneRosserSecondSplice :=
    one_le_dimensionOneRosserSecondSplice
  have hUpos : 0 < dimensionOneRosserSecondSplice :=
    zero_lt_one.trans_le hU1
  have hgrowth' : 9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
    simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
  have hsplice := dimensionOneRosserSourceSplice_twice_le (by linarith : 2 <= s)
    hss0 hsource hLExp hgate hgrowth
  have hUs0 : dimensionOneRosserSecondSplice < s0 := by linarith
  have hantiU := sourceProfileMinus_strictAntiOn hL hU2 hU hUs0
    hsource hLExp hgate
  have hfactorU := dimensionOneRosserArtificialFactor_zero_le_one_add
    hU1 (by positivity : 0 <= dimensionOneRosserSecondSplice)
      le_rfl hgrowth'
  have hfactorU2 : dimensionOneRosserArtificialFactor L 0
      dimensionOneRosserSecondSplice <= 2 := by
    have hden : 0 < 12 * dimensionOneRosserSecondSplice := by positivity
    have hone : 1 / (12 * dimensionOneRosserSecondSplice) <= (1 : Real) := by
      exact (div_le_one hden).2 (by linarith)
    linarith
  have hqUpos : 0 < dimensionOneDelayScaledMinus
      dimensionOneRosserSecondSplice :=
    dimensionOneDelayScaledMinus_pos hUpos
  have hqSpos : 0 < dimensionOneDelayScaledMinus s :=
    dimensionOneDelayScaledMinus_pos (by linarith : 0 < s)
  have hA_s : 1 <= dimensionOneRosserArtificialFactor L 0 s :=
    one_le_dimensionOneRosserArtificialFactor_zero hL (by linarith)
  by_cases hsU : s <= dimensionOneRosserSecondSplice
  · have hqmono := dimensionOneDelayScaledMinus_antitoneOn
      (show s ∈ Ici (2 : Real) by change 2 <= s; linarith)
      (show dimensionOneRosserSecondSplice ∈ Ici (2 : Real) by exact hU2)
      hsU
    have hauxU : dimensionOneRosserMinusArtificialAux L 0 s0 <
        dimensionOneRosserMinusArtificialAux L 0 dimensionOneRosserSecondSplice :=
      hantiU ⟨le_rfl, hUs0.le⟩ ⟨hUs0.le, le_rfl⟩ hUs0
    have hauxUle : dimensionOneRosserMinusArtificialAux L 0
        dimensionOneRosserSecondSplice <=
        2 * dimensionOneRosserMinusArtificialAux L 0 s := by
      unfold dimensionOneRosserMinusArtificialAux at *
      have h1 := mul_le_mul_of_nonneg_right hfactorU2 hqUpos.le
      have h2 := mul_le_mul_of_nonneg_left hqmono
        (mul_nonneg (le_trans (by norm_num) hA_s) hqSpos.le)
      have h3 := mul_le_mul_of_nonneg_right hA_s hqSpos.le
      nlinarith [h1, h2, h3]
    exact hauxU.le.trans hauxUle
  · have hsU' : dimensionOneRosserSecondSplice < s := lt_of_not_ge hsU
    have hsLarge : Real.exp 5000 + 1 <= s := hU.trans hsU'.le
    have hantiS := sourceProfileMinus_strictAntiOn hL hs hsLarge hss0
      hsource hLExp hgate
    have hauxSpos : 0 < dimensionOneRosserMinusArtificialAux L 0 s :=
      dimensionOneRosserMinusArtificialAux_pos hL (by linarith)
    have hauxSle := (hantiS ⟨le_rfl, hss0.le⟩
      ⟨hss0.le, le_rfl⟩ hss0).le
    nlinarith

end PrimesRestrictedDigits
