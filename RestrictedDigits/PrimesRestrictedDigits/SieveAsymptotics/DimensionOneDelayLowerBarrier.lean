import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayLowerBarrierPropagation

/-!
# Explicit lower Eq. (6.5)-scale statement for the dimension-one delay sum

This absorbs the fixed global barrier multiplier into the absolute error coefficient and
proves the lower-scale existential.
-/

open Set

noncomputable section

namespace PrimesRestrictedDigits

private theorem dimensionOneDelayLowerScale_eight_le_auxiliary
    {s : Real} (hs : Real.exp 5000 + 1 <= s) :
    dimensionOneDelayLowerScale 8 s <=
      dimensionOneDelayAuxiliaryLowerScale s := by
  have hs0 : 0 < s := by linarith [Real.exp_pos (5000 : Real)]
  have hsLog : 5000 < Real.log s :=
    (Real.lt_log_iff_exp_lt hs0).2 (by linarith)
  have hsLogPos : 0 < Real.log s := by linarith
  have hmPos : 0 < Real.log (Real.log s) := by
    apply Real.log_pos
    linarith [hsLog]
  have hTwoS : s <= 2 * s := by nlinarith
  have hLogTwoS : Real.log s <= Real.log (2 * s) :=
    Real.strictMonoOn_log.monotoneOn
      (show s ∈ Ioi (0 : Real) by exact hs0)
      (show 2 * s ∈ Ioi (0 : Real) by
        change 0 < 2 * s
        positivity) hTwoS
  have hLogLog : Real.log (Real.log s) <=
      Real.log (Real.log (2 * s)) :=
    Real.strictMonoOn_log.monotoneOn
      (show Real.log s ∈ Ioi (0 : Real) by exact hsLogPos)
      (show Real.log (2 * s) ∈ Ioi (0 : Real) by
        exact hsLogPos.trans_le hLogTwoS)
      hLogTwoS
  have hCoeff : 7 * Real.log (Real.log s) <=
      8 * Real.log (Real.log (2 * s)) := by
    linarith [hLogLog, hmPos]
  have hFactor : 0 <= s / Real.log s := by positivity
  have hMul := mul_le_mul_of_nonneg_left hCoeff hFactor
  unfold dimensionOneDelayLowerScale dimensionOneDelayAuxiliaryLowerScale
    dimensionOneDelayAuxiliaryExponent
  apply Real.exp_le_exp.mpr
  simp only [Pi.add_apply, Pi.sub_apply]
  ring_nf at hMul ⊢
  linarith

private theorem one_le_dimensionOneDelayLowerErrorWeight
    {s : Real} (hs : Real.exp 5000 + 1 <= s) :
    1 <= s * Real.log (Real.log (2 * s)) / Real.log s := by
  have hs0 : 0 < s := by linarith [Real.exp_pos (5000 : Real)]
  have hsLog : 5000 < Real.log s :=
    (Real.lt_log_iff_exp_lt hs0).2 (by linarith)
  have hsLogPos : 0 < Real.log s := by linarith
  have hmOne : 1 < Real.log (Real.log s) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).2
    have hthree : (3 : Real) < Real.log s := by linarith [hsLog]
    exact Real.exp_one_lt_three.trans hthree
  have hLogTwoS : Real.log s <= Real.log (2 * s) :=
    Real.strictMonoOn_log.monotoneOn
      (show s ∈ Ioi (0 : Real) by exact hs0)
      (show 2 * s ∈ Ioi (0 : Real) by
        change 0 < 2 * s
        positivity) (by nlinarith)
  have hmTwo : 1 <= Real.log (Real.log (2 * s)) := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (show Real.log s ∈ Ioi (0 : Real) by exact hsLogPos)
      (show Real.log (2 * s) ∈ Ioi (0 : Real) by
        exact hsLogPos.trans_le hLogTwoS) hLogTwoS
    exact hmOne.le.trans hmono
  have hLogLe : Real.log s <= s := by
    have h := Real.log_le_sub_one_of_pos hs0
    linarith
  rw [le_div_iff₀ hsLogPos]
  have hScale := mul_le_mul_of_nonneg_left hmTwo hs0.le
  nlinarith

private theorem dimensionOneDelayLowerScale_absorb
    {K s : Real} (hK : 0 < K) (hKOne : K <= 1)
    (hs : Real.exp 5000 + 1 <= s) :
    dimensionOneDelayLowerScale (8 - Real.log K) s <=
      K * dimensionOneDelayLowerScale 8 s := by
  let w : Real := s * Real.log (Real.log (2 * s)) / Real.log s
  have hw : 1 <= w := by
    dsimp [w]
    exact one_le_dimensionOneDelayLowerErrorWeight hs
  have hlogK : Real.log K <= 0 := Real.log_nonpos hK.le hKOne
  have hlogMul : Real.log K * w <= Real.log K := by
    simpa only [mul_one] using mul_le_mul_of_nonpos_left hw hlogK
  have hExpFactor : Real.exp (Real.log K * w) <= K := by
    calc
      Real.exp (Real.log K * w) <= Real.exp (Real.log K) :=
        Real.exp_le_exp.mpr hlogMul
      _ = K := Real.exp_log hK
  have hIdentity : dimensionOneDelayLowerScale (8 - Real.log K) s =
      dimensionOneDelayLowerScale 8 s *
        Real.exp (Real.log K * w) := by
    unfold dimensionOneDelayLowerScale
    rw [← Real.exp_add]
    congr 1
    dsimp [w]
    ring
  rw [hIdentity]
  have hE : 0 <= dimensionOneDelayLowerScale 8 s := (Real.exp_pos _).le
  calc
    dimensionOneDelayLowerScale 8 s * Real.exp (Real.log K * w) <=
        dimensionOneDelayLowerScale 8 s * K :=
      mul_le_mul_of_nonneg_left hExpFactor hE
    _ = K * dimensionOneDelayLowerScale 8 s := by ring

/-- Explicit lower half of the dimension-one Eq. (6.5) scale. The constants
are absolute and selected before the real delay coordinate. -/
theorem exists_dimensionOneDelaySum_lowerScale :
    ∃ C S : Real, 0 < C ∧ Real.exp 1 < S ∧
      ∀ {s : Real}, S <= s ->
        dimensionOneDelayLowerScale C s < dimensionOneDelaySum s := by
  obtain ⟨K, hK, hKOne, hGlobal⟩ :=
    exists_dimensionOneDelayAuxiliaryLowerScale_global
  refine ⟨8 - Real.log K, Real.exp 5000 + 1, ?_, ?_, ?_⟩
  · have hlogK : Real.log K <= 0 := Real.log_nonpos hK.le hKOne
    linarith
  · have hExp : Real.exp 1 < Real.exp 5000 :=
      Real.exp_lt_exp.mpr (by norm_num)
    linarith
  · intro s hs
    have hAbsorb := dimensionOneDelayLowerScale_absorb hK hKOne hs
    have hAux := dimensionOneDelayLowerScale_eight_le_auxiliary hs
    have hScale := mul_le_mul_of_nonneg_left hAux hK.le
    exact hAbsorb.trans_lt (hScale.trans_lt (hGlobal hs))

end PrimesRestrictedDigits
