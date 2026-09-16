import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayLowerBarrierSubsolution
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayMonotonicity

/-!
# Global propagation of the explicit lower delay barrier

The strict unit-window subsolution and the Y upper average rule out a first point where a
fixed positive multiple of the barrier meets the delay sum.
-/

open MeasureTheory Set

noncomputable section

namespace PrimesRestrictedDigits

theorem dimensionOneDelayAuxiliaryLowerScale_lt_one
    {s : Real} (hs : Real.exp 5000 <= s) :
    dimensionOneDelayAuxiliaryLowerScale s < 1 := by
  have hs0 : 0 < s := (Real.exp_pos 5000).trans_le hs
  have hsLog : 5000 <= Real.log s :=
    (Real.le_log_iff_exp_le hs0).2 hs
  have hsLogPos : 0 < Real.log s := by linarith
  have hmPos : 0 < Real.log (Real.log s) := by
    apply Real.log_pos
    linarith
  unfold dimensionOneDelayAuxiliaryLowerScale
    dimensionOneDelayAuxiliaryExponent
  rw [Real.exp_lt_one_iff]
  have hMain : 0 < s * (Real.log s - 1) :=
    mul_pos hs0 (by linarith)
  have hLogLog : 0 <= s * Real.log (Real.log s) :=
    mul_nonneg hs0.le hmPos.le
  have hError : 0 <= 7 * (s * Real.log (Real.log s) / Real.log s) := by
    positivity
  simp only [Pi.add_apply, Pi.sub_apply]
  nlinarith

theorem exists_dimensionOneDelayAuxiliaryLowerScale_global :
    ∃ K : Real, 0 < K ∧ K <= 1 ∧
      ∀ {s : Real}, Real.exp 5000 + 1 <= s ->
        K * dimensionOneDelayAuxiliaryLowerScale s <
          dimensionOneDelaySum s := by
  let S : Real := Real.exp 5000 + 1
  let K : Real := min 1 (dimensionOneDelaySum S) / 2
  have hS0 : 0 < S := by
    dsimp [S]
    linarith [Real.exp_pos (5000 : Real)]
  have hSumS : 0 < dimensionOneDelaySum S :=
    dimensionOneDelaySum_pos hS0
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (lt_min (by norm_num) hSumS) (by norm_num)
  have hKOne : K <= 1 := by
    dsimp [K]
    have hmin : min (1 : Real) (dimensionOneDelaySum S) <= 1 := min_le_left _ _
    nlinarith
  have hKSum : K < dimensionOneDelaySum S := by
    have hmin : min (1 : Real) (dimensionOneDelaySum S) <=
        dimensionOneDelaySum S := min_le_right _ _
    dsimp [K]
    nlinarith
  have hInitial : ∀ x ∈ Icc (S - 1) S,
      K * dimensionOneDelayAuxiliaryLowerScale x <
        dimensionOneDelaySum x := by
    intro x hx
    have hxLarge : Real.exp 5000 <= x := by
      dsimp [S] at hx
      linarith [hx.1]
    have hB := dimensionOneDelayAuxiliaryLowerScale_lt_one hxLarge
    have hKB : K * dimensionOneDelayAuxiliaryLowerScale x < K :=
      by simpa using (mul_lt_mul_iff_of_pos_left hK).2 hB
    have hx0 : 0 < x := (Real.exp_pos 5000).trans_le hxLarge
    have hAnti : dimensionOneDelaySum S <= dimensionOneDelaySum x :=
      dimensionOneDelaySum_strictAntiOn.antitoneOn
        (show x ∈ Ioi (0 : Real) by exact hx0)
        (show S ∈ Ioi (0 : Real) by exact hS0) hx.2
    exact hKB.trans (hKSum.trans_le hAnti)
  refine ⟨K, hK, hKOne, ?_⟩
  intro s hs
  change S <= s at hs
  by_contra hTarget
  have hBadS : dimensionOneDelaySum s <=
      K * dimensionOneDelayAuxiliaryLowerScale s := le_of_not_gt hTarget
  let bad : Set Real :=
    {x ∈ Icc S s | dimensionOneDelaySum x <=
      K * dimensionOneDelayAuxiliaryLowerScale x}
  have hPositiveCarrier : Icc S s ⊆ Ioi (0 : Real) := by
    intro x hx
    change 0 < x
    exact hS0.trans_le hx.1
  have hOneCarrier : Icc S s ⊆ Ioi (1 : Real) := by
    intro x hx
    change 1 < x
    have hExpOne : 1 < Real.exp 5000 := by
      have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
      linarith
    dsimp [S] at hx
    linarith [hx.1, hExpOne]
  have hSumCont : ContinuousOn dimensionOneDelaySum (Icc S s) :=
    dimensionOneDelaySum_continuousOn.mono hPositiveCarrier
  have hBCont : ContinuousOn dimensionOneDelayAuxiliaryLowerScale (Icc S s) :=
    dimensionOneDelayAuxiliaryLowerScale_continuousOn.mono hOneCarrier
  have hBadClosed : IsClosed bad := by
    dsimp [bad]
    exact isClosed_Icc.isClosed_le hSumCont (continuousOn_const.mul hBCont)
  have hBadCompact : IsCompact bad :=
    isCompact_Icc.of_isClosed_subset hBadClosed (by
      intro x hx
      exact hx.1)
  have hBadNonempty : bad.Nonempty :=
    ⟨s, ⟨⟨hs, le_rfl⟩, hBadS⟩⟩
  obtain ⟨u, huBad, huMin⟩ :=
    hBadCompact.exists_isMinOn hBadNonempty continuousOn_id
  have huS : S <= u := huBad.1.1
  have hus : u <= s := huBad.1.2
  have hSu : S < u := by
    apply lt_of_le_of_ne huS
    intro hEq
    have hu : u = S := hEq.symm
    subst u
    exact (not_lt_of_ge huBad.2) (hInitial S ⟨by linarith, le_rfl⟩)
  have huLarge : Real.exp 5000 + 1 <= u := by
    simpa [S] using huS
  have hu0 : 0 < u := hS0.trans_le huS
  have hPointwise : ∀ x ∈ Ioo (u - 1) u,
      0 < dimensionOneDelaySum x -
        K * dimensionOneDelayAuxiliaryLowerScale x := by
    intro x hx
    have hxLower : S - 1 < x := by linarith [hSu, hx.1]
    by_cases hxS : x <= S
    · have h := hInitial x ⟨hxLower.le, hxS⟩
      linarith
    · have hxS' : S < x := lt_of_not_ge hxS
      have hxBound : x <= s := hx.2.le.trans hus
      by_contra hnot
      have hxBad : x ∈ bad :=
        ⟨⟨hxS'.le, hxBound⟩, by linarith⟩
      have hux := huMin hxBad
      change u <= x at hux
      linarith [hx.2]
  have hWindowOne : Icc (u - 1) u ⊆ Ioi (1 : Real) := by
    intro x hx
    change 1 < x
    have hExpOne : 1 < Real.exp 5000 := by
      have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
      linarith
    linarith [huLarge, hx.1, hExpOne]
  have hWindowPositive : Icc (u - 1) u ⊆ Ioi (0 : Real) := by
    intro x hx
    exact (show 0 < x by
      linarith [huLarge, hx.1, Real.exp_pos (5000 : Real)])
  have hDiffCont : ContinuousOn (fun x => dimensionOneDelaySum x -
      K * dimensionOneDelayAuxiliaryLowerScale x) (Icc (u - 1) u) :=
    (dimensionOneDelaySum_continuousOn.mono hWindowPositive).sub
      (continuousOn_const.mul
        (dimensionOneDelayAuxiliaryLowerScale_continuousOn.mono hWindowOne))
  have hDiffInt : IntervalIntegrable (fun x => dimensionOneDelaySum x -
      K * dimensionOneDelayAuxiliaryLowerScale x) volume (u - 1) u :=
    hDiffCont.intervalIntegrable_of_Icc (by linarith)
  have hDiffPos := intervalIntegral.intervalIntegral_pos_of_pos_on
    hDiffInt hPointwise
    (by linarith : u - 1 < u)
  have hSumInt : IntervalIntegrable dimensionOneDelaySum volume (u - 1) u :=
    (dimensionOneDelaySum_continuousOn.mono hWindowPositive)
      |>.intervalIntegrable_of_Icc (by linarith)
  have hBInt : IntervalIntegrable dimensionOneDelayAuxiliaryLowerScale
      volume (u - 1) u :=
    (dimensionOneDelayAuxiliaryLowerScale_continuousOn.mono hWindowOne)
      |>.intervalIntegrable_of_Icc (by linarith)
  have hIntegralStrict : K *
      (∫ x in u - 1..u, dimensionOneDelayAuxiliaryLowerScale x) <
      ∫ x in u - 1..u, dimensionOneDelaySum x := by
    rw [intervalIntegral.integral_sub hSumInt (hBInt.const_mul K),
      intervalIntegral.integral_const_mul] at hDiffPos
    linarith
  have hSub := dimensionOneDelayAuxiliaryLowerScale_unit_subsolution huLarge
  have hSubScaled : u *
      (K * dimensionOneDelayAuxiliaryLowerScale u) <
      K * (∫ x in u - 1..u, dimensionOneDelayAuxiliaryLowerScale x) := by
    have h := mul_lt_mul_of_pos_left hSub hK
    nlinarith
  have huThree : 3 <= u := by
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith [huLarge]
  have hUpper := dimensionOneDelaySum_integral_le (s := u) huThree
  have hContradiction : u *
      (K * dimensionOneDelayAuxiliaryLowerScale u) <
      u * dimensionOneDelaySum u :=
    hSubScaled.trans (hIntegralStrict.trans_le hUpper)
  have hCancel : K * dimensionOneDelayAuxiliaryLowerScale u <
      dimensionOneDelaySum u :=
    (mul_lt_mul_iff_of_pos_left hu0).mp hContradiction
  exact (not_lt_of_ge huBad.2) hCancel

end PrimesRestrictedDigits
