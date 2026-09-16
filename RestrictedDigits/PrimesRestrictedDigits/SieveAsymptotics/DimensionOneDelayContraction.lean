import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayContractionBase

/-!
# Dimension-one delay contraction

This proves the explicit half-contraction for the corrected Section 6 sum and difference. The
proof uses the finite averaging identities and a least point of failure on a compact interval.
Splitting the final averaging window keeps the failure endpoint out of every pointwise
comparison.

See `IWANIEC-ROSSER-SIEVE-1980`, Lemmas 13--14 and Eq. (6.3), printed pp. 189--191.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

private noncomputable def dimensionOneDelayContractionMajorant
    (u x : Real) : Real :=
  dimensionOneDelaySum x / 2 *
    (dimensionOneDelayConjugateWeight (x + 1) /
      dimensionOneDelayConjugateWeight u)

/-- The corrected difference is strictly less than half the corrected sum on
the positive domain. -/
theorem dimensionOneDelay_contraction
    {s : Real} (hs0 : 0 < s) :
    |dimensionOneDelayDifference s| < dimensionOneDelaySum s / 2 := by
  by_cases hs3 : s <= 3
  · exact dimensionOneDelay_base_contraction hs0 hs3
  · have h3s : 3 < s := lt_of_not_ge hs3
    by_contra hTarget
    have hTargetBad : dimensionOneDelaySum s / 2 <=
        |dimensionOneDelayDifference s| := le_of_not_gt hTarget
    let bad : Set Real :=
      {x ∈ Icc (3 : Real) s |
        dimensionOneDelaySum x / 2 <= |dimensionOneDelayDifference x|}
    have hPositiveCarrier : Icc (3 : Real) s ⊆ Ioi 0 := by
      intro x hx
      exact (by linarith [hx.1] : 0 < x)
    have hSumContinuous : ContinuousOn dimensionOneDelaySum (Icc 3 s) :=
      dimensionOneDelaySum_continuousOn.mono hPositiveCarrier
    have hDifferenceContinuous : ContinuousOn dimensionOneDelayDifference
        (Icc 3 s) :=
      dimensionOneDelayDifference_continuousOn.mono hPositiveCarrier
    have hBadClosed : IsClosed bad := by
      dsimp [bad]
      exact isClosed_Icc.isClosed_le (hSumContinuous.div_const 2)
        hDifferenceContinuous.abs
    have hBadCompact : IsCompact bad :=
      isCompact_Icc.of_isClosed_subset hBadClosed (by
        intro x hx
        exact hx.1)
    have hBadNonempty : bad.Nonempty :=
      ⟨s, ⟨⟨h3s.le, le_rfl⟩, hTargetBad⟩⟩
    obtain ⟨u, huBad, huMin⟩ :=
      hBadCompact.exists_isMinOn hBadNonempty continuousOn_id
    have hu3 : 3 < u := by
      have h3u : 3 <= u := huBad.1.1
      by_contra hnot
      have hu : u = 3 := le_antisymm (le_of_not_gt hnot) h3u
      subst u
      have hBase := dimensionOneDelay_base_contraction
        (s := (3 : Real)) (by norm_num) (by norm_num)
      exact (not_lt_of_ge huBad.2) hBase
    have hu0 : 0 < u := by linarith
    have huS : u <= s := huBad.1.2
    have hBefore : ∀ {x : Real}, 0 < x -> x < u ->
        |dimensionOneDelayDifference x| < dimensionOneDelaySum x / 2 := by
      intro x hx0 hxu
      by_cases hx3 : x <= 3
      · exact dimensionOneDelay_base_contraction hx0 hx3
      · have h3x : 3 < x := lt_of_not_ge hx3
        by_contra hnot
        have hxBad : x ∈ bad :=
          ⟨⟨h3x.le, hxu.le.trans huS⟩, le_of_not_gt hnot⟩
        have hux := huMin hxBad
        change u <= x at hux
        linarith
    have hGu : 0 < dimensionOneDelayConjugateWeight u :=
      dimensionOneDelayConjugateWeight_pos (by linarith)
    have hWindowPositive : Icc (u - 1) u ⊆ Ioi 0 := by
      intro x hx
      exact (by linarith [hx.1, hu3] : 0 < x)
    have hAbsContinuous : ContinuousOn
        (fun x => |dimensionOneDelayDifference x|) (Icc (u - 1) u) :=
      (dimensionOneDelayDifference_continuousOn.mono hWindowPositive).abs
    have hMajorantContinuous : ContinuousOn
        (dimensionOneDelayContractionMajorant u) (Icc (u - 1) u) := by
      unfold dimensionOneDelayContractionMajorant
      exact (dimensionOneDelaySum_continuousOn.mono hWindowPositive).div_const 2 |>.mul
        ((dimensionOneDelayConjugateWeight_continuous.comp
          (continuous_id.add continuous_const)).continuousOn.div_const
            (dimensionOneDelayConjugateWeight u))
    have hPointwise : ∀ {x : Real}, x ∈ Icc (u - 1) u -> x < u ->
        |dimensionOneDelayDifference x| <
          dimensionOneDelayContractionMajorant u x := by
      intro x hx hxu
      have hx0 : 0 < x := by linarith [hx.1, hu3]
      have hContract := hBefore hx0 hxu
      have hHalfPos : 0 < dimensionOneDelaySum x / 2 :=
        lt_of_le_of_lt (abs_nonneg _) hContract
      have hGMono : dimensionOneDelayConjugateWeight u <=
          dimensionOneDelayConjugateWeight (x + 1) := by
        apply dimensionOneDelayConjugateWeight_monoOn
        · exact (by linarith : 1 <= u)
        · exact (by linarith [hx.1] : 1 <= x + 1)
        · linarith [hx.1]
      have hRatio : 1 <= dimensionOneDelayConjugateWeight (x + 1) /
          dimensionOneDelayConjugateWeight u :=
        one_le_div_iff.mpr (Or.inl ⟨hGu, hGMono⟩)
      unfold dimensionOneDelayContractionMajorant
      have hScale := mul_le_mul_of_nonneg_left hRatio hHalfPos.le
      nlinarith
    let c : Real := u - 1 / 2
    have hLeftLt : u - 1 < c := by dsimp [c]; linarith
    have hCLt : c < u := by dsimp [c]; linarith
    have hFirstStrict :
        (∫ x in u - 1..c, |dimensionOneDelayDifference x|) <
          ∫ x in u - 1..c, dimensionOneDelayContractionMajorant u x := by
      apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        hLeftLt
        (hAbsContinuous.mono (Icc_subset_Icc_right hCLt.le))
        (hMajorantContinuous.mono (Icc_subset_Icc_right hCLt.le))
      · intro x hx
        have hxu : x < u := hx.2.trans_lt hCLt
        exact (hPointwise ⟨hx.1.le, hxu.le⟩ hxu).le
      · exact ⟨c, ⟨hLeftLt.le, le_rfl⟩,
          hPointwise ⟨hLeftLt.le, hCLt.le⟩ hCLt⟩
    have hSecondWeak :
        (∫ x in c..u, |dimensionOneDelayDifference x|) <=
          ∫ x in c..u, dimensionOneDelayContractionMajorant u x := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hCLt.le
        (hAbsContinuous.mono (Icc_subset_Icc_left hLeftLt.le) |>.intervalIntegrable_of_Icc
          hCLt.le)
        (hMajorantContinuous.mono (Icc_subset_Icc_left hLeftLt.le) |>.intervalIntegrable_of_Icc
          hCLt.le)
      intro x hx
      exact (hPointwise ⟨hLeftLt.le.trans hx.1.le, hx.2.le⟩ hx.2).le
    have hAbsIntegrableLeft : IntervalIntegrable
        (fun x => |dimensionOneDelayDifference x|) volume (u - 1) c :=
      (hAbsContinuous.mono (Icc_subset_Icc_right hCLt.le)).intervalIntegrable_of_Icc
        hLeftLt.le
    have hAbsIntegrableRight : IntervalIntegrable
        (fun x => |dimensionOneDelayDifference x|) volume c u :=
      (hAbsContinuous.mono (Icc_subset_Icc_left hLeftLt.le)).intervalIntegrable_of_Icc
        hCLt.le
    have hMajorantIntegrableLeft : IntervalIntegrable
        (dimensionOneDelayContractionMajorant u) volume (u - 1) c :=
      (hMajorantContinuous.mono
        (Icc_subset_Icc_right hCLt.le)).intervalIntegrable_of_Icc hLeftLt.le
    have hMajorantIntegrableRight : IntervalIntegrable
        (dimensionOneDelayContractionMajorant u) volume c u :=
      (hMajorantContinuous.mono
        (Icc_subset_Icc_left hLeftLt.le)).intervalIntegrable_of_Icc hCLt.le
    have hIntegralStrict :
        (∫ x in u - 1..u, |dimensionOneDelayDifference x|) <
          ∫ x in u - 1..u, dimensionOneDelayContractionMajorant u x := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hAbsIntegrableLeft
          hAbsIntegrableRight,
        ← intervalIntegral.integral_add_adjacent_intervals hMajorantIntegrableLeft
          hMajorantIntegrableRight]
      exact add_lt_add_of_lt_of_le hFirstStrict hSecondWeak
    have hMajorantIntegral :
        (∫ x in u - 1..u, dimensionOneDelayContractionMajorant u x) =
          u * dimensionOneDelaySum u / 2 := by
      rw [show (∫ x in u - 1..u, dimensionOneDelayContractionMajorant u x) =
          (1 / (2 * dimensionOneDelayConjugateWeight u)) *
            ∫ x in u - 1..u,
              dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1) by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _hx
        unfold dimensionOneDelayContractionMajorant
        field_simp [hGu.ne'],
        ← dimensionOneDelaySum_averaging hu3.le]
      field_simp [hGu.ne']
    have hDifferenceIntegral := dimensionOneDelayDifference_averaging hu3.le
    have hAbsolute : u * |dimensionOneDelayDifference u| <=
        ∫ x in u - 1..u, |dimensionOneDelayDifference x| := by
      calc
        u * |dimensionOneDelayDifference u| =
            |u * dimensionOneDelayDifference u| := by
          rw [abs_mul, abs_of_pos hu0]
        _ = |∫ x in u - 1..u, dimensionOneDelayDifference x| := by
          rw [hDifferenceIntegral, abs_neg]
        _ <= ∫ x in u - 1..u, |dimensionOneDelayDifference x| :=
          intervalIntegral.abs_integral_le_integral_abs (by linarith)
    have hContradiction : u * |dimensionOneDelayDifference u| <
        u * dimensionOneDelaySum u / 2 := by
      calc
        u * |dimensionOneDelayDifference u| <=
            ∫ x in u - 1..u, |dimensionOneDelayDifference x| := hAbsolute
        _ < ∫ x in u - 1..u, dimensionOneDelayContractionMajorant u x :=
          hIntegralStrict
        _ = u * dimensionOneDelaySum u / 2 := hMajorantIntegral
    have hFailureScaled := mul_le_mul_of_nonneg_left huBad.2 hu0.le
    nlinarith

end PrimesRestrictedDigits
