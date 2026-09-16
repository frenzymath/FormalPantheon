import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralLargeAnalytic
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralLargeLogCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralLargeOuterIntegration
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighCentralLargeIntegralBound -/
open MeasureTheory Set
open scoped BigOperators
namespace PrimesRestrictedDigits
noncomputable section

private theorem i8_outer_inner_integrable (branch : Fin 2) :
    IntegrableOn
      (fun u => ∫ v in sectionSixFirstHighCentralLargeCertificateLower u..
          sectionSixFirstHighCentralLargeCertificateUpper u,
          sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v))
      (sectionSixFirstHighCentralLargeCertificateOuter branch) := by
  apply integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    _ _ _ _
    (sectionSixFirstHighCentralLargeCertificate_outer_measurable branch)
    sectionSixFirstHighCentralLargeCertificate_lower_measurable
    sectionSixFirstHighCentralLargeCertificate_upper_measurable
    (fun u hu => (sectionSixFirstHighCentralLargeCertificate_outer_facts branch hu).2.2.2.2.1)
    (by rw [← Measure.volume_eq_prod]
        exact sectionSixFirstHighCentralLargeCertificate_fiber_integrable branch)

private theorem i8_buchstab_intervalIntegrable_le
    {u B l h : Real} (hu : 0 < u) (hl : 0 < l) (hlh : l ≤ h)
    (hupper : 2 * h ≤ B) :
    IntervalIntegrable
      (fun t : Real => buchstabFunction ((B - t) / t) / (u * t ^ 2))
      volume l h := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  · exact sectionSixFirstHighCentralLargeCertificate_buchstab_intervalIntegrable
      hu hl hlh hupper

private theorem i8_mixed_tail_intervalIntegrable :
    IntervalIntegrable
      (fun t : Real => sectionSixFirstHighCentralLargeCertificateMixedTailMajorant t)
      volume sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3 := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro t ht
  rw [uIcc_of_le (by norm_num [sectionSixFirstHighCentralLargeCertificateBeta,
    sectionSixFirstHighCentralLargeCertificateU3] :
    sectionSixFirstHighCentralLargeCertificateBeta ≤
      sectionSixFirstHighCentralLargeCertificateU3)] at ht
  have htPos : 0 < t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateBeta,
      sectionSixFirstHighCentralLargeCertificateU3] at ht ⊢
    linarith
  have htA : 0 < sectionSixFirstHighCentralLargeCertificateA - t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateA,
      sectionSixFirstHighCentralLargeCertificateU3] at ht ⊢
    linarith
  have htM : 0 < sectionSixFirstHighCentralLargeCertificateMiddle t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateMiddle,
      sectionSixFirstHighCentralLargeCertificateU3] at ht ⊢
    linarith [ht.2]
  have htU : 0 < sectionSixFirstHighCentralLargeCertificateUpper t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateU3,
      sectionSixFirstHighCentralLargeCertificateUpper] at ht ⊢
    linarith
  change ContinuousAt
    (fun t : Real => sectionSixFirstHighCentralLargeCertificateTailConstant / t *
      (1 / ((sectionSixFirstHighCentralLargeCertificateA - t) / 2) -
        1 / ((1 - t) / 4))) t
  fun_prop (disch := positivity)

private theorem i8_mixed_middle_intervalIntegrable :
    IntervalIntegrable
      (fun t : Real => sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant t)
      volume sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3 := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro t ht
  rw [uIcc_of_le (by norm_num [sectionSixFirstHighCentralLargeCertificateBeta,
    sectionSixFirstHighCentralLargeCertificateU3] :
    sectionSixFirstHighCentralLargeCertificateBeta ≤
      sectionSixFirstHighCentralLargeCertificateU3)] at ht
  have htPos : 0 < t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateBeta,
      sectionSixFirstHighCentralLargeCertificateU3] at ht ⊢
    linarith
  have htC : 0 < sectionSixFirstHighCentralLargeCertificateC - t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateU3] at ht ⊢
    linarith
  have htU : 0 < sectionSixFirstHighCentralLargeCertificateUpper t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateU3,
      sectionSixFirstHighCentralLargeCertificateUpper] at ht ⊢
    linarith
  have htOne : 0 < 1 - t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateU3] at ht ⊢
    linarith [ht.2]
  have htOneNe : (1 - t) / 4 ≠ 0 := by positivity
  change ContinuousAt
    (fun t : Real => sectionSixFirstHighCentralLargeCertificateMiddleConstant / t *
      (1 / ((1 - t) / 4) -
        1 / (sectionSixFirstHighCentralLargeCertificateC - t))) t
  fun_prop (disch := positivity)

private theorem i8_tail_intervalIntegrable :
    IntervalIntegrable
      (fun t : Real => sectionSixFirstHighCentralLargeCertificateTailMajorant t)
      volume sectionSixFirstHighCentralLargeCertificateU3 (1 / 2) := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro t ht
  rw [uIcc_of_le (by norm_num [sectionSixFirstHighCentralLargeCertificateU3] :
    sectionSixFirstHighCentralLargeCertificateU3 ≤ (1 / 2 : Real))] at ht
  have htPos : 0 < t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateU3] at ht ⊢
    linarith
  have htA : 0 < sectionSixFirstHighCentralLargeCertificateA - t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateA,
      sectionSixFirstHighCentralLargeCertificateU3] at ht ⊢
    linarith
  have htC : 0 < sectionSixFirstHighCentralLargeCertificateC - t := by
    norm_num [sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateU3] at ht ⊢
    linarith
  change ContinuousAt
    (fun t : Real => sectionSixFirstHighCentralLargeCertificateTailConstant / t *
      (1 / ((sectionSixFirstHighCentralLargeCertificateA - t) / 2) -
        1 / (sectionSixFirstHighCentralLargeCertificateC - t))) t
  fun_prop (disch := positivity)

private theorem i8_branch0_outer_le :
    (∫ u in sectionSixFirstHighCentralLargeCertificateOuter 0,
      ∫ v in sectionSixFirstHighCentralLargeCertificateLower u..
        sectionSixFirstHighCentralLargeCertificateUpper u,
        sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v)) ≤
      (∫ u in sectionSixFirstHighCentralLargeCertificateOuter 0,
        sectionSixFirstHighCentralLargeCertificateMixedTailMajorant u) +
      (∫ u in sectionSixFirstHighCentralLargeCertificateOuter 0,
        sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant u) := by
  let f := fun u => ∫ v in sectionSixFirstHighCentralLargeCertificateLower u..
      sectionSixFirstHighCentralLargeCertificateUpper u,
      sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v)
  have hAB : sectionSixFirstHighCentralLargeCertificateBeta ≤
      sectionSixFirstHighCentralLargeCertificateU3 := by
    norm_num [sectionSixFirstHighCentralLargeCertificateBeta,
      sectionSixFirstHighCentralLargeCertificateU3]
  have hfOn := i8_outer_inner_integrable 0
  have hf : IntervalIntegrable f volume
      sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
    simpa [f, sectionSixFirstHighCentralLargeCertificateOuter] using hfOn
  have hleftInt : ∀ u ∈ Icc sectionSixFirstHighCentralLargeCertificateBeta
      sectionSixFirstHighCentralLargeCertificateU3,
      IntervalIntegrable
        (fun v => sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v))
        volume (sectionSixFirstHighCentralLargeCertificateLower u)
          (sectionSixFirstHighCentralLargeCertificateMiddle u) := by
    intro u hu
    have huPos : 0 < u := by
      norm_num [sectionSixFirstHighCentralLargeCertificateBeta] at hu ⊢
      linarith [hu.1]
    have hLPos : 0 < sectionSixFirstHighCentralLargeCertificateLower u := by
      norm_num [sectionSixFirstHighCentralLargeCertificateA,
        sectionSixFirstHighCentralLargeCertificateBeta,
        sectionSixFirstHighCentralLargeCertificateLower,
        sectionSixFirstHighCentralLargeCertificateU3] at hu ⊢
      linarith [hu.2]
    have hLMlt : sectionSixFirstHighCentralLargeCertificateLower u ≤
        sectionSixFirstHighCentralLargeCertificateMiddle u := by
      norm_num [sectionSixFirstHighCentralLargeCertificateA,
        sectionSixFirstHighCentralLargeCertificateBeta,
        sectionSixFirstHighCentralLargeCertificateLower,
        sectionSixFirstHighCentralLargeCertificateMiddle,
        sectionSixFirstHighCentralLargeCertificateU3] at hu ⊢
      nlinarith [hu.1]
    have hi := i8_buchstab_intervalIntegrable_le
      (u := u) (B := 1 - u)
      (l := sectionSixFirstHighCentralLargeCertificateLower u)
      (h := sectionSixFirstHighCentralLargeCertificateMiddle u)
      huPos hLPos hLMlt (by
        change 2 * ((1 - u) / 4) ≤ 1 - u
        norm_num [sectionSixFirstHighCentralLargeCertificateU3] at hu ⊢
        linarith [hu.2])
    simpa [sectionSixFirstHighCentralLargeCertificateTransposedKernel,
      sectionSixFirstPairBuchstabKernel] using hi
  have hrightInt : ∀ u ∈ Icc sectionSixFirstHighCentralLargeCertificateBeta
      sectionSixFirstHighCentralLargeCertificateU3,
      IntervalIntegrable
        (fun v => sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v))
        volume (sectionSixFirstHighCentralLargeCertificateMiddle u)
          (sectionSixFirstHighCentralLargeCertificateUpper u) := by
    intro u hu
    have huPos : 0 < u := by
      norm_num [sectionSixFirstHighCentralLargeCertificateBeta] at hu ⊢
      norm_num [sectionSixFirstHighCentralLargeCertificateU3] at hu ⊢
      linarith [hu.1, hu.2]
    have hMPos : 0 < sectionSixFirstHighCentralLargeCertificateMiddle u := by
      norm_num [sectionSixFirstHighCentralLargeCertificateMiddle,
        sectionSixFirstHighCentralLargeCertificateU3] at hu ⊢
      linarith [hu.2]
    have hMHlt : sectionSixFirstHighCentralLargeCertificateMiddle u ≤
        sectionSixFirstHighCentralLargeCertificateUpper u := by
      change (1 - u) / 4 ≤ (287500001 / 500000000 : Real) - u
      norm_num [sectionSixFirstHighCentralLargeCertificateBeta,
        sectionSixFirstHighCentralLargeCertificateU3] at hu ⊢
      linarith [hu.1, hu.2]
    exact i8_buchstab_intervalIntegrable_le
      (u := u) (B := 1 - u)
      (l := sectionSixFirstHighCentralLargeCertificateMiddle u)
      (h := sectionSixFirstHighCentralLargeCertificateUpper u)
      huPos hMPos hMHlt (by
        norm_num [sectionSixFirstHighCentralLargeCertificateC,
          sectionSixFirstHighCentralLargeCertificateUpper,
          sectionSixFirstHighCentralLargeCertificateBeta] at hu ⊢
        linarith [hu.1])
  have hpoint : ∀ u ∈ Icc sectionSixFirstHighCentralLargeCertificateBeta
      sectionSixFirstHighCentralLargeCertificateU3, f u ≤
      sectionSixFirstHighCentralLargeCertificateMixedTailMajorant u +
        sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant u := by
    intro u hu
    have hleft := sectionSixFirstHighCentralLargeCertificate_mixed_tail_inner_le hu
    have hright := sectionSixFirstHighCentralLargeCertificate_mixed_middle_inner_le hu
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hleftInt u hu) (hrightInt u hu)
    dsimp [f]
    rw [← hsplit]
    linarith
  have hsumInt : IntervalIntegrable
      (fun u => sectionSixFirstHighCentralLargeCertificateMixedTailMajorant u +
        sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant u) volume
      sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3 :=
    i8_mixed_tail_intervalIntegrable.add i8_mixed_middle_intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hAB hf hsumInt hpoint
  rw [intervalIntegral.integral_add i8_mixed_tail_intervalIntegrable
    i8_mixed_middle_intervalIntegrable] at hmono
  simpa [f, sectionSixFirstHighCentralLargeCertificateOuter,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hAB,
    intervalIntegral.integral_add] using hmono
private theorem i8_branch1_outer_le :
    (∫ u in sectionSixFirstHighCentralLargeCertificateOuter 1,
      ∫ v in sectionSixFirstHighCentralLargeCertificateLower u..
        sectionSixFirstHighCentralLargeCertificateUpper u,
        sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v)) ≤
      ∫ u in sectionSixFirstHighCentralLargeCertificateOuter 1,
        sectionSixFirstHighCentralLargeCertificateTailMajorant u := by
  let f := fun u => ∫ v in sectionSixFirstHighCentralLargeCertificateLower u..
      sectionSixFirstHighCentralLargeCertificateUpper u,
      sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v)
  have hAB : sectionSixFirstHighCentralLargeCertificateU3 ≤ (1 / 2 : Real) := by
    norm_num [sectionSixFirstHighCentralLargeCertificateU3]
  have hfOn := i8_outer_inner_integrable 1
  have hf : IntervalIntegrable f volume
      sectionSixFirstHighCentralLargeCertificateU3 (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
    simpa [f, sectionSixFirstHighCentralLargeCertificateOuter] using hfOn
  have hpoint : ∀ u ∈ Icc sectionSixFirstHighCentralLargeCertificateU3 (1 / 2),
      f u ≤ sectionSixFirstHighCentralLargeCertificateTailMajorant u := by
    intro u hu
    exact sectionSixFirstHighCentralLargeCertificate_tail_inner_le hu
  have hmono := intervalIntegral.integral_mono_on hAB hf
    i8_tail_intervalIntegrable hpoint
  change (∫ u in Icc sectionSixFirstHighCentralLargeCertificateU3 (1 / 2), f u) ≤
    ∫ u in Icc sectionSixFirstHighCentralLargeCertificateU3 (1 / 2),
      sectionSixFirstHighCentralLargeCertificateTailMajorant u
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hAB,
    ← intervalIntegral.integral_of_le hAB]
  exact hmono

private theorem i8_integral_delta_lt :
    sectionSixFirstHighCentralLargeIntegral
        sectionSixFirstHighCentralLargeCertificateDelta <
      (203394 : Real) / 1000000 := by
  rw [← sectionSixFirstHighCentralLargeCertificate_setIntegral_transpose]
  calc
    _ ≤ ∑ branch ∈ (Finset.univ : Finset (Fin 2)),
        ∫ z in sectionSixFirstHighCentralLargeCertificateFiber branch,
          sectionSixFirstHighCentralLargeCertificateTransposedKernel z :=
      setIntegral_le_finset_setIntegral_of_cover volume Finset.univ _ _ _
        ((measurableSet_sectionSixFirstHighCentralLargeRegion _).preimage
          measurable_swap)
        (fun branch _ => sectionSixFirstHighCentralLargeCertificate_fiber_measurable branch)
        (fun branch _ => sectionSixFirstHighCentralLargeCertificate_fiber_integrable branch)
        (fun branch _ z hz =>
          sectionSixFirstHighCentralLargeCertificate_fiber_nonneg branch hz)
        sectionSixFirstHighCentralLargeCertificate_region_covered
    _ = ∑ branch : Fin 2,
        ∫ u in sectionSixFirstHighCentralLargeCertificateOuter branch,
          ∫ v in sectionSixFirstHighCentralLargeCertificateLower u..
            sectionSixFirstHighCentralLargeCertificateUpper u,
            sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v) := by
      apply Finset.sum_congr rfl
      intro branch _
      rw [Measure.volume_eq_prod]
      exact setIntegral_closedIccFiberCell_eq_iterated _ _ _ _
        (sectionSixFirstHighCentralLargeCertificate_outer_measurable branch)
        sectionSixFirstHighCentralLargeCertificate_lower_measurable
        sectionSixFirstHighCentralLargeCertificate_upper_measurable
        (fun u hu =>
          (sectionSixFirstHighCentralLargeCertificate_outer_facts branch hu).2.2.2.2.1)
        (by
          rw [← Measure.volume_eq_prod]
          exact sectionSixFirstHighCentralLargeCertificate_fiber_integrable branch)
    _ ≤
        (∫ u in sectionSixFirstHighCentralLargeCertificateOuter 0,
          sectionSixFirstHighCentralLargeCertificateMixedTailMajorant u) +
        (∫ u in sectionSixFirstHighCentralLargeCertificateOuter 0,
          sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant u) +
        (∫ u in sectionSixFirstHighCentralLargeCertificateOuter 1,
          sectionSixFirstHighCentralLargeCertificateTailMajorant u) := by
      simpa [Fin.sum_univ_two] using
        add_le_add i8_branch0_outer_le i8_branch1_outer_le
    _ = sectionSixFirstHighCentralLargeCertificateLogCombination := by
      rw [sectionSixFirstHighCentralLargeCertificate_mixedTail_outer_eq,
        sectionSixFirstHighCentralLargeCertificate_mixedMiddle_outer_eq,
        sectionSixFirstHighCentralLargeCertificate_tail_outer_eq]
      rfl
    _ < (203394 : Real) / 1000000 :=
      sectionSixFirstHighCentralLargeCertificateLogCombination_lt

private theorem i8_project_nonneg_on_delta {x : Real × Real}
    (hx : x ∈ sectionSixFirstHighCentralLargeRegion
      sectionSixFirstHighCentralLargeCertificateDelta) :
    0 ≤ sectionSixFirstPairBuchstabKernel x := by
  rcases hx with ⟨hgap, horder, _, hhalf, hcap, _, _, _⟩
  have hparams := sectionSix_parameter_bounds
    (epsilon := sectionSixFirstHighCentralLargeCertificateDelta)
    (by norm_num [sectionSixFirstHighCentralLargeCertificateDelta])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateDelta])
  have hv : 0 < x.1 := hparams.1.trans hgap
  have hu : 0 < x.2 := hv.trans_le horder
  have harg : 1 ≤ (1 - x.2 - x.1) / x.1 := by
    rw [le_div_iff₀ hv]
    linarith
  have homega := buchstabFunction_mem_Icc harg
  unfold sectionSixFirstPairBuchstabKernel
  have hden : 0 < x.2 * x.1 ^ 2 :=
    mul_pos hu (sq_pos_of_pos hv)
  exact div_nonneg (by linarith [homega.1]) hden.le

theorem sectionSixFirstHighCentralLargeIntegral_lt
    {epsilon : Real}
    (hepsilonUpper : epsilon <= 1 / 1000000000) :
    sectionSixFirstHighCentralLargeIntegral epsilon <
      (203394 : Real) / 1000000 := by
  have hepsilonDelta : epsilon <=
      sectionSixFirstHighCentralLargeCertificateDelta := by
    change epsilon <= (1 / 1000000000 : Real)
    exact hepsilonUpper
  have hnonneg : 0 ≤ᵐ[volume.restrict
      (sectionSixFirstHighCentralLargeRegion
        sectionSixFirstHighCentralLargeCertificateDelta)]
      sectionSixFirstPairBuchstabKernel := by
    filter_upwards [ae_restrict_mem
      (measurableSet_sectionSixFirstHighCentralLargeRegion _)] with x hx
    exact i8_project_nonneg_on_delta hx
  unfold sectionSixFirstHighCentralLargeIntegral
  calc
    _ ≤ ∫ x in sectionSixFirstHighCentralLargeRegion
        sectionSixFirstHighCentralLargeCertificateDelta,
        sectionSixFirstPairBuchstabKernel x :=
      setIntegral_mono_set
        sectionSixFirstHighCentralLargeCertificate_project_integrable
        hnonneg
        (Filter.Eventually.of_forall
          (sectionSixFirstHighCentralLargeRegion_mono hepsilonDelta))
    _ < (203394 : Real) / 1000000 := i8_integral_delta_lt

end
end PrimesRestrictedDigits
