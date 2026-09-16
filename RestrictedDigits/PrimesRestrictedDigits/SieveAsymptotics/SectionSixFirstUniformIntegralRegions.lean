import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallQuadrupleRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleRegions
import Mathlib.Tactic.Linarith
/-! # SectionSixFirstUniformIntegralRegions -/

open Set

namespace PrimesRestrictedDigits

private theorem main005AI_thetaGap_anti
    {epsilon delta : Real} (h : epsilon <= delta) :
    sectionSixThetaGap delta <= sectionSixThetaGap epsilon := by
  simp only [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  linarith

private theorem main005AI_thetaOne_mono
    {epsilon delta : Real} (h : epsilon <= delta) :
    sectionSixThetaOne epsilon <= sectionSixThetaOne delta := by
  simp only [sectionSixThetaOne]
  linarith

private theorem main005AI_thetaTwo_anti
    {epsilon delta : Real} (h : epsilon <= delta) :
    sectionSixThetaTwo delta <= sectionSixThetaTwo epsilon := by
  simp only [sectionSixThetaTwo]
  linarith

private theorem main005AI_not_mem_thetaBand_mono
    {epsilon delta y : Real} (h : epsilon <= delta)
    (hy : y ∉ Set.Icc (sectionSixThetaOne epsilon)
      (sectionSixThetaTwo epsilon)) :
    y ∉ Set.Icc (sectionSixThetaOne delta)
      (sectionSixThetaTwo delta) := by
  intro hyDelta
  apply hy
  exact ⟨(main005AI_thetaOne_mono h).trans hyDelta.1,
    hyDelta.2.trans (main005AI_thetaTwo_anti h)⟩

private theorem main005AI_not_mem_complementBand_mono
    {epsilon delta y : Real} (h : epsilon <= delta)
    (hy : y ∉ Set.Icc (1 - sectionSixThetaTwo epsilon)
      (1 - sectionSixThetaOne epsilon)) :
    y ∉ Set.Icc (1 - sectionSixThetaTwo delta)
      (1 - sectionSixThetaOne delta) := by
  intro hyDelta
  apply hy
  have hone := main005AI_thetaOne_mono h
  have htwo := main005AI_thetaTwo_anti h
  exact ⟨by linarith [hyDelta.1], by linarith [hyDelta.2]⟩

def sectionSixFirstLowCentralSmallUniformOuterRegion
    (delta : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap delta < x.2 ∧
    x.2 <= x.1.2 ∧ x.1.2 <= x.1.1.2 ∧ x.1.1.2 <= x.1.1.1 ∧
    x.1.1.1 <= sectionSixThetaOne delta ∧
    sectionSixThetaTwo delta < x.1.1.1 + x.1.1.2 ∧
    x.1.1.1 + 2 * x.1.1.2 < 16 / 25 ∧
    x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1 ∧
    x.1.1.1 + x.1.2 ∉
      Set.Icc (sectionSixThetaOne delta) (sectionSixThetaTwo delta) ∧
    x.1.1.1 + x.2 ∉
      Set.Icc (sectionSixThetaOne delta) (sectionSixThetaTwo delta) ∧
    x.1.1.2 + x.1.2 ∉
      Set.Icc (sectionSixThetaOne delta) (sectionSixThetaTwo delta) ∧
    x.1.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne delta) (sectionSixThetaTwo delta) ∧
    x.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne delta) (sectionSixThetaTwo delta)}

def sectionSixFirstHighCentralSmallUniformOuterRegion
    (delta : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap delta < x.2 ∧
    x.2 <= x.1.2 ∧ x.1.2 <= x.1.1.2 ∧
    sectionSixThetaTwo delta < x.1.1.1 ∧
    x.1.1.1 <= (1 / 2 : Real) ∧
    x.1.1.1 + 2 * x.1.1.2 < 16 / 25}

theorem sectionSixFirstLowFarRegion_mono
    {epsilon delta : Real} (h : epsilon <= delta) :
    sectionSixFirstLowFarRegion epsilon ⊆
      sectionSixFirstLowFarRegion delta := by
  rintro x ⟨hgap, horder, hu, hcap, hsum⟩
  have hgap' := main005AI_thetaGap_anti h
  have hone := main005AI_thetaOne_mono h
  exact ⟨hgap'.trans_lt hgap, horder, hu.trans hone, hcap,
    by linarith⟩

theorem sectionSixFirstLowCentralLargeTerminalRegion_mono
    {epsilon delta : Real} (h : epsilon <= delta) :
    sectionSixFirstLowCentralLargeTerminalRegion epsilon ⊆
      sectionSixFirstLowCentralLargeTerminalRegion delta := by
  rintro x ⟨hgap, horder, hu, hsumLower, hsumUpper, hsquare, hcap⟩
  have hgap' := main005AI_thetaGap_anti h
  have hone := main005AI_thetaOne_mono h
  have htwo := main005AI_thetaTwo_anti h
  exact ⟨hgap'.trans_lt hgap, horder, hu.trans hone,
    htwo.trans_lt hsumLower, by linarith, by linarith, hcap⟩

theorem sectionSixFirstLowCentralLargeBelowRegion_mono
    {epsilon delta : Real} (h : epsilon <= delta) :
    sectionSixFirstLowCentralLargeBelowRegion epsilon ⊆
      sectionSixFirstLowCentralLargeBelowRegion delta := by
  rintro x ⟨hgap, horder, hu, hsumLower, hsumUpper, hsquare,
    hpairCap, hw, hfullCap, hbelow⟩
  have hgap' := main005AI_thetaGap_anti h
  have hone := main005AI_thetaOne_mono h
  have htwo := main005AI_thetaTwo_anti h
  exact ⟨hgap'.trans_lt hgap, horder, hu.trans hone,
    htwo.trans_lt hsumLower, by linarith, by linarith, hpairCap,
    hw, hfullCap, hbelow.trans_le hone⟩

theorem sectionSixFirstLowCentralLargeAboveRegion_mono
    {epsilon delta : Real} (h : epsilon <= delta) :
    sectionSixFirstLowCentralLargeAboveRegion epsilon ⊆
      sectionSixFirstLowCentralLargeAboveRegion delta := by
  rintro x ⟨hgap, horder, hu, hsumLower, hsumUpper, hsquare,
    hpairCap, hw, hfullCap, habove⟩
  have hgap' := main005AI_thetaGap_anti h
  have hone := main005AI_thetaOne_mono h
  have htwo := main005AI_thetaTwo_anti h
  exact ⟨hgap'.trans_lt hgap, horder, hu.trans hone,
    htwo.trans_lt hsumLower, by linarith, by linarith, hpairCap,
    hw, hfullCap, htwo.trans_lt habove⟩

theorem sectionSixFirstLowCentralSmallQuadrupleRegion_subset_uniformOuterRegion
    {epsilon delta : Real} (hepsilon : 0 <= epsilon)
    (h : epsilon <= delta) :
    sectionSixFirstLowCentralSmallQuadrupleRegion epsilon ⊆
      sectionSixFirstLowCentralSmallUniformOuterRegion delta := by
  rintro x ⟨hgap, h01, h12, h23, hu, hsumLower, hsquare,
    hcap, hA, hB, hC, hD, hE⟩
  have hgap' := main005AI_thetaGap_anti h
  have hone := main005AI_thetaOne_mono h
  have htwo := main005AI_thetaTwo_anti h
  refine ⟨hgap'.trans_lt hgap, h01, h12, h23, hu.trans hone,
    htwo.trans_lt hsumLower, ?_, hcap,
    main005AI_not_mem_thetaBand_mono h hA,
    main005AI_not_mem_thetaBand_mono h hB,
    main005AI_not_mem_thetaBand_mono h hC,
    main005AI_not_mem_thetaBand_mono h hD,
    main005AI_not_mem_thetaBand_mono h hE⟩
  simp only [sectionSixThetaOne] at hsquare
  linarith

theorem sectionSixFirstLowBelowQuadrupleRegion_mono
    {epsilon delta : Real} (h : epsilon <= delta) :
    sectionSixFirstLowBelowQuadrupleRegion epsilon ⊆
      sectionSixFirstLowBelowQuadrupleRegion delta := by
  rintro x ⟨hgap, h01, h12, h23, hpair, hA, hB, hC, hD,
    hfullFirst, hfullSecond⟩
  have hgap' := main005AI_thetaGap_anti h
  have hone := main005AI_thetaOne_mono h
  exact ⟨hgap'.trans_lt hgap, h01, h12, h23, hpair.trans_le hone,
    main005AI_not_mem_thetaBand_mono h hA,
    main005AI_not_mem_thetaBand_mono h hB,
    main005AI_not_mem_thetaBand_mono h hC,
    main005AI_not_mem_thetaBand_mono h hD,
    main005AI_not_mem_thetaBand_mono h hfullFirst,
    main005AI_not_mem_complementBand_mono h hfullSecond⟩

theorem sectionSixFirstHighFarRegion_mono
    {epsilon delta : Real} (h : epsilon <= delta) :
    sectionSixFirstHighFarRegion epsilon ⊆
      sectionSixFirstHighFarRegion delta := by
  rintro x ⟨hgap, horder, hu, hhalf, hcap, hsum⟩
  have hgap' := main005AI_thetaGap_anti h
  have hone := main005AI_thetaOne_mono h
  have htwo := main005AI_thetaTwo_anti h
  exact ⟨hgap'.trans_lt hgap, horder, htwo.trans_lt hu, hhalf,
    hcap, by linarith⟩

theorem sectionSixFirstHighCentralLargeRegion_mono
    {epsilon delta : Real} (h : epsilon <= delta) :
    sectionSixFirstHighCentralLargeRegion epsilon ⊆
      sectionSixFirstHighCentralLargeRegion delta := by
  rintro x ⟨hgap, horder, hu, hhalf, hcap, hsumLower,
    hsumUpper, hsquare⟩
  have hgap' := main005AI_thetaGap_anti h
  have hone := main005AI_thetaOne_mono h
  have htwo := main005AI_thetaTwo_anti h
  exact ⟨hgap'.trans_lt hgap, horder, htwo.trans_lt hu, hhalf,
    hcap, htwo.trans_lt hsumLower, by linarith, by linarith⟩

theorem sectionSixFirstHighCentralSmallQuadrupleRegion_subset_uniformOuterRegion
    {epsilon delta : Real} (hepsilon : 0 <= epsilon)
    (h : epsilon <= delta) :
    sectionSixFirstHighCentralSmallQuadrupleRegion epsilon ⊆
      sectionSixFirstHighCentralSmallUniformOuterRegion delta := by
  rintro x ⟨hgap, h01, h12, hu, hhalf, hsquare⟩
  have hgap' := main005AI_thetaGap_anti h
  have htwo := main005AI_thetaTwo_anti h
  refine ⟨hgap'.trans_lt hgap, h01, h12, htwo.trans_lt hu, hhalf, ?_⟩
  simp only [sectionSixThetaOne] at hsquare
  linarith

end PrimesRestrictedDigits
