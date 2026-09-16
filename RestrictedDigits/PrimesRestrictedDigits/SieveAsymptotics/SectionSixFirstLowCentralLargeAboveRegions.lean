import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowRegions

/-!
# The low central-large above-band region

This file defines the exact finite region and Buchstab kernel for Maynard's `I_4` term. The
exact region keeps the weak walls of the finite continuation carrier; the separate source
region records the five literal open walls.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.11).
-/

open Filter MeasureTheory Set Topology

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralLargeAboveRegion
    (epsilon : Real) : Set ((Real × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.1.2 ∧
    x.1.2 <= x.1.1 ∧
    x.1.1 <= sectionSixThetaOne epsilon ∧
    sectionSixThetaTwo epsilon < x.1.1 + x.1.2 ∧
    x.1.1 + x.1.2 < 1 - sectionSixThetaTwo epsilon ∧
    1 - sectionSixThetaOne epsilon <= x.1.1 + 2 * x.1.2 ∧
    x.1.1 + 2 * x.1.2 <= 1 ∧
    x.1.2 < x.2 ∧
    x.1.1 + x.1.2 + 2 * x.2 <= 1 ∧
    sectionSixThetaTwo epsilon < x.1.2 + x.2}

def sectionSixFirstLowCentralLargeAboveSourceRegion
    (epsilon : Real) : Set ((Real × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.1.2 ∧
    x.1.2 < x.1.1 ∧
    x.1.1 < sectionSixThetaOne epsilon ∧
    sectionSixThetaTwo epsilon < x.1.1 + x.1.2 ∧
    x.1.1 + x.1.2 < 1 - sectionSixThetaTwo epsilon ∧
    1 - sectionSixThetaOne epsilon < x.1.1 + 2 * x.1.2 ∧
    x.1.1 + 2 * x.1.2 < 1 ∧
    x.1.2 < x.2 ∧
    x.1.1 + x.1.2 + 2 * x.2 < 1 ∧
    sectionSixThetaTwo epsilon < x.1.2 + x.2}

noncomputable def sectionSixFirstLowCentralLargeAboveKernel
    (x : (Real × Real) × Real) : Real :=
  sectionSixFirstLowCentralLargeBelowKernel x

noncomputable def sectionSixFirstLowCentralLargeAboveIntegral
    (epsilon : Real) : Real :=
  ∫ x in sectionSixFirstLowCentralLargeAboveRegion epsilon,
    sectionSixFirstLowCentralLargeAboveKernel x

private abbrev triplePair : ((Real × Real) × Real) →ₗ[Real] Real × Real :=
  LinearMap.fst Real (Real × Real) Real

private abbrev tripleU : ((Real × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.fst Real Real Real).comp triplePair

private abbrev tripleV : ((Real × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real Real Real).comp triplePair

private abbrev tripleW : ((Real × Real) × Real) →ₗ[Real] Real :=
  LinearMap.snd Real (Real × Real) Real

private theorem sectionSixFirstLowCentralLargeAboveRegion_convex
    (epsilon : Real) :
    Convex Real (sectionSixFirstLowCentralLargeAboveRegion epsilon) := by
  have h :=
    (convex_halfSpace_gt tripleV.isLinear
      (sectionSixThetaGap epsilon)).inter
      ((convex_halfSpace_le (tripleV - tripleU).isLinear 0).inter
        ((convex_halfSpace_le tripleU.isLinear
          (sectionSixThetaOne epsilon)).inter
          ((convex_halfSpace_gt (tripleU + tripleV).isLinear
            (sectionSixThetaTwo epsilon)).inter
            ((convex_halfSpace_lt (tripleU + tripleV).isLinear
              (1 - sectionSixThetaTwo epsilon)).inter
              ((convex_halfSpace_ge
                (tripleU + (2 : Real) • tripleV).isLinear
                (1 - sectionSixThetaOne epsilon)).inter
                ((convex_halfSpace_le
                  (tripleU + (2 : Real) • tripleV).isLinear 1).inter
                  ((convex_halfSpace_lt (tripleV - tripleW).isLinear 0).inter
                    ((convex_halfSpace_le
                      (tripleU + tripleV + (2 : Real) • tripleW).isLinear
                      1).inter
                      (convex_halfSpace_gt
                        (tripleV + tripleW).isLinear
                        (sectionSixThetaTwo epsilon))))))))))
  simpa [sectionSixFirstLowCentralLargeAboveRegion, tripleU, tripleV, tripleW,
    triplePair, Set.inter_def, sub_nonpos] using h

theorem sectionSixFirstLowCentralLargeAboveRegion_strict_data
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {x : (Real × Real) × Real}
    (hx : x ∈ sectionSixFirstLowCentralLargeAboveRegion epsilon) :
    x.1.1 + 2 * x.1.2 < 1 ∧ x.1.2 + x.2 <= 1 / 2 := by
  rcases hx with ⟨hgap, horder, _hu, _hsumLower, _hsumUpper,
    _hsquareLower, _hsquareUpper, hvw, hcap, _habove⟩
  have hgapPos : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hvPos : 0 < x.1.2 := hgapPos.trans hgap
  have hwPos : 0 < x.2 := hvPos.trans hvw
  constructor <;> linarith

theorem measurableSet_sectionSixFirstLowCentralLargeAboveRegion
    (epsilon : Real) :
    MeasurableSet (sectionSixFirstLowCentralLargeAboveRegion epsilon) := by
  unfold sectionSixFirstLowCentralLargeAboveRegion
  measurability

theorem sectionSixFirstLowCentralLargeAboveRegion_subset_logBox
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowCentralLargeAboveRegion epsilon ⊆
      (Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)) ×ˢ
          Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) := by
  intro x hx
  have hstrict := sectionSixFirstLowCentralLargeAboveRegion_strict_data
    epsilon hepsilon hepsilonSmall hx
  rcases hx with ⟨hgap, horder, hu, _, _, _, _, hvw, _, _⟩
  have htheta : sectionSixThetaOne epsilon <= 1 / 2 := by
    simp only [sectionSixThetaOne]
    linarith
  have huHalf : x.1.1 <= 1 / 2 := hu.trans htheta
  have hvHalf : x.1.2 <= 1 / 2 := horder.trans huHalf
  have hgapPos : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hvPos : 0 < x.1.2 := hgapPos.trans hgap
  have hwHalf : x.2 <= 1 / 2 := by
    linarith [hstrict.2]
  exact ⟨⟨⟨hgap.trans_le horder, huHalf⟩, ⟨hgap, hvHalf⟩⟩,
    ⟨hgap.trans hvw, hwHalf⟩⟩

local instance sectionSixFirstLowCentralLargeAbovePairHaar :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstLowCentralLargeAboveTripleHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Real × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

theorem volume_frontier_sectionSixFirstLowCentralLargeAboveRegion
    (epsilon : Real) :
    volume (frontier
      (sectionSixFirstLowCentralLargeAboveRegion epsilon)) = 0 :=
  (sectionSixFirstLowCentralLargeAboveRegion_convex epsilon).addHaar_frontier
    volume

theorem sectionSixFirstLowCentralLargeAboveKernelExtension_eq_on_region
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Set.EqOn
      (sectionSixFirstLowCentralLargeBelowKernelExtension
        epsilon hepsilon hepsilonSmall)
      sectionSixFirstLowCentralLargeAboveKernel
      (sectionSixFirstLowCentralLargeAboveRegion epsilon) := by
  intro x hx
  have hbox := sectionSixFirstLowCentralLargeAboveRegion_subset_logBox
    epsilon hepsilon hepsilonSmall hx
  simpa only [sectionSixFirstLowCentralLargeAboveKernel] using
    sectionSixFirstLowCentralLargeKernelExtension_eq epsilon hepsilon
      hepsilonSmall hbox.1.1 hbox.1.2 hbox.2
        hx.2.2.2.2.2.2.2.2.1

theorem tendsto_sectionSixFirstLowCentralLargeAboveKernelSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Tendsto
      (fun length : Nat => normalizedPrimeLogTripleSum
        (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
        (sectionSixFirstLowCentralLargeAboveRegion epsilon)
        sectionSixFirstLowCentralLargeAboveKernel)
      atTop
      (nhds (sectionSixFirstLowCentralLargeAboveIntegral epsilon)) := by
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hgapHalf : sectionSixThetaGap epsilon < (1 / 2 : Real) := by
    rw [sectionSixThetaGap_eq]
    linarith
  let extension := sectionSixFirstLowCentralLargeBelowKernelExtension
    epsilon hepsilon hepsilonSmall
  have hextension :=
    sectionSixFirstLowCentralLargeAboveKernelExtension_eq_on_region
      epsilon hepsilon hepsilonSmall
  have hlimit := tendsto_normalizedPrimeLogTripleSum_powTen hgap hgapHalf
    (measurableSet_sectionSixFirstLowCentralLargeAboveRegion epsilon)
    (sectionSixFirstLowCentralLargeAboveRegion_subset_logBox
      epsilon hepsilon hepsilonSmall)
    (volume_frontier_sectionSixFirstLowCentralLargeAboveRegion epsilon)
    extension
  have hintegral :
      (∫ x in sectionSixFirstLowCentralLargeAboveRegion epsilon,
          extension x) =
        sectionSixFirstLowCentralLargeAboveIntegral epsilon := by
    unfold sectionSixFirstLowCentralLargeAboveIntegral
    exact setIntegral_congr_fun
      (measurableSet_sectionSixFirstLowCentralLargeAboveRegion epsilon)
      fun x hx => hextension hx
  rw [hintegral] at hlimit
  apply hlimit.congr'
  filter_upwards [] with length
  exact normalizedPrimeLogTripleSum_congr _ _ _ hextension

end

end PrimesRestrictedDigits
