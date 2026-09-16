import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogTriple
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The low central-large below-band region

This file defines the exact finite region and Buchstab kernel for Maynard's `I_3` term. The
exact region keeps the weak walls of the finite continuation carrier; the separate source
region records the five literal open walls.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.10).
-/

open Filter MeasureTheory Set Topology

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralLargeBelowRegion
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
    x.1.2 + x.2 < sectionSixThetaOne epsilon}

def sectionSixFirstLowCentralLargeBelowSourceRegion
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
    x.1.2 + x.2 < sectionSixThetaOne epsilon}

private abbrev triplePair : ((Real × Real) × Real) →ₗ[Real] Real × Real :=
  LinearMap.fst Real (Real × Real) Real

private abbrev tripleU : ((Real × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.fst Real Real Real).comp triplePair

private abbrev tripleV : ((Real × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real Real Real).comp triplePair

private abbrev tripleW : ((Real × Real) × Real) →ₗ[Real] Real :=
  LinearMap.snd Real (Real × Real) Real

private theorem sectionSixFirstLowCentralLargeBelowRegion_convex
    (epsilon : Real) :
    Convex Real (sectionSixFirstLowCentralLargeBelowRegion epsilon) := by
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
                      (convex_halfSpace_lt
                        (tripleV + tripleW).isLinear
                        (sectionSixThetaOne epsilon))))))))))
  simpa [sectionSixFirstLowCentralLargeBelowRegion, tripleU, tripleV, tripleW,
    triplePair, Set.inter_def, sub_nonpos] using h

theorem measurableSet_sectionSixFirstLowCentralLargeBelowRegion
    (epsilon : Real) :
    MeasurableSet (sectionSixFirstLowCentralLargeBelowRegion epsilon) := by
  unfold sectionSixFirstLowCentralLargeBelowRegion
  measurability

theorem sectionSixFirstLowCentralLargeBelowRegion_strict_data
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {x : (Real × Real) × Real}
    (hx : x ∈ sectionSixFirstLowCentralLargeBelowRegion epsilon) :
    x.1.2 < x.1.1 ∧ x.2 < x.1.1 ∧
      x.1.1 + 2 * x.1.2 < 1 := by
  rcases hx with ⟨hgap, _horder, _hu, hsumLower, _hsumUpper,
    _hsquareLower, _hsquareUpper, hvw, hcap, hbelow⟩
  have hgapPos : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have htheta : sectionSixThetaOne epsilon < sectionSixThetaTwo epsilon := by
    rw [← sub_pos]
    exact hgapPos
  have hwu : x.2 < x.1.1 := by
    linarith
  refine ⟨hvw.trans hwu, hwu, ?_⟩
  linarith

theorem sectionSixFirstLowCentralLargeBelowRegion_subset_logBox
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowCentralLargeBelowRegion epsilon ⊆
      (Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)) ×ˢ
          Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) := by
  intro x hx
  rcases hx with ⟨hgap, horder, hu, _, _, _, _, hvw, hcap, _⟩
  have hgapPos : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have htheta : sectionSixThetaOne epsilon <= 1 / 2 := by
    simp only [sectionSixThetaOne]
    linarith
  have hvPos : 0 < x.1.2 := hgapPos.trans hgap
  have huHalf : x.1.1 <= 1 / 2 := hu.trans htheta
  have hvHalf : x.1.2 <= 1 / 2 := horder.trans huHalf
  have hwHalf : x.2 <= 1 / 2 := by
    linarith
  exact ⟨⟨⟨hgap.trans_le horder, huHalf⟩, ⟨hgap, hvHalf⟩⟩,
    ⟨hgap.trans hvw, hwHalf⟩⟩

local instance sectionSixFirstLowCentralLargeBelowPairHaar :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstLowCentralLargeBelowTripleHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Real × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

theorem volume_frontier_sectionSixFirstLowCentralLargeBelowRegion
    (epsilon : Real) :
    volume (frontier
      (sectionSixFirstLowCentralLargeBelowRegion epsilon)) = 0 :=
  (sectionSixFirstLowCentralLargeBelowRegion_convex epsilon).addHaar_frontier
    volume

noncomputable def sectionSixFirstLowCentralLargeBelowKernel
    (x : (Real × Real) × Real) : Real :=
  buchstabFunction ((1 - x.1.1 - x.1.2 - x.2) / x.2) /
    (x.1.1 * x.1.2 * x.2 ^ 2)

noncomputable def sectionSixFirstLowCentralLargeBelowIntegral
    (epsilon : Real) : Real :=
  ∫ x in sectionSixFirstLowCentralLargeBelowRegion epsilon,
    sectionSixFirstLowCentralLargeBelowKernel x

private noncomputable def sectionSixFirstLowCentralLargeBelowClamp
    (epsilon t : Real) : Real :=
  max (sectionSixThetaGap epsilon) (min (1 / 2) t)

private noncomputable def sectionSixFirstLowCentralLargeBelowSafeArgument
    (epsilon : Real) (x : (Real × Real) × Real) : Real :=
  max 1 ((1 - sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.1 -
    sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.2 -
    sectionSixFirstLowCentralLargeBelowClamp epsilon x.2) /
      sectionSixFirstLowCentralLargeBelowClamp epsilon x.2)

private noncomputable def sectionSixFirstLowCentralLargeBelowSafeKernel
    (epsilon : Real) (x : (Real × Real) × Real) : Real :=
  buchstabFunction
      (sectionSixFirstLowCentralLargeBelowSafeArgument epsilon x) /
    (sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.1 *
      sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.2 *
        sectionSixFirstLowCentralLargeBelowClamp epsilon x.2 ^ 2)

private theorem sectionSixFirstLowCentralLargeBelowSafeKernel_continuous
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon) :
    Continuous (sectionSixFirstLowCentralLargeBelowSafeKernel epsilon) := by
  have hu : Continuous (fun x : (Real × Real) × Real =>
      sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.1) :=
    continuous_const.max (continuous_const.min continuous_fst.fst)
  have hv : Continuous (fun x : (Real × Real) × Real =>
      sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.2) :=
    continuous_const.max (continuous_const.min continuous_fst.snd)
  have hw : Continuous (fun x : (Real × Real) × Real =>
      sectionSixFirstLowCentralLargeBelowClamp epsilon x.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  have hwPos (x : (Real × Real) × Real) :
      0 < sectionSixFirstLowCentralLargeBelowClamp epsilon x.2 :=
    hgap.trans_le (le_max_left _ _)
  have harg : Continuous
      (sectionSixFirstLowCentralLargeBelowSafeArgument epsilon) := by
    apply continuous_const.max
    exact (((continuous_const.sub hu).sub hv).sub hw).div hw
      (fun x => (hwPos x).ne')
  have homega : Continuous (fun x : (Real × Real) × Real =>
      buchstabFunction
        (sectionSixFirstLowCentralLargeBelowSafeArgument epsilon x)) := by
    apply continuousOn_buchstabFunction.comp_continuous harg
    intro x
    exact le_max_left (1 : Real) _
  have huPos (x : (Real × Real) × Real) :
      0 < sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.1 :=
    hgap.trans_le (le_max_left _ _)
  have hvPos (x : (Real × Real) × Real) :
      0 < sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.2 :=
    hgap.trans_le (le_max_left _ _)
  exact homega.div ((hu.mul hv).mul (hw.pow 2)) fun x =>
    mul_ne_zero (mul_ne_zero (huPos x).ne' (hvPos x).ne')
      (pow_ne_zero _ (hwPos x).ne')

private theorem sectionSixFirstLowCentralLargeBelowSafeKernel_norm_le
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    (x : (Real × Real) × Real) :
    ‖sectionSixFirstLowCentralLargeBelowSafeKernel epsilon x‖ <=
      1 / sectionSixThetaGap epsilon ^ 4 := by
  let u := sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.1
  let v := sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.2
  let w := sectionSixFirstLowCentralLargeBelowClamp epsilon x.2
  have hu : sectionSixThetaGap epsilon <= u := le_max_left _ _
  have hv : sectionSixThetaGap epsilon <= v := le_max_left _ _
  have hw : sectionSixThetaGap epsilon <= w := le_max_left _ _
  have huPos : 0 < u := hgap.trans_le hu
  have hvPos : 0 < v := hgap.trans_le hv
  have hwPos : 0 < w := hgap.trans_le hw
  have huv : sectionSixThetaGap epsilon ^ 2 <= u * v := by
    simpa [pow_two] using mul_le_mul hu hv hgap.le huPos.le
  have hwSq : sectionSixThetaGap epsilon ^ 2 <= w ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hgap.le hw
  have hden : sectionSixThetaGap epsilon ^ 4 <= u * v * w ^ 2 := by
    calc
      sectionSixThetaGap epsilon ^ 4 =
          sectionSixThetaGap epsilon ^ 2 *
            sectionSixThetaGap epsilon ^ 2 := by ring
      _ <= u * v * w ^ 2 :=
        mul_le_mul huv hwSq (sq_nonneg _) (mul_nonneg huPos.le hvPos.le)
  have hdenPos : 0 < u * v * w ^ 2 :=
    mul_pos (mul_pos huPos hvPos) (sq_pos_of_pos hwPos)
  have hgapFourth : 0 < sectionSixThetaGap epsilon ^ 4 := pow_pos hgap _
  have homega := buchstabFunction_mem_Icc
    (show 1 <= sectionSixFirstLowCentralLargeBelowSafeArgument epsilon x from
      le_max_left _ _)
  have homegaNonneg : 0 <= buchstabFunction
      (sectionSixFirstLowCentralLargeBelowSafeArgument epsilon x) := by
    linarith [homega.1]
  rw [sectionSixFirstLowCentralLargeBelowSafeKernel, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg homegaNonneg hdenPos.le)]
  exact div_le_div₀ (by norm_num) homega.2 hgapFourth hden

noncomputable def sectionSixFirstLowCentralLargeBelowKernelExtension
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    BoundedContinuousFunction ((Real × Real) × Real) Real :=
  let hgap := (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  BoundedContinuousFunction.ofNormedAddCommGroup
    (sectionSixFirstLowCentralLargeBelowSafeKernel epsilon)
    (sectionSixFirstLowCentralLargeBelowSafeKernel_continuous epsilon hgap)
    (1 / sectionSixThetaGap epsilon ^ 4)
    (sectionSixFirstLowCentralLargeBelowSafeKernel_norm_le epsilon hgap)

private theorem sectionSixFirstLowCentralLargeBelowSafeKernel_eq
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    {x : (Real × Real) × Real}
    (huBox : x.1.1 ∈ Set.Ioc (sectionSixThetaGap epsilon) (1 / 2))
    (hvBox : x.1.2 ∈ Set.Ioc (sectionSixThetaGap epsilon) (1 / 2))
    (hwBox : x.2 ∈ Set.Ioc (sectionSixThetaGap epsilon) (1 / 2))
    (hcap : x.1.1 + x.1.2 + 2 * x.2 <= 1) :
    sectionSixFirstLowCentralLargeBelowSafeKernel epsilon x =
      sectionSixFirstLowCentralLargeBelowKernel x := by
  have hwPos : 0 < x.2 := hgap.trans hwBox.1
  have hclampU :
      sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.1 = x.1.1 := by
    rw [sectionSixFirstLowCentralLargeBelowClamp,
      min_eq_right huBox.2, max_eq_right huBox.1.le]
  have hclampV :
      sectionSixFirstLowCentralLargeBelowClamp epsilon x.1.2 = x.1.2 := by
    rw [sectionSixFirstLowCentralLargeBelowClamp,
      min_eq_right hvBox.2, max_eq_right hvBox.1.le]
  have hclampW :
      sectionSixFirstLowCentralLargeBelowClamp epsilon x.2 = x.2 := by
    rw [sectionSixFirstLowCentralLargeBelowClamp,
      min_eq_right hwBox.2, max_eq_right hwBox.1.le]
  have harg : 1 <= (1 - x.1.1 - x.1.2 - x.2) / x.2 := by
    rw [le_div_iff₀ hwPos]
    linarith
  simp [sectionSixFirstLowCentralLargeBelowSafeKernel,
    sectionSixFirstLowCentralLargeBelowSafeArgument,
    sectionSixFirstLowCentralLargeBelowKernel, hclampU, hclampV, hclampW,
    max_eq_right harg]

theorem sectionSixFirstLowCentralLargeKernelExtension_eq
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {x : (Real × Real) × Real}
    (huBox : x.1.1 ∈ Set.Ioc (sectionSixThetaGap epsilon) (1 / 2))
    (hvBox : x.1.2 ∈ Set.Ioc (sectionSixThetaGap epsilon) (1 / 2))
    (hwBox : x.2 ∈ Set.Ioc (sectionSixThetaGap epsilon) (1 / 2))
    (hcap : x.1.1 + x.1.2 + 2 * x.2 <= 1) :
    sectionSixFirstLowCentralLargeBelowKernelExtension
        epsilon hepsilon hepsilonSmall x =
      sectionSixFirstLowCentralLargeBelowKernel x := by
  exact sectionSixFirstLowCentralLargeBelowSafeKernel_eq epsilon
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
    huBox hvBox hwBox hcap

theorem sectionSixFirstLowCentralLargeBelowKernelExtension_eq_on_region
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Set.EqOn
      (sectionSixFirstLowCentralLargeBelowKernelExtension
        epsilon hepsilon hepsilonSmall)
      sectionSixFirstLowCentralLargeBelowKernel
      (sectionSixFirstLowCentralLargeBelowRegion epsilon) := by
  intro x hx
  have hbox := sectionSixFirstLowCentralLargeBelowRegion_subset_logBox
    epsilon hepsilon hepsilonSmall hx
  exact sectionSixFirstLowCentralLargeBelowSafeKernel_eq epsilon
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
    hbox.1.1 hbox.1.2 hbox.2 hx.2.2.2.2.2.2.2.2.1

theorem tendsto_sectionSixFirstLowCentralLargeBelowKernelSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Tendsto
      (fun length : Nat => normalizedPrimeLogTripleSum
        (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
        (sectionSixFirstLowCentralLargeBelowRegion epsilon)
        sectionSixFirstLowCentralLargeBelowKernel)
      atTop
      (nhds (sectionSixFirstLowCentralLargeBelowIntegral epsilon)) := by
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hgapHalf : sectionSixThetaGap epsilon < (1 / 2 : Real) := by
    rw [sectionSixThetaGap_eq]
    linarith
  let extension := sectionSixFirstLowCentralLargeBelowKernelExtension
    epsilon hepsilon hepsilonSmall
  have hextension :=
    sectionSixFirstLowCentralLargeBelowKernelExtension_eq_on_region
      epsilon hepsilon hepsilonSmall
  have hlimit := tendsto_normalizedPrimeLogTripleSum_powTen hgap hgapHalf
    (measurableSet_sectionSixFirstLowCentralLargeBelowRegion epsilon)
    (sectionSixFirstLowCentralLargeBelowRegion_subset_logBox
      epsilon hepsilon hepsilonSmall)
    (volume_frontier_sectionSixFirstLowCentralLargeBelowRegion epsilon)
    extension
  have hintegral :
      (∫ x in sectionSixFirstLowCentralLargeBelowRegion epsilon,
          extension x) =
        sectionSixFirstLowCentralLargeBelowIntegral epsilon := by
    unfold sectionSixFirstLowCentralLargeBelowIntegral
    exact setIntegral_congr_fun
      (measurableSet_sectionSixFirstLowCentralLargeBelowRegion epsilon)
      fun x hx => hextension hx
  rw [hintegral] at hlimit
  apply hlimit.congr'
  filter_upwards [] with length
  exact normalizedPrimeLogTripleSum_congr _ _ _ hextension

end

end PrimesRestrictedDigits
