import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogPair
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The low central-large terminal region

This file defines the exact finite region and rational kernel for Maynard's `I_2` term. The
exact region retains the weak finite-carrier walls; the separate source region records the
literal open domain in the paper.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 141, Eq. (6.9).
-/

open Filter MeasureTheory Set Topology

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralLargeTerminalRegion
    (epsilon : Real) : Set (Real × Real) :=
  {x | sectionSixThetaGap epsilon < x.1 ∧
    x.1 <= x.2 ∧ x.2 <= sectionSixThetaOne epsilon ∧
    sectionSixThetaTwo epsilon < x.2 + x.1 ∧
    x.2 + x.1 < 1 - sectionSixThetaTwo epsilon ∧
    1 - sectionSixThetaOne epsilon <= x.2 + 2 * x.1 ∧
    x.2 + 2 * x.1 <= 1}

def sectionSixFirstLowCentralLargeTerminalSourceRegion
    (epsilon : Real) : Set (Real × Real) :=
  {x | sectionSixThetaGap epsilon < x.1 ∧
    x.1 < x.2 ∧ x.2 < sectionSixThetaOne epsilon ∧
    sectionSixThetaTwo epsilon < x.2 + x.1 ∧
    x.2 + x.1 < 1 - sectionSixThetaTwo epsilon ∧
    1 - sectionSixThetaOne epsilon < x.2 + 2 * x.1 ∧
    x.2 + 2 * x.1 < 1}

private abbrev pairFirst : (Real × Real) →ₗ[Real] Real :=
  LinearMap.fst Real Real Real

private abbrev pairSecond : (Real × Real) →ₗ[Real] Real :=
  LinearMap.snd Real Real Real

private theorem sectionSixFirstLowCentralLargeTerminalRegion_convex
    (epsilon : Real) :
    Convex Real (sectionSixFirstLowCentralLargeTerminalRegion epsilon) := by
  have h :=
    (convex_halfSpace_gt pairFirst.isLinear
      (sectionSixThetaGap epsilon)).inter
      ((convex_halfSpace_le (pairFirst - pairSecond).isLinear 0).inter
        ((convex_halfSpace_le pairSecond.isLinear
          (sectionSixThetaOne epsilon)).inter
          ((convex_halfSpace_gt (pairSecond + pairFirst).isLinear
            (sectionSixThetaTwo epsilon)).inter
            ((convex_halfSpace_lt (pairSecond + pairFirst).isLinear
              (1 - sectionSixThetaTwo epsilon)).inter
              ((convex_halfSpace_ge
                (pairSecond + (2 : Real) • pairFirst).isLinear
                (1 - sectionSixThetaOne epsilon)).inter
                (convex_halfSpace_le
                  (pairSecond + (2 : Real) • pairFirst).isLinear 1))))))
  simpa [sectionSixFirstLowCentralLargeTerminalRegion, pairFirst, pairSecond,
    Set.inter_def, sub_nonpos] using h

theorem measurableSet_sectionSixFirstLowCentralLargeTerminalRegion
    (epsilon : Real) :
    MeasurableSet (sectionSixFirstLowCentralLargeTerminalRegion epsilon) := by
  unfold sectionSixFirstLowCentralLargeTerminalRegion
  measurability

theorem sectionSixFirstLowCentralLargeTerminalRegion_subset_logBox
    (epsilon : Real) (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowCentralLargeTerminalRegion epsilon ⊆
      Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) := by
  intro x hx
  rcases hx with ⟨hgap, horder, hu, _, _, _, _⟩
  have htheta : sectionSixThetaOne epsilon <= 1 / 2 := by
    simp only [sectionSixThetaOne]
    linarith
  exact ⟨⟨hgap, horder.trans (hu.trans htheta)⟩,
    ⟨hgap.trans_le horder, hu.trans htheta⟩⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

theorem volume_frontier_sectionSixFirstLowCentralLargeTerminalRegion
    (epsilon : Real) :
    volume (frontier
      (sectionSixFirstLowCentralLargeTerminalRegion epsilon)) = 0 :=
  (sectionSixFirstLowCentralLargeTerminalRegion_convex epsilon).addHaar_frontier
    volume

noncomputable def sectionSixFirstLowCentralLargeTerminalKernel
    (x : Real × Real) : Real :=
  1 / (x.2 * x.1 * (1 - x.2 - x.1))

noncomputable def sectionSixFirstLowCentralLargeTerminalIntegral
    (epsilon : Real) : Real :=
  ∫ x in sectionSixFirstLowCentralLargeTerminalRegion epsilon,
    sectionSixFirstLowCentralLargeTerminalKernel x

private noncomputable def sectionSixFirstLowCentralLargeTerminalClamp
    (lower t : Real) : Real :=
  max lower t

private noncomputable def sectionSixFirstLowCentralLargeTerminalSafeKernel
    (epsilon : Real) (x : Real × Real) : Real :=
  1 /
    (sectionSixFirstLowCentralLargeTerminalClamp
        (sectionSixThetaGap epsilon) x.2 *
      sectionSixFirstLowCentralLargeTerminalClamp
        (sectionSixThetaGap epsilon) x.1 *
      sectionSixFirstLowCentralLargeTerminalClamp
        (sectionSixThetaTwo epsilon) (1 - x.2 - x.1))

private theorem sectionSixThetaTwo_pos
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    0 < sectionSixThetaTwo epsilon := by
  simp only [sectionSixThetaTwo]
  linarith

private theorem sectionSixFirstLowCentralLargeTerminalSafeKernel_continuous
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    (hthetaTwo : 0 < sectionSixThetaTwo epsilon) :
    Continuous (sectionSixFirstLowCentralLargeTerminalSafeKernel epsilon) := by
  have hu : Continuous (fun x : Real × Real =>
      sectionSixFirstLowCentralLargeTerminalClamp
        (sectionSixThetaGap epsilon) x.2) :=
    continuous_const.max continuous_snd
  have hv : Continuous (fun x : Real × Real =>
      sectionSixFirstLowCentralLargeTerminalClamp
        (sectionSixThetaGap epsilon) x.1) :=
    continuous_const.max continuous_fst
  have hresidual : Continuous (fun x : Real × Real =>
      sectionSixFirstLowCentralLargeTerminalClamp
        (sectionSixThetaTwo epsilon) (1 - x.2 - x.1)) :=
    continuous_const.max
      ((continuous_const.sub continuous_snd).sub continuous_fst)
  exact continuous_const.div ((hu.mul hv).mul hresidual) fun x => by
    have huPos : 0 < sectionSixFirstLowCentralLargeTerminalClamp
        (sectionSixThetaGap epsilon) x.2 :=
      hgap.trans_le (le_max_left _ _)
    have hvPos : 0 < sectionSixFirstLowCentralLargeTerminalClamp
        (sectionSixThetaGap epsilon) x.1 :=
      hgap.trans_le (le_max_left _ _)
    have hresidualPos : 0 < sectionSixFirstLowCentralLargeTerminalClamp
        (sectionSixThetaTwo epsilon) (1 - x.2 - x.1) :=
      hthetaTwo.trans_le (le_max_left _ _)
    exact mul_ne_zero (mul_ne_zero huPos.ne' hvPos.ne') hresidualPos.ne'

private theorem sectionSixFirstLowCentralLargeTerminalSafeKernel_norm_le
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    (hthetaTwo : 0 < sectionSixThetaTwo epsilon) (x : Real × Real) :
    ‖sectionSixFirstLowCentralLargeTerminalSafeKernel epsilon x‖ <=
      1 / (sectionSixThetaGap epsilon * sectionSixThetaGap epsilon *
        sectionSixThetaTwo epsilon) := by
  let u := sectionSixFirstLowCentralLargeTerminalClamp
    (sectionSixThetaGap epsilon) x.2
  let v := sectionSixFirstLowCentralLargeTerminalClamp
    (sectionSixThetaGap epsilon) x.1
  let residual := sectionSixFirstLowCentralLargeTerminalClamp
    (sectionSixThetaTwo epsilon) (1 - x.2 - x.1)
  have hu : sectionSixThetaGap epsilon <= u := le_max_left _ _
  have hv : sectionSixThetaGap epsilon <= v := le_max_left _ _
  have hresidual : sectionSixThetaTwo epsilon <= residual := le_max_left _ _
  have huPos : 0 < u := hgap.trans_le hu
  have hvPos : 0 < v := hgap.trans_le hv
  have hresidualPos : 0 < residual := hthetaTwo.trans_le hresidual
  have hpair : sectionSixThetaGap epsilon * sectionSixThetaGap epsilon <=
      u * v := mul_le_mul hu hv hgap.le huPos.le
  have hdenominator :
      sectionSixThetaGap epsilon * sectionSixThetaGap epsilon *
          sectionSixThetaTwo epsilon <= u * v * residual :=
    mul_le_mul hpair hresidual hthetaTwo.le
      (mul_nonneg huPos.le hvPos.le)
  have hlowerPos : 0 <
      sectionSixThetaGap epsilon * sectionSixThetaGap epsilon *
        sectionSixThetaTwo epsilon :=
    mul_pos (mul_pos hgap hgap) hthetaTwo
  have hdenominatorPos : 0 < u * v * residual :=
    mul_pos (mul_pos huPos hvPos) hresidualPos
  rw [sectionSixFirstLowCentralLargeTerminalSafeKernel, Real.norm_eq_abs,
    abs_of_nonneg (one_div_nonneg.mpr hdenominatorPos.le)]
  exact one_div_le_one_div_of_le hlowerPos hdenominator

noncomputable def sectionSixFirstLowCentralLargeTerminalKernelExtension
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    BoundedContinuousFunction (Real × Real) Real :=
  let hbounds := sectionSix_parameter_bounds hepsilon hepsilonSmall
  let hthetaTwo := sectionSixThetaTwo_pos hepsilon hepsilonSmall
  BoundedContinuousFunction.ofNormedAddCommGroup
    (sectionSixFirstLowCentralLargeTerminalSafeKernel epsilon)
    (sectionSixFirstLowCentralLargeTerminalSafeKernel_continuous epsilon
      hbounds.1 hthetaTwo)
    (1 / (sectionSixThetaGap epsilon * sectionSixThetaGap epsilon *
      sectionSixThetaTwo epsilon))
    (sectionSixFirstLowCentralLargeTerminalSafeKernel_norm_le epsilon
      hbounds.1 hthetaTwo)

private theorem sectionSixFirstLowCentralLargeTerminalSafeKernel_eq
    (epsilon : Real) {x : Real × Real}
    (hfirst : sectionSixThetaGap epsilon < x.1)
    (horder : x.1 <= x.2)
    (hsum : x.2 + x.1 < 1 - sectionSixThetaTwo epsilon) :
    sectionSixFirstLowCentralLargeTerminalSafeKernel epsilon x =
      sectionSixFirstLowCentralLargeTerminalKernel x := by
  have hsecond : sectionSixThetaGap epsilon <= x.2 :=
    hfirst.le.trans horder
  have hresidual : sectionSixThetaTwo epsilon <= 1 - x.2 - x.1 := by
    linarith
  simp only [sectionSixFirstLowCentralLargeTerminalSafeKernel,
    sectionSixFirstLowCentralLargeTerminalKernel,
    sectionSixFirstLowCentralLargeTerminalClamp,
    max_eq_right hsecond, max_eq_right hfirst.le,
    max_eq_right hresidual]

theorem
    sectionSixFirstLowCentralLargeTerminalKernelExtension_eq_on_region
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Set.EqOn
      (sectionSixFirstLowCentralLargeTerminalKernelExtension
        epsilon hepsilon hepsilonSmall)
      sectionSixFirstLowCentralLargeTerminalKernel
      (sectionSixFirstLowCentralLargeTerminalRegion epsilon) := by
  intro x hx
  exact sectionSixFirstLowCentralLargeTerminalSafeKernel_eq epsilon
    hx.1 hx.2.1 hx.2.2.2.2.1

private theorem normalizedPrimeLogPairSum_congr
    (a b : Real) (X : Nat) {region : Set (Real × Real)}
    {f g : Real × Real -> Real} (hfg : Set.EqOn f g region) :
    normalizedPrimeLogPairSum a b X region f =
      normalizedPrimeLogPairSum a b X region g := by
  classical
  unfold normalizedPrimeLogPairSum
  apply Finset.sum_congr rfl
  intro pair hpair
  have hpair' := hpair
  unfold normalizedPrimeLogPairIndices at hpair'
  have hregion := (Finset.mem_filter.mp hpair').2
  rw [hfg hregion]

theorem tendsto_sectionSixFirstLowCentralLargeTerminalKernelSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Tendsto
      (fun length : Nat => normalizedPrimeLogPairSum
        (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
        (sectionSixFirstLowCentralLargeTerminalRegion epsilon)
        sectionSixFirstLowCentralLargeTerminalKernel)
      atTop
      (nhds (sectionSixFirstLowCentralLargeTerminalIntegral epsilon)) := by
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hgapHalf : sectionSixThetaGap epsilon < (1 / 2 : Real) := by
    rw [sectionSixThetaGap_eq]
    linarith
  let extension :=
    sectionSixFirstLowCentralLargeTerminalKernelExtension epsilon hepsilon
      hepsilonSmall
  have hextension :=
    sectionSixFirstLowCentralLargeTerminalKernelExtension_eq_on_region
      epsilon hepsilon hepsilonSmall
  have hlimit := tendsto_normalizedPrimeLogPairSum_powTen hgap hgapHalf
    (measurableSet_sectionSixFirstLowCentralLargeTerminalRegion epsilon)
    (sectionSixFirstLowCentralLargeTerminalRegion_subset_logBox epsilon
      hepsilonSmall)
    (volume_frontier_sectionSixFirstLowCentralLargeTerminalRegion epsilon)
    extension
  have hintegral :
      (∫ x in sectionSixFirstLowCentralLargeTerminalRegion epsilon,
          extension x) =
        sectionSixFirstLowCentralLargeTerminalIntegral epsilon := by
    unfold sectionSixFirstLowCentralLargeTerminalIntegral
    exact setIntegral_congr_fun
      (measurableSet_sectionSixFirstLowCentralLargeTerminalRegion epsilon)
      fun x hx => hextension hx
  rw [hintegral] at hlimit
  apply hlimit.congr'
  filter_upwards [] with length
  exact normalizedPrimeLogPairSum_congr _ _ _ hextension

end

end PrimesRestrictedDigits
