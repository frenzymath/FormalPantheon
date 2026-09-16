import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogFourfold
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleRegions
import Mathlib.Analysis.Convex.Measure
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum

/-!
# Convergence for the low-below clean quadruple term

The exact `I_6` region is a five-wall convex core intersected with the complements of six
closed product slabs. This file proves its normalized prime-log kernel sum converges to the
exact-region integral.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.13) and `R_4`.
-/

open Filter MeasureTheory Set Topology

namespace PrimesRestrictedDigits

noncomputable section

private abbrev lowBelowQuadrupleTriple :
    (((Real × Real) × Real) × Real) →ₗ[Real] ((Real × Real) × Real) :=
  LinearMap.fst Real ((Real × Real) × Real) Real

private abbrev lowBelowQuadruplePair :
    (((Real × Real) × Real) × Real) →ₗ[Real] (Real × Real) :=
  (LinearMap.fst Real (Real × Real) Real).comp lowBelowQuadrupleTriple

private abbrev lowBelowQuadrupleU :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.fst Real Real Real).comp lowBelowQuadruplePair

private abbrev lowBelowQuadrupleV :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real Real Real).comp lowBelowQuadruplePair

private abbrev lowBelowQuadrupleW :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real (Real × Real) Real).comp lowBelowQuadrupleTriple

private abbrev lowBelowQuadrupleT :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  LinearMap.snd Real ((Real × Real) × Real) Real

private def sectionSixFirstLowBelowQuadrupleCore
    (epsilon : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.2 ∧
    x.2 <= x.1.2 ∧
    x.1.2 <= x.1.1.2 ∧
    x.1.1.2 <= x.1.1.1 ∧
    x.1.1.1 + x.1.1.2 < sectionSixThetaOne epsilon}

private def sectionSixFirstLowBelowQuadrupleBand
    (lower upper : Real)
    (f : (((Real × Real) × Real) × Real) →ₗ[Real] Real) :
    Set (((Real × Real) × Real) × Real) :=
  {x | f x ∈ Set.Icc lower upper}

private theorem sectionSixFirstLowBelowQuadrupleCore_convex
    (epsilon : Real) :
    Convex Real (sectionSixFirstLowBelowQuadrupleCore epsilon) := by
  have h :=
    (convex_halfSpace_gt lowBelowQuadrupleT.isLinear
      (sectionSixThetaGap epsilon)).inter
      ((convex_halfSpace_le
        (lowBelowQuadrupleT - lowBelowQuadrupleW).isLinear 0).inter
        ((convex_halfSpace_le
          (lowBelowQuadrupleW - lowBelowQuadrupleV).isLinear 0).inter
          ((convex_halfSpace_le
            (lowBelowQuadrupleV - lowBelowQuadrupleU).isLinear 0).inter
            (convex_halfSpace_lt
              (lowBelowQuadrupleU + lowBelowQuadrupleV).isLinear
              (sectionSixThetaOne epsilon)))))
  simpa [sectionSixFirstLowBelowQuadrupleCore, lowBelowQuadrupleU,
    lowBelowQuadrupleV, lowBelowQuadrupleW, lowBelowQuadrupleT,
    lowBelowQuadruplePair, lowBelowQuadrupleTriple, Set.inter_def,
    sub_nonpos] using h

private theorem sectionSixFirstLowBelowQuadrupleBand_convex
    (lower upper : Real)
    (f : (((Real × Real) × Real) × Real) →ₗ[Real] Real) :
    Convex Real (sectionSixFirstLowBelowQuadrupleBand lower upper f) := by
  have h :=
    (convex_halfSpace_ge f.isLinear lower).inter
      (convex_halfSpace_le f.isLinear upper)
  simpa [sectionSixFirstLowBelowQuadrupleBand, Set.inter_def] using h

private theorem measurableSet_sectionSixFirstLowBelowQuadrupleRegion
    (epsilon : Real) :
    MeasurableSet (sectionSixFirstLowBelowQuadrupleRegion epsilon) := by
  unfold sectionSixFirstLowBelowQuadrupleRegion
  measurability

private theorem sectionSixFirstLowBelowQuadrupleRegion_eq_inter
    (epsilon : Real) :
    sectionSixFirstLowBelowQuadrupleRegion epsilon =
      ((((((sectionSixFirstLowBelowQuadrupleCore epsilon ∩
        (sectionSixFirstLowBelowQuadrupleBand
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
          (lowBelowQuadrupleU + lowBelowQuadrupleV +
            lowBelowQuadrupleW))ᶜ) ∩
        (sectionSixFirstLowBelowQuadrupleBand
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
          (lowBelowQuadrupleU + lowBelowQuadrupleV +
            lowBelowQuadrupleT))ᶜ) ∩
        (sectionSixFirstLowBelowQuadrupleBand
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
          (lowBelowQuadrupleU + lowBelowQuadrupleW +
            lowBelowQuadrupleT))ᶜ) ∩
        (sectionSixFirstLowBelowQuadrupleBand
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
          (lowBelowQuadrupleV + lowBelowQuadrupleW +
            lowBelowQuadrupleT))ᶜ) ∩
        (sectionSixFirstLowBelowQuadrupleBand
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
          (lowBelowQuadrupleU + lowBelowQuadrupleV +
            lowBelowQuadrupleW + lowBelowQuadrupleT))ᶜ) ∩
        (sectionSixFirstLowBelowQuadrupleBand
          (1 - sectionSixThetaTwo epsilon)
          (1 - sectionSixThetaOne epsilon)
          (lowBelowQuadrupleU + lowBelowQuadrupleV +
            lowBelowQuadrupleW + lowBelowQuadrupleT))ᶜ) := by
  ext x
  simp [sectionSixFirstLowBelowQuadrupleRegion,
    sectionSixFirstLowBelowQuadrupleCore,
    sectionSixFirstLowBelowQuadrupleBand, lowBelowQuadrupleU,
    lowBelowQuadrupleV, lowBelowQuadrupleW, lowBelowQuadrupleT,
    lowBelowQuadruplePair, lowBelowQuadrupleTriple, and_assoc]

local instance sectionSixFirstLowBelowQuadruplePairHaar :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstLowBelowQuadrupleTripleHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Real × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstLowBelowQuadrupleFourfoldHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure (((Real × Real) × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

private theorem volume_frontier_sectionSixFirstLowBelowQuadrupleBand_compl
    (lower upper : Real)
    (f : (((Real × Real) × Real) × Real) →ₗ[Real] Real) :
    volume (frontier
      (sectionSixFirstLowBelowQuadrupleBand lower upper f)ᶜ) = 0 := by
  rw [frontier_compl]
  exact (sectionSixFirstLowBelowQuadrupleBand_convex lower upper f)
    |>.addHaar_frontier volume

private theorem volume_frontier_sectionSixFirstLowBelowQuadrupleRegion
    (epsilon : Real) :
    volume (frontier (sectionSixFirstLowBelowQuadrupleRegion epsilon)) = 0 := by
  rw [sectionSixFirstLowBelowQuadrupleRegion_eq_inter]
  apply null_frontier_inter
  · apply null_frontier_inter
    · apply null_frontier_inter
      · apply null_frontier_inter
        · apply null_frontier_inter
          · apply null_frontier_inter
            · exact (sectionSixFirstLowBelowQuadrupleCore_convex epsilon)
                |>.addHaar_frontier volume
            · exact
                volume_frontier_sectionSixFirstLowBelowQuadrupleBand_compl
                  (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
                  (lowBelowQuadrupleU + lowBelowQuadrupleV +
                    lowBelowQuadrupleW)
          · exact
              volume_frontier_sectionSixFirstLowBelowQuadrupleBand_compl
                (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
                (lowBelowQuadrupleU + lowBelowQuadrupleV +
                  lowBelowQuadrupleT)
        · exact
            volume_frontier_sectionSixFirstLowBelowQuadrupleBand_compl
              (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
              (lowBelowQuadrupleU + lowBelowQuadrupleW +
                lowBelowQuadrupleT)
      · exact
          volume_frontier_sectionSixFirstLowBelowQuadrupleBand_compl
            (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
            (lowBelowQuadrupleV + lowBelowQuadrupleW + lowBelowQuadrupleT)
    · exact
        volume_frontier_sectionSixFirstLowBelowQuadrupleBand_compl
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
          (lowBelowQuadrupleU + lowBelowQuadrupleV + lowBelowQuadrupleW +
            lowBelowQuadrupleT)
  · exact
      volume_frontier_sectionSixFirstLowBelowQuadrupleBand_compl
        (1 - sectionSixThetaTwo epsilon) (1 - sectionSixThetaOne epsilon)
        (lowBelowQuadrupleU + lowBelowQuadrupleV + lowBelowQuadrupleW +
          lowBelowQuadrupleT)

private theorem sectionSixFirstLowBelowQuadrupleRegion_geometry
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {x : ((Real × Real) × Real) × Real}
    (hx : x ∈ sectionSixFirstLowBelowQuadrupleRegion epsilon) :
    x ∈ (((Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon)
        (sectionSixThetaOne epsilon)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon)
        (sectionSixThetaOne epsilon)) ∧
      x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1 := by
  rcases hx with ⟨htGap, htw, hwv, hvu, huvTheta, _⟩
  have hvPos : 0 < x.1.1.2 :=
    hgap.trans htGap |>.trans_le (htw.trans hwv)
  have huTheta : x.1.1.1 < sectionSixThetaOne epsilon := by
    linarith
  have hcap : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1 := by
    simp only [sectionSixThetaOne] at huvTheta
    linarith
  refine ⟨?_, hcap⟩
  exact ⟨⟨⟨⟨htGap.trans_le (htw.trans (hwv.trans hvu)), huTheta.le⟩,
      ⟨htGap.trans_le (htw.trans hwv), (hvu.trans_lt huTheta).le⟩⟩,
      ⟨htGap.trans_le htw, hwv.trans (hvu.trans_lt huTheta).le⟩⟩,
    ⟨htGap, htw.trans (hwv.trans (hvu.trans_lt huTheta).le)⟩⟩

private theorem sectionSixFirstLowBelowQuadrupleRegion_subset_logBox
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowBelowQuadrupleRegion epsilon ⊆
      (((Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon)
        (sectionSixThetaOne epsilon)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon)
        (sectionSixThetaOne epsilon)) := by
  intro x hx
  exact (sectionSixFirstLowBelowQuadrupleRegion_geometry epsilon hgap
    hepsilonSmall hx).1

private noncomputable def sectionSixFirstLowBelowQuadrupleClamp
    (epsilon t : Real) : Real :=
  max (sectionSixThetaGap epsilon) (min (sectionSixThetaOne epsilon) t)

private noncomputable def sectionSixFirstLowBelowQuadrupleSafeArgument
    (epsilon : Real) (x : ((Real × Real) × Real) × Real) : Real :=
  max 1 ((1 - sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.1.1 -
    sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.1.2 -
    sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.2 -
    sectionSixFirstLowBelowQuadrupleClamp epsilon x.2) /
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.2)

private noncomputable def sectionSixFirstLowBelowQuadrupleSafeKernel
    (epsilon : Real) (x : ((Real × Real) × Real) × Real) : Real :=
  buchstabFunction
      (sectionSixFirstLowBelowQuadrupleSafeArgument epsilon x) /
    (((sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.1.1 *
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.1.2) *
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.2) *
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.2 ^ 2)

private theorem sectionSixFirstLowBelowQuadrupleSafeKernel_continuous
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon) :
    Continuous (sectionSixFirstLowBelowQuadrupleSafeKernel epsilon) := by
  have hu : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.1.1) :=
    continuous_const.max (continuous_const.min continuous_fst.fst.fst)
  have hv : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.1.2) :=
    continuous_const.max (continuous_const.min continuous_fst.fst.snd)
  have hw : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.2) :=
    continuous_const.max (continuous_const.min continuous_fst.snd)
  have ht : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  have hpos (s : Real) :
      0 < sectionSixFirstLowBelowQuadrupleClamp epsilon s :=
    hgap.trans_le (le_max_left _ _)
  have harg : Continuous
      (sectionSixFirstLowBelowQuadrupleSafeArgument epsilon) := by
    apply continuous_const.max
    exact ((((continuous_const.sub hu).sub hv).sub hw).sub ht).div ht
      (fun x => (hpos x.2).ne')
  have homega : Continuous (fun x : ((Real × Real) × Real) × Real =>
      buchstabFunction
        (sectionSixFirstLowBelowQuadrupleSafeArgument epsilon x)) := by
    apply continuousOn_buchstabFunction.comp_continuous harg
    intro x
    exact le_max_left (1 : Real) _
  exact homega.div (((hu.mul hv).mul hw).mul (ht.pow 2)) fun x =>
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (hpos x.1.1.1).ne' (hpos x.1.1.2).ne')
        (hpos x.1.2).ne')
      (pow_ne_zero _ (hpos x.2).ne')

private theorem sectionSixFirstLowBelowQuadrupleSafeKernel_norm_le
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    (x : ((Real × Real) × Real) × Real) :
    ‖sectionSixFirstLowBelowQuadrupleSafeKernel epsilon x‖ <=
      1 / sectionSixThetaGap epsilon ^ 5 := by
  let u := sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.1.1
  let v := sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.1.2
  let w := sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.2
  let t := sectionSixFirstLowBelowQuadrupleClamp epsilon x.2
  have hu : sectionSixThetaGap epsilon <= u := le_max_left _ _
  have hv : sectionSixThetaGap epsilon <= v := le_max_left _ _
  have hw : sectionSixThetaGap epsilon <= w := le_max_left _ _
  have ht : sectionSixThetaGap epsilon <= t := le_max_left _ _
  have huPos : 0 < u := hgap.trans_le hu
  have hvPos : 0 < v := hgap.trans_le hv
  have hwPos : 0 < w := hgap.trans_le hw
  have htPos : 0 < t := hgap.trans_le ht
  have huv : sectionSixThetaGap epsilon ^ 2 <= u * v := by
    simpa [pow_two] using mul_le_mul hu hv hgap.le huPos.le
  have huvw : sectionSixThetaGap epsilon ^ 3 <= (u * v) * w := by
    calc
      sectionSixThetaGap epsilon ^ 3 =
          sectionSixThetaGap epsilon ^ 2 * sectionSixThetaGap epsilon := by ring
      _ <= (u * v) * w :=
        mul_le_mul huv hw hgap.le (mul_nonneg huPos.le hvPos.le)
  have htSq : sectionSixThetaGap epsilon ^ 2 <= t ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hgap.le ht
  have hden : sectionSixThetaGap epsilon ^ 5 <= ((u * v) * w) * t ^ 2 := by
    calc
      sectionSixThetaGap epsilon ^ 5 =
          sectionSixThetaGap epsilon ^ 3 *
            sectionSixThetaGap epsilon ^ 2 := by ring
      _ <= ((u * v) * w) * t ^ 2 :=
        mul_le_mul huvw htSq (sq_nonneg _)
          (mul_nonneg (mul_nonneg huPos.le hvPos.le) hwPos.le)
  have hdenPos : 0 < ((u * v) * w) * t ^ 2 :=
    mul_pos (mul_pos (mul_pos huPos hvPos) hwPos) (sq_pos_of_pos htPos)
  have hgapFifth : 0 < sectionSixThetaGap epsilon ^ 5 := pow_pos hgap _
  have homega := buchstabFunction_mem_Icc
    (show 1 <= sectionSixFirstLowBelowQuadrupleSafeArgument epsilon x from
      le_max_left _ _)
  have homegaNonneg : 0 <= buchstabFunction
      (sectionSixFirstLowBelowQuadrupleSafeArgument epsilon x) := by
    linarith [homega.1]
  rw [sectionSixFirstLowBelowQuadrupleSafeKernel, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg homegaNonneg hdenPos.le)]
  exact div_le_div₀ (by norm_num) homega.2 hgapFifth hden

private noncomputable def sectionSixFirstLowBelowQuadrupleKernelExtension
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    BoundedContinuousFunction (((Real × Real) × Real) × Real) Real :=
  let hgap := (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  BoundedContinuousFunction.ofNormedAddCommGroup
    (sectionSixFirstLowBelowQuadrupleSafeKernel epsilon)
    (sectionSixFirstLowBelowQuadrupleSafeKernel_continuous epsilon hgap)
    (1 / sectionSixThetaGap epsilon ^ 5)
    (sectionSixFirstLowBelowQuadrupleSafeKernel_norm_le epsilon hgap)

private theorem sectionSixFirstLowBelowQuadrupleSafeKernel_eq
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    {x : ((Real × Real) × Real) × Real}
    (hbox : x ∈ (((Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon)
        (sectionSixThetaOne epsilon)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon)
        (sectionSixThetaOne epsilon)))
    (hcap : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1) :
    sectionSixFirstLowBelowQuadrupleSafeKernel epsilon x =
      sectionSixFirstLowBelowQuadrupleKernel x := by
  have htPos : 0 < x.2 := hgap.trans hbox.2.1
  have hclampU :
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.1.1 = x.1.1.1 := by
    rw [sectionSixFirstLowBelowQuadrupleClamp,
      min_eq_right hbox.1.1.1.2, max_eq_right hbox.1.1.1.1.le]
  have hclampV :
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.1.2 = x.1.1.2 := by
    rw [sectionSixFirstLowBelowQuadrupleClamp,
      min_eq_right hbox.1.1.2.2, max_eq_right hbox.1.1.2.1.le]
  have hclampW :
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.1.2 = x.1.2 := by
    rw [sectionSixFirstLowBelowQuadrupleClamp,
      min_eq_right hbox.1.2.2, max_eq_right hbox.1.2.1.le]
  have hclampT :
      sectionSixFirstLowBelowQuadrupleClamp epsilon x.2 = x.2 := by
    rw [sectionSixFirstLowBelowQuadrupleClamp,
      min_eq_right hbox.2.2, max_eq_right hbox.2.1.le]
  have harg : 1 <= (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
    rw [le_div_iff₀ htPos]
    linarith
  simp [sectionSixFirstLowBelowQuadrupleSafeKernel,
    sectionSixFirstLowBelowQuadrupleSafeArgument,
    sectionSixFirstLowBelowQuadrupleKernel, hclampU, hclampV, hclampW,
    hclampT, max_eq_right harg]

private theorem sectionSixFirstLowBelowQuadrupleKernelExtension_eq_on_region
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Set.EqOn
      (sectionSixFirstLowBelowQuadrupleKernelExtension epsilon hepsilon
        hepsilonSmall)
      sectionSixFirstLowBelowQuadrupleKernel
      (sectionSixFirstLowBelowQuadrupleRegion epsilon) := by
  intro x hx
  have hgap := (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hgeometry :=
    sectionSixFirstLowBelowQuadrupleRegion_geometry epsilon hgap
      hepsilonSmall hx
  exact sectionSixFirstLowBelowQuadrupleSafeKernel_eq epsilon hgap
    hgeometry.1 hgeometry.2.le

theorem tendsto_sectionSixFirstLowBelowQuadrupleKernelSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Tendsto
      (fun length : Nat => normalizedPrimeLogFourfoldSum
        (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)
        (10 ^ length)
        (sectionSixFirstLowBelowQuadrupleRegion epsilon)
        sectionSixFirstLowBelowQuadrupleKernel)
      atTop
      (nhds (sectionSixFirstLowBelowQuadrupleIntegral epsilon)) := by
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hgapTheta :
      sectionSixThetaGap epsilon < sectionSixThetaOne epsilon := by
    rw [sectionSixThetaGap_eq]
    simp only [sectionSixThetaOne]
    linarith
  let extension :=
    sectionSixFirstLowBelowQuadrupleKernelExtension epsilon hepsilon
      hepsilonSmall
  have hextension :=
    sectionSixFirstLowBelowQuadrupleKernelExtension_eq_on_region epsilon
      hepsilon hepsilonSmall
  have hlimit := tendsto_normalizedPrimeLogFourfoldSum_powTen hgap hgapTheta
    (measurableSet_sectionSixFirstLowBelowQuadrupleRegion epsilon)
    (sectionSixFirstLowBelowQuadrupleRegion_subset_logBox epsilon hgap
      hepsilonSmall)
    (volume_frontier_sectionSixFirstLowBelowQuadrupleRegion epsilon)
    extension
  have hintegral :
      (∫ x in sectionSixFirstLowBelowQuadrupleRegion epsilon, extension x) =
        sectionSixFirstLowBelowQuadrupleIntegral epsilon := by
    unfold sectionSixFirstLowBelowQuadrupleIntegral
    exact setIntegral_congr_fun
      (measurableSet_sectionSixFirstLowBelowQuadrupleRegion epsilon)
      fun x hx => hextension hx
  rw [hintegral] at hlimit
  apply hlimit.congr'
  filter_upwards [] with length
  exact normalizedPrimeLogFourfoldSum_congr _ _ _ hextension

end

end PrimesRestrictedDigits
