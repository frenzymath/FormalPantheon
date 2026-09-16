import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogFourfold
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallQuadrupleRegions
import Mathlib.Analysis.Convex.Measure
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum

/-!
# Convergence for the low central-small clean quadruple term

The exact `I_5` region is an eight-wall convex core intersected with the complements of five
closed pair-product slabs. This file proves its normalized prime-log kernel sum converges to
the exact-region integral.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12) and `R_3`.
-/

open Filter MeasureTheory Set Topology

namespace PrimesRestrictedDigits

noncomputable section

private abbrev lowQuadrupleTriple :
    (((Real × Real) × Real) × Real) →ₗ[Real] ((Real × Real) × Real) :=
  LinearMap.fst Real ((Real × Real) × Real) Real

private abbrev lowQuadruplePair :
    (((Real × Real) × Real) × Real) →ₗ[Real] (Real × Real) :=
  (LinearMap.fst Real (Real × Real) Real).comp lowQuadrupleTriple

private abbrev lowQuadrupleU :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.fst Real Real Real).comp lowQuadruplePair

private abbrev lowQuadrupleV :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real Real Real).comp lowQuadruplePair

private abbrev lowQuadrupleW :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real (Real × Real) Real).comp lowQuadrupleTriple

private abbrev lowQuadrupleT :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  LinearMap.snd Real ((Real × Real) × Real) Real

private def sectionSixFirstLowCentralSmallQuadrupleCore
    (epsilon : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.2 ∧
    x.2 <= x.1.2 ∧
    x.1.2 <= x.1.1.2 ∧
    x.1.1.2 <= x.1.1.1 ∧
    x.1.1.1 <= sectionSixThetaOne epsilon ∧
    sectionSixThetaTwo epsilon < x.1.1.1 + x.1.1.2 ∧
    x.1.1.1 + 2 * x.1.1.2 < 1 - sectionSixThetaOne epsilon ∧
    x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1}

private def sectionSixFirstLowCentralSmallQuadrupleBand
    (epsilon : Real)
    (f : (((Real × Real) × Real) × Real) →ₗ[Real] Real) :
    Set (((Real × Real) × Real) × Real) :=
  {x | f x ∈ Set.Icc
    (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)}

private theorem sectionSixFirstLowCentralSmallQuadrupleCore_convex
    (epsilon : Real) :
    Convex Real (sectionSixFirstLowCentralSmallQuadrupleCore epsilon) := by
  have h :=
    (convex_halfSpace_gt lowQuadrupleT.isLinear
      (sectionSixThetaGap epsilon)).inter
      ((convex_halfSpace_le (lowQuadrupleT - lowQuadrupleW).isLinear 0).inter
        ((convex_halfSpace_le (lowQuadrupleW - lowQuadrupleV).isLinear 0).inter
          ((convex_halfSpace_le (lowQuadrupleV - lowQuadrupleU).isLinear 0).inter
            ((convex_halfSpace_le lowQuadrupleU.isLinear
              (sectionSixThetaOne epsilon)).inter
              ((convex_halfSpace_gt
                (lowQuadrupleU + lowQuadrupleV).isLinear
                (sectionSixThetaTwo epsilon)).inter
                ((convex_halfSpace_lt
                  (lowQuadrupleU + (2 : Real) • lowQuadrupleV).isLinear
                  (1 - sectionSixThetaOne epsilon)).inter
                  (convex_halfSpace_le
                    (lowQuadrupleU + lowQuadrupleV + lowQuadrupleW +
                      (2 : Real) • lowQuadrupleT).isLinear 1)))))))
  simpa [sectionSixFirstLowCentralSmallQuadrupleCore, lowQuadrupleU,
    lowQuadrupleV, lowQuadrupleW, lowQuadrupleT, lowQuadruplePair,
    lowQuadrupleTriple, Set.inter_def, sub_nonpos] using h

private theorem sectionSixFirstLowCentralSmallQuadrupleBand_convex
    (epsilon : Real)
    (f : (((Real × Real) × Real) × Real) →ₗ[Real] Real) :
    Convex Real (sectionSixFirstLowCentralSmallQuadrupleBand epsilon f) := by
  have h :=
    (convex_halfSpace_ge f.isLinear (sectionSixThetaOne epsilon)).inter
      (convex_halfSpace_le f.isLinear (sectionSixThetaTwo epsilon))
  simpa [sectionSixFirstLowCentralSmallQuadrupleBand, Set.inter_def] using h

private theorem measurableSet_sectionSixFirstLowCentralSmallQuadrupleRegion
    (epsilon : Real) :
    MeasurableSet (sectionSixFirstLowCentralSmallQuadrupleRegion epsilon) := by
  unfold sectionSixFirstLowCentralSmallQuadrupleRegion
  measurability

private theorem sectionSixFirstLowCentralSmallQuadrupleRegion_eq_inter
    (epsilon : Real) :
    sectionSixFirstLowCentralSmallQuadrupleRegion epsilon =
      (((((sectionSixFirstLowCentralSmallQuadrupleCore epsilon ∩
        (sectionSixFirstLowCentralSmallQuadrupleBand epsilon
          (lowQuadrupleU + lowQuadrupleW))ᶜ) ∩
        (sectionSixFirstLowCentralSmallQuadrupleBand epsilon
          (lowQuadrupleU + lowQuadrupleT))ᶜ) ∩
        (sectionSixFirstLowCentralSmallQuadrupleBand epsilon
          (lowQuadrupleV + lowQuadrupleW))ᶜ) ∩
        (sectionSixFirstLowCentralSmallQuadrupleBand epsilon
          (lowQuadrupleV + lowQuadrupleT))ᶜ) ∩
        (sectionSixFirstLowCentralSmallQuadrupleBand epsilon
          (lowQuadrupleW + lowQuadrupleT))ᶜ) := by
  ext x
  simp [sectionSixFirstLowCentralSmallQuadrupleRegion,
    sectionSixFirstLowCentralSmallQuadrupleCore,
    sectionSixFirstLowCentralSmallQuadrupleBand, lowQuadrupleU,
    lowQuadrupleV, lowQuadrupleW, lowQuadrupleT, lowQuadruplePair,
    lowQuadrupleTriple, and_assoc]

local instance sectionSixFirstLowCentralSmallQuadruplePairHaar :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstLowCentralSmallQuadrupleTripleHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Real × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstLowCentralSmallQuadrupleFourfoldHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure (((Real × Real) × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

private theorem volume_frontier_sectionSixFirstLowCentralSmallQuadrupleBand_compl
    (epsilon : Real)
    (f : (((Real × Real) × Real) × Real) →ₗ[Real] Real) :
    volume (frontier
      (sectionSixFirstLowCentralSmallQuadrupleBand epsilon f)ᶜ) = 0 := by
  rw [frontier_compl]
  exact (sectionSixFirstLowCentralSmallQuadrupleBand_convex epsilon f)
    |>.addHaar_frontier volume

private theorem volume_frontier_sectionSixFirstLowCentralSmallQuadrupleRegion
    (epsilon : Real) :
    volume (frontier
      (sectionSixFirstLowCentralSmallQuadrupleRegion epsilon)) = 0 := by
  rw [sectionSixFirstLowCentralSmallQuadrupleRegion_eq_inter]
  apply null_frontier_inter
  · apply null_frontier_inter
    · apply null_frontier_inter
      · apply null_frontier_inter
        · apply null_frontier_inter
          · exact (sectionSixFirstLowCentralSmallQuadrupleCore_convex epsilon)
              |>.addHaar_frontier volume
          · exact
              volume_frontier_sectionSixFirstLowCentralSmallQuadrupleBand_compl
                epsilon (lowQuadrupleU + lowQuadrupleW)
        · exact
            volume_frontier_sectionSixFirstLowCentralSmallQuadrupleBand_compl
              epsilon (lowQuadrupleU + lowQuadrupleT)
      · exact
          volume_frontier_sectionSixFirstLowCentralSmallQuadrupleBand_compl
            epsilon (lowQuadrupleV + lowQuadrupleW)
    · exact
        volume_frontier_sectionSixFirstLowCentralSmallQuadrupleBand_compl
          epsilon (lowQuadrupleV + lowQuadrupleT)
  · exact
      volume_frontier_sectionSixFirstLowCentralSmallQuadrupleBand_compl
        epsilon (lowQuadrupleW + lowQuadrupleT)

private theorem sectionSixFirstLowCentralSmallQuadrupleRegion_geometry
    (epsilon : Real)
    {x : ((Real × Real) × Real) × Real}
    (hx : x ∈ sectionSixFirstLowCentralSmallQuadrupleRegion epsilon) :
    x ∈ (((Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon)
        (sectionSixThetaOne epsilon)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon)
        (sectionSixThetaOne epsilon)) ∧
      x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1 := by
  rcases hx with
    ⟨htGap, htw, hwv, hvu, huTheta, _hcentral, _hsquare, hcap, _⟩
  refine ⟨?_, hcap⟩
  exact ⟨⟨⟨⟨htGap.trans_le (htw.trans (hwv.trans hvu)), huTheta⟩,
      ⟨htGap.trans_le (htw.trans hwv), hvu.trans huTheta⟩⟩,
      ⟨htGap.trans_le htw, hwv.trans (hvu.trans huTheta)⟩⟩,
    ⟨htGap, htw.trans (hwv.trans (hvu.trans huTheta))⟩⟩

private theorem sectionSixFirstLowCentralSmallQuadrupleRegion_subset_logBox
    (epsilon : Real) :
    sectionSixFirstLowCentralSmallQuadrupleRegion epsilon ⊆
      (((Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon)
          (sectionSixThetaOne epsilon)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon)
        (sectionSixThetaOne epsilon)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon)
        (sectionSixThetaOne epsilon)) := by
  intro x hx
  exact (sectionSixFirstLowCentralSmallQuadrupleRegion_geometry epsilon hx).1

private noncomputable def sectionSixFirstLowCentralSmallQuadrupleClamp
    (epsilon t : Real) : Real :=
  max (sectionSixThetaGap epsilon) (min (sectionSixThetaOne epsilon) t)

private noncomputable def sectionSixFirstLowCentralSmallQuadrupleSafeArgument
    (epsilon : Real) (x : ((Real × Real) × Real) × Real) : Real :=
  max 1 ((1 - sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.1.1 -
    sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.1.2 -
    sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.2 -
    sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.2) /
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.2)

private noncomputable def sectionSixFirstLowCentralSmallQuadrupleSafeKernel
    (epsilon : Real) (x : ((Real × Real) × Real) × Real) : Real :=
  buchstabFunction
      (sectionSixFirstLowCentralSmallQuadrupleSafeArgument epsilon x) /
    (((sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.1.1 *
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.1.2) *
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.2) *
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.2 ^ 2)

private theorem sectionSixFirstLowCentralSmallQuadrupleSafeKernel_continuous
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon) :
    Continuous (sectionSixFirstLowCentralSmallQuadrupleSafeKernel epsilon) := by
  have hu : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.1.1) :=
    continuous_const.max (continuous_const.min continuous_fst.fst.fst)
  have hv : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.1.2) :=
    continuous_const.max (continuous_const.min continuous_fst.fst.snd)
  have hw : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.2) :=
    continuous_const.max (continuous_const.min continuous_fst.snd)
  have ht : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  have hpos (s : Real) :
      0 < sectionSixFirstLowCentralSmallQuadrupleClamp epsilon s :=
    hgap.trans_le (le_max_left _ _)
  have harg : Continuous
      (sectionSixFirstLowCentralSmallQuadrupleSafeArgument epsilon) := by
    apply continuous_const.max
    exact ((((continuous_const.sub hu).sub hv).sub hw).sub ht).div ht
      (fun x => (hpos x.2).ne')
  have homega : Continuous (fun x : ((Real × Real) × Real) × Real =>
      buchstabFunction
        (sectionSixFirstLowCentralSmallQuadrupleSafeArgument epsilon x)) := by
    apply continuousOn_buchstabFunction.comp_continuous harg
    intro x
    exact le_max_left (1 : Real) _
  exact homega.div (((hu.mul hv).mul hw).mul (ht.pow 2)) fun x =>
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (hpos x.1.1.1).ne' (hpos x.1.1.2).ne')
        (hpos x.1.2).ne')
      (pow_ne_zero _ (hpos x.2).ne')

private theorem sectionSixFirstLowCentralSmallQuadrupleSafeKernel_norm_le
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    (x : ((Real × Real) × Real) × Real) :
    ‖sectionSixFirstLowCentralSmallQuadrupleSafeKernel epsilon x‖ <=
      1 / sectionSixThetaGap epsilon ^ 5 := by
  let u := sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.1.1
  let v := sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.1.2
  let w := sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.2
  let t := sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.2
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
    (show 1 <= sectionSixFirstLowCentralSmallQuadrupleSafeArgument epsilon x
      from le_max_left _ _)
  have homegaNonneg : 0 <= buchstabFunction
      (sectionSixFirstLowCentralSmallQuadrupleSafeArgument epsilon x) := by
    linarith [homega.1]
  rw [sectionSixFirstLowCentralSmallQuadrupleSafeKernel, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg homegaNonneg hdenPos.le)]
  exact div_le_div₀ (by norm_num) homega.2 hgapFifth hden

private noncomputable def sectionSixFirstLowCentralSmallQuadrupleKernelExtension
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    BoundedContinuousFunction (((Real × Real) × Real) × Real) Real :=
  let hgap := (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  BoundedContinuousFunction.ofNormedAddCommGroup
    (sectionSixFirstLowCentralSmallQuadrupleSafeKernel epsilon)
    (sectionSixFirstLowCentralSmallQuadrupleSafeKernel_continuous epsilon hgap)
    (1 / sectionSixThetaGap epsilon ^ 5)
    (sectionSixFirstLowCentralSmallQuadrupleSafeKernel_norm_le epsilon hgap)

private theorem sectionSixFirstLowCentralSmallQuadrupleSafeKernel_eq
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
    sectionSixFirstLowCentralSmallQuadrupleSafeKernel epsilon x =
      sectionSixFirstLowCentralSmallQuadrupleKernel x := by
  have htPos : 0 < x.2 := hgap.trans hbox.2.1
  have hclampU :
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.1.1 =
        x.1.1.1 := by
    rw [sectionSixFirstLowCentralSmallQuadrupleClamp,
      min_eq_right hbox.1.1.1.2, max_eq_right hbox.1.1.1.1.le]
  have hclampV :
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.1.2 =
        x.1.1.2 := by
    rw [sectionSixFirstLowCentralSmallQuadrupleClamp,
      min_eq_right hbox.1.1.2.2, max_eq_right hbox.1.1.2.1.le]
  have hclampW :
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.1.2 = x.1.2 := by
    rw [sectionSixFirstLowCentralSmallQuadrupleClamp,
      min_eq_right hbox.1.2.2, max_eq_right hbox.1.2.1.le]
  have hclampT :
      sectionSixFirstLowCentralSmallQuadrupleClamp epsilon x.2 = x.2 := by
    rw [sectionSixFirstLowCentralSmallQuadrupleClamp,
      min_eq_right hbox.2.2, max_eq_right hbox.2.1.le]
  have harg :
      1 <= (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
    rw [le_div_iff₀ htPos]
    linarith
  simp [sectionSixFirstLowCentralSmallQuadrupleSafeKernel,
    sectionSixFirstLowCentralSmallQuadrupleSafeArgument,
    sectionSixFirstLowCentralSmallQuadrupleKernel, hclampU, hclampV,
    hclampW, hclampT, max_eq_right harg]

private theorem
    sectionSixFirstLowCentralSmallQuadrupleKernelExtension_eq_on_region
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Set.EqOn
      (sectionSixFirstLowCentralSmallQuadrupleKernelExtension epsilon
        hepsilon hepsilonSmall)
      sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixFirstLowCentralSmallQuadrupleRegion epsilon) := by
  intro x hx
  have hgeometry :=
    sectionSixFirstLowCentralSmallQuadrupleRegion_geometry epsilon hx
  exact sectionSixFirstLowCentralSmallQuadrupleSafeKernel_eq epsilon
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
    hgeometry.1 hgeometry.2

theorem tendsto_sectionSixFirstLowCentralSmallQuadrupleKernelSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Tendsto
      (fun length : Nat => normalizedPrimeLogFourfoldSum
        (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)
        (10 ^ length)
        (sectionSixFirstLowCentralSmallQuadrupleRegion epsilon)
        sectionSixFirstLowCentralSmallQuadrupleKernel)
      atTop
      (nhds (sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon)) := by
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hgapTheta :
      sectionSixThetaGap epsilon < sectionSixThetaOne epsilon := by
    rw [sectionSixThetaGap_eq]
    simp only [sectionSixThetaOne]
    linarith
  let extension :=
    sectionSixFirstLowCentralSmallQuadrupleKernelExtension epsilon hepsilon
      hepsilonSmall
  have hextension :=
    sectionSixFirstLowCentralSmallQuadrupleKernelExtension_eq_on_region
      epsilon hepsilon hepsilonSmall
  have hlimit := tendsto_normalizedPrimeLogFourfoldSum_powTen hgap hgapTheta
    (measurableSet_sectionSixFirstLowCentralSmallQuadrupleRegion epsilon)
    (sectionSixFirstLowCentralSmallQuadrupleRegion_subset_logBox epsilon)
    (volume_frontier_sectionSixFirstLowCentralSmallQuadrupleRegion epsilon)
    extension
  have hintegral :
      (∫ x in sectionSixFirstLowCentralSmallQuadrupleRegion epsilon,
          extension x) =
        sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon := by
    unfold sectionSixFirstLowCentralSmallQuadrupleIntegral
    exact setIntegral_congr_fun
      (measurableSet_sectionSixFirstLowCentralSmallQuadrupleRegion epsilon)
      fun x hx => hextension hx
  rw [hintegral] at hlimit
  apply hlimit.congr'
  filter_upwards [] with length
  exact normalizedPrimeLogFourfoldSum_congr _ _ _ hextension

end

end PrimesRestrictedDigits
