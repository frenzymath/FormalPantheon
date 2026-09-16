import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogFourfold
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum

/-!
# The high central-small strict quadruple region

This file defines the exact six-wall region and Buchstab kernel for Maynard's `I_9` term. The
weak role and cutoff walls belong to the finite carrier; the separate source region records
the full literal open predicate in the paper.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 145--146, Eq. (6.16).
-/

open Filter MeasureTheory Set Topology

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstHighCentralSmallQuadrupleRegion
    (epsilon : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.2 ∧
    x.2 <= x.1.2 ∧
    x.1.2 <= x.1.1.2 ∧
    sectionSixThetaTwo epsilon < x.1.1.1 ∧
    x.1.1.1 <= (1 / 2 : Real) ∧
    x.1.1.1 + 2 * x.1.1.2 < 1 - sectionSixThetaOne epsilon}

def sectionSixFirstHighCentralSmallQuadrupleSourceRegion
    (epsilon : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.2 ∧
    x.2 < x.1.2 ∧
    x.1.2 < x.1.1.2 ∧
    sectionSixThetaTwo epsilon < x.1.1.1 ∧
    x.1.1.1 < (1 / 2 : Real) ∧
    x.1.1.1 + 2 * x.1.1.2 < 1 - sectionSixThetaOne epsilon ∧
    x.1.1.1 + x.1.1.2 + 2 * x.1.2 < 1 ∧
    x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1 ∧
    sectionSixThetaTwo epsilon < x.1.1.1 + x.1.1.2 ∧
    x.1.1.1 + x.1.1.2 < 1 - sectionSixThetaTwo epsilon ∧
    x.1.1.1 + x.1.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.1 + x.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.1 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.2 + x.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
    x.1.2 + x.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)}

private abbrev quadrupleTriple :
    (((Real × Real) × Real) × Real) →ₗ[Real] ((Real × Real) × Real) :=
  LinearMap.fst Real ((Real × Real) × Real) Real

private abbrev quadruplePair :
    (((Real × Real) × Real) × Real) →ₗ[Real] (Real × Real) :=
  (LinearMap.fst Real (Real × Real) Real).comp quadrupleTriple

private abbrev quadrupleU :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.fst Real Real Real).comp quadruplePair

private abbrev quadrupleV :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real Real Real).comp quadruplePair

private abbrev quadrupleW :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real (Real × Real) Real).comp quadrupleTriple

private abbrev quadrupleT :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  LinearMap.snd Real ((Real × Real) × Real) Real

private theorem sectionSixFirstHighCentralSmallQuadrupleRegion_convex
    (epsilon : Real) :
    Convex Real (sectionSixFirstHighCentralSmallQuadrupleRegion epsilon) := by
  have h :=
    (convex_halfSpace_gt quadrupleT.isLinear
      (sectionSixThetaGap epsilon)).inter
      ((convex_halfSpace_le (quadrupleT - quadrupleW).isLinear 0).inter
        ((convex_halfSpace_le (quadrupleW - quadrupleV).isLinear 0).inter
          ((convex_halfSpace_gt quadrupleU.isLinear
            (sectionSixThetaTwo epsilon)).inter
            ((convex_halfSpace_le quadrupleU.isLinear (1 / 2)).inter
              (convex_halfSpace_lt
                (quadrupleU + (2 : Real) • quadrupleV).isLinear
                (1 - sectionSixThetaOne epsilon))))))
  simpa [sectionSixFirstHighCentralSmallQuadrupleRegion, quadrupleU,
    quadrupleV, quadrupleW, quadrupleT, quadruplePair, quadrupleTriple,
    Set.inter_def, sub_nonpos] using h

private theorem measurableSet_sectionSixFirstHighCentralSmallQuadrupleRegion
    (epsilon : Real) :
    MeasurableSet
      (sectionSixFirstHighCentralSmallQuadrupleRegion epsilon) := by
  unfold sectionSixFirstHighCentralSmallQuadrupleRegion
  measurability

private theorem
    sectionSixFirstHighCentralSmallQuadrupleRegion_derived_geometry
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {x : ((Real × Real) × Real) × Real}
    (hx : x ∈ sectionSixFirstHighCentralSmallQuadrupleRegion epsilon) :
    x.1.1.2 < x.1.1.1 ∧
      x.1.1.1 + x.1.1.2 + 2 * x.1.2 < 1 ∧
      x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1 ∧
      sectionSixThetaTwo epsilon < x.1.1.1 + x.1.1.2 ∧
      x.1.1.1 + x.1.1.2 < 1 - sectionSixThetaTwo epsilon ∧
      x.1.1.1 + x.1.1.2 ∉
        Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
      x.1.1.1 + x.1.2 ∉
        Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
      x.1.1.1 + x.2 ∉
        Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
      x.1.1.2 + x.1.2 ∉
        Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
      x.1.1.2 + x.2 ∉
        Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ∧
      x.1.2 + x.2 ∉
        Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) := by
  rcases hx with ⟨htGap, htw, hwv, huTheta, _huHalf, hsquare⟩
  have hgapPos : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have htPos : 0 < x.2 := hgapPos.trans htGap
  have hwPos : 0 < x.1.2 := htPos.trans_le htw
  have hvPos : 0 < x.1.1.2 := hwPos.trans_le hwv
  have hvGap : sectionSixThetaGap epsilon < x.1.1.2 :=
    htGap.trans_le (htw.trans hwv)
  have hvThetaTwo : x.1.1.2 < sectionSixThetaTwo epsilon := by
    simp only [sectionSixThetaOne, sectionSixThetaTwo] at huTheta hsquare ⊢
    linarith
  have hvU : x.1.1.2 < x.1.1.1 := hvThetaTwo.trans huTheta
  have htwoVThetaOne :
      2 * x.1.1.2 < sectionSixThetaOne epsilon := by
    simp only [sectionSixThetaOne, sectionSixThetaTwo] at huTheta hsquare ⊢
    linarith
  have hvThetaOne : x.1.1.2 < sectionSixThetaOne epsilon := by
    linarith
  have hcapW : x.1.1.1 + x.1.1.2 + 2 * x.1.2 < 1 := by
    linarith
  have hcapT :
      x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1 := by
    linarith
  have hcentralLower :
      sectionSixThetaTwo epsilon < x.1.1.1 + x.1.1.2 := by
    linarith
  have hcentralUpper :
      x.1.1.1 + x.1.1.2 < 1 - sectionSixThetaTwo epsilon := by
    unfold sectionSixThetaGap at hvGap
    linarith
  refine ⟨hvU, hcapW, hcapT, hcentralLower, hcentralUpper,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro hmem
    rcases hmem with ⟨hlower, hupper⟩
    linarith

private theorem sectionSixFirstHighCentralSmallQuadrupleRegion_geometry
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {x : ((Real × Real) × Real) × Real}
    (hx : x ∈ sectionSixFirstHighCentralSmallQuadrupleRegion epsilon) :
    x ∈ (((Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)) ∧
      x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1 := by
  have hderived :=
    sectionSixFirstHighCentralSmallQuadrupleRegion_derived_geometry epsilon
      hepsilon hepsilonSmall hx
  rcases hx with ⟨htGap, htw, hwv, huTheta, huHalf, hsquare⟩
  have hbounds := sectionSix_parameter_bounds hepsilon hepsilonSmall
  have huGap : sectionSixThetaGap epsilon < x.1.1.1 := by
    unfold sectionSixThetaGap
    linarith [hbounds.2.1]
  have hvHalf : x.1.1.2 < (1 / 2 : Real) := by
    simp only [sectionSixThetaOne, sectionSixThetaTwo] at huTheta hsquare ⊢
    linarith
  have htwoVThetaOne :
      2 * x.1.1.2 < sectionSixThetaOne epsilon := by
    simp only [sectionSixThetaOne, sectionSixThetaTwo] at huTheta hsquare ⊢
    linarith
  refine ⟨?_, hderived.2.2.1⟩
  exact ⟨⟨⟨⟨huGap, huHalf⟩,
      ⟨htGap.trans_le (htw.trans hwv), hvHalf.le⟩⟩,
      ⟨htGap.trans_le htw, hwv.trans hvHalf.le⟩⟩,
    ⟨htGap, htw.trans (hwv.trans hvHalf.le)⟩⟩

private theorem
    sectionSixFirstHighCentralSmallQuadrupleRegion_subset_logBox
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstHighCentralSmallQuadrupleRegion epsilon ⊆
      (((Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)) := by
  intro x hx
  exact (sectionSixFirstHighCentralSmallQuadrupleRegion_geometry epsilon
    hepsilon hepsilonSmall hx).1

local instance sectionSixFirstHighCentralSmallQuadruplePairHaar :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstHighCentralSmallQuadrupleTripleHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Real × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstHighCentralSmallQuadrupleFourfoldHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure (((Real × Real) × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

private theorem volume_frontier_sectionSixFirstHighCentralSmallQuadrupleRegion
    (epsilon : Real) :
    volume (frontier
      (sectionSixFirstHighCentralSmallQuadrupleRegion epsilon)) = 0 :=
  (sectionSixFirstHighCentralSmallQuadrupleRegion_convex epsilon)
    |>.addHaar_frontier volume

noncomputable def sectionSixFirstHighCentralSmallQuadrupleKernel
    (x : (((Real × Real) × Real) × Real)) : Real :=
  buchstabFunction
      ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) /
    (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2)

noncomputable def sectionSixFirstHighCentralSmallQuadrupleIntegral
    (epsilon : Real) : Real :=
  ∫ x in sectionSixFirstHighCentralSmallQuadrupleRegion epsilon,
    sectionSixFirstHighCentralSmallQuadrupleKernel x

private noncomputable def sectionSixFirstHighCentralSmallQuadrupleClamp
    (epsilon t : Real) : Real :=
  max (sectionSixThetaGap epsilon) (min (1 / 2) t)

private noncomputable def
    sectionSixFirstHighCentralSmallQuadrupleSafeArgument
    (epsilon : Real) (x : ((Real × Real) × Real) × Real) : Real :=
  max 1 ((1 - sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.1.1 -
    sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.1.2 -
    sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.2 -
    sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.2) /
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.2)

private noncomputable def sectionSixFirstHighCentralSmallQuadrupleSafeKernel
    (epsilon : Real) (x : ((Real × Real) × Real) × Real) : Real :=
  buchstabFunction
      (sectionSixFirstHighCentralSmallQuadrupleSafeArgument epsilon x) /
    (((sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.1.1 *
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.1.2) *
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.2) *
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.2 ^ 2)

private theorem sectionSixFirstHighCentralSmallQuadrupleSafeKernel_continuous
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon) :
    Continuous
      (sectionSixFirstHighCentralSmallQuadrupleSafeKernel epsilon) := by
  have hu : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.1.1) :=
    continuous_const.max (continuous_const.min continuous_fst.fst.fst)
  have hv : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.1.2) :=
    continuous_const.max (continuous_const.min continuous_fst.fst.snd)
  have hw : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.2) :=
    continuous_const.max (continuous_const.min continuous_fst.snd)
  have ht : Continuous (fun x : ((Real × Real) × Real) × Real =>
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  have hpos (s : Real) :
      0 < sectionSixFirstHighCentralSmallQuadrupleClamp epsilon s :=
    hgap.trans_le (le_max_left _ _)
  have harg : Continuous
      (sectionSixFirstHighCentralSmallQuadrupleSafeArgument epsilon) := by
    apply continuous_const.max
    exact ((((continuous_const.sub hu).sub hv).sub hw).sub ht).div ht
      (fun x => (hpos x.2).ne')
  have homega : Continuous (fun x : ((Real × Real) × Real) × Real =>
      buchstabFunction
        (sectionSixFirstHighCentralSmallQuadrupleSafeArgument epsilon x)) := by
    apply continuousOn_buchstabFunction.comp_continuous harg
    intro x
    exact le_max_left (1 : Real) _
  exact homega.div (((hu.mul hv).mul hw).mul (ht.pow 2)) fun x =>
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (hpos x.1.1.1).ne' (hpos x.1.1.2).ne')
        (hpos x.1.2).ne')
      (pow_ne_zero _ (hpos x.2).ne')

private theorem sectionSixFirstHighCentralSmallQuadrupleSafeKernel_norm_le
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    (x : ((Real × Real) × Real) × Real) :
    ‖sectionSixFirstHighCentralSmallQuadrupleSafeKernel epsilon x‖ <=
      1 / sectionSixThetaGap epsilon ^ 5 := by
  let u := sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.1.1
  let v := sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.1.2
  let w := sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.2
  let t := sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.2
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
    (show 1 <= sectionSixFirstHighCentralSmallQuadrupleSafeArgument epsilon x
      from le_max_left _ _)
  have homegaNonneg : 0 <= buchstabFunction
      (sectionSixFirstHighCentralSmallQuadrupleSafeArgument epsilon x) := by
    linarith [homega.1]
  rw [sectionSixFirstHighCentralSmallQuadrupleSafeKernel, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg homegaNonneg hdenPos.le)]
  exact div_le_div₀ (by norm_num) homega.2 hgapFifth hden

private noncomputable def
    sectionSixFirstHighCentralSmallQuadrupleKernelExtension
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    BoundedContinuousFunction (((Real × Real) × Real) × Real) Real :=
  let hgap := (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  BoundedContinuousFunction.ofNormedAddCommGroup
    (sectionSixFirstHighCentralSmallQuadrupleSafeKernel epsilon)
    (sectionSixFirstHighCentralSmallQuadrupleSafeKernel_continuous epsilon hgap)
    (1 / sectionSixThetaGap epsilon ^ 5)
    (sectionSixFirstHighCentralSmallQuadrupleSafeKernel_norm_le epsilon hgap)

private theorem sectionSixFirstHighCentralSmallQuadrupleSafeKernel_eq
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    {x : ((Real × Real) × Real) × Real}
    (hbox : x ∈ (((Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)) ×ˢ
      Set.Ioc (sectionSixThetaGap epsilon) (1 / 2)))
    (hcap : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1) :
    sectionSixFirstHighCentralSmallQuadrupleSafeKernel epsilon x =
      sectionSixFirstHighCentralSmallQuadrupleKernel x := by
  have htPos : 0 < x.2 := hgap.trans hbox.2.1
  have hclampU :
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.1.1 =
        x.1.1.1 := by
    rw [sectionSixFirstHighCentralSmallQuadrupleClamp,
      min_eq_right hbox.1.1.1.2, max_eq_right hbox.1.1.1.1.le]
  have hclampV :
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.1.2 =
        x.1.1.2 := by
    rw [sectionSixFirstHighCentralSmallQuadrupleClamp,
      min_eq_right hbox.1.1.2.2, max_eq_right hbox.1.1.2.1.le]
  have hclampW :
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.1.2 = x.1.2 := by
    rw [sectionSixFirstHighCentralSmallQuadrupleClamp,
      min_eq_right hbox.1.2.2, max_eq_right hbox.1.2.1.le]
  have hclampT :
      sectionSixFirstHighCentralSmallQuadrupleClamp epsilon x.2 = x.2 := by
    rw [sectionSixFirstHighCentralSmallQuadrupleClamp,
      min_eq_right hbox.2.2, max_eq_right hbox.2.1.le]
  have harg :
      1 <= (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
    rw [le_div_iff₀ htPos]
    linarith
  simp [sectionSixFirstHighCentralSmallQuadrupleSafeKernel,
    sectionSixFirstHighCentralSmallQuadrupleSafeArgument,
    sectionSixFirstHighCentralSmallQuadrupleKernel, hclampU, hclampV,
    hclampW, hclampT, max_eq_right harg]

private theorem
    sectionSixFirstHighCentralSmallQuadrupleKernelExtension_eq_on_region
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Set.EqOn
      (sectionSixFirstHighCentralSmallQuadrupleKernelExtension epsilon
        hepsilon hepsilonSmall)
      sectionSixFirstHighCentralSmallQuadrupleKernel
      (sectionSixFirstHighCentralSmallQuadrupleRegion epsilon) := by
  intro x hx
  have hgeometry :=
    sectionSixFirstHighCentralSmallQuadrupleRegion_geometry epsilon
      hepsilon hepsilonSmall hx
  exact sectionSixFirstHighCentralSmallQuadrupleSafeKernel_eq epsilon
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
    hgeometry.1 hgeometry.2

theorem tendsto_sectionSixFirstHighCentralSmallQuadrupleKernelSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Tendsto
      (fun length : Nat => normalizedPrimeLogFourfoldSum
        (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
        (sectionSixFirstHighCentralSmallQuadrupleRegion epsilon)
        sectionSixFirstHighCentralSmallQuadrupleKernel)
      atTop
      (nhds (sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon)) := by
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hgapHalf : sectionSixThetaGap epsilon < (1 / 2 : Real) := by
    rw [sectionSixThetaGap_eq]
    linarith
  let extension :=
    sectionSixFirstHighCentralSmallQuadrupleKernelExtension epsilon hepsilon
      hepsilonSmall
  have hextension :=
    sectionSixFirstHighCentralSmallQuadrupleKernelExtension_eq_on_region
      epsilon hepsilon hepsilonSmall
  have hlimit := tendsto_normalizedPrimeLogFourfoldSum_powTen hgap hgapHalf
    (measurableSet_sectionSixFirstHighCentralSmallQuadrupleRegion epsilon)
    (sectionSixFirstHighCentralSmallQuadrupleRegion_subset_logBox epsilon
      hepsilon hepsilonSmall)
    (volume_frontier_sectionSixFirstHighCentralSmallQuadrupleRegion epsilon)
    extension
  have hintegral :
      (∫ x in sectionSixFirstHighCentralSmallQuadrupleRegion epsilon,
          extension x) =
        sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon := by
    unfold sectionSixFirstHighCentralSmallQuadrupleIntegral
    exact setIntegral_congr_fun
      (measurableSet_sectionSixFirstHighCentralSmallQuadrupleRegion epsilon)
      fun x hx => hextension hx
  rw [hintegral] at hlimit
  apply hlimit.congr'
  filter_upwards [] with length
  exact normalizedPrimeLogFourfoldSum_congr _ _ _ hextension

end

end PrimesRestrictedDigits
