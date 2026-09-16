import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Direct pair regions in the first Section 6 decomposition

These are the three pair regions represented directly by the integrals
`I_1`, `I_7`, and `I_8` in Maynard's published paper, pp. 140--146.
The weak finite carriers retain their partition endpoints; the source carriers
below reproduce the literal open integral domains.
-/

open MeasureTheory Set Topology

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowFarRegion (epsilon : Real) : Set (Real × Real) :=
  {x | sectionSixThetaGap epsilon < x.1 ∧
    x.1 <= x.2 ∧ x.2 <= sectionSixThetaOne epsilon ∧
    x.2 + 2 * x.1 <= 1 ∧
    1 - sectionSixThetaOne epsilon < x.2 + x.1}

def sectionSixFirstHighFarRegion (epsilon : Real) : Set (Real × Real) :=
  {x | sectionSixThetaGap epsilon < x.1 ∧
    x.1 <= x.2 ∧ sectionSixThetaTwo epsilon < x.2 ∧
    x.2 <= 1 / 2 ∧ x.2 + 2 * x.1 <= 1 ∧
    1 - sectionSixThetaOne epsilon < x.2 + x.1}

def sectionSixFirstHighCentralLargeRegion (epsilon : Real) : Set (Real × Real) :=
  {x | sectionSixThetaGap epsilon < x.1 ∧
    x.1 <= x.2 ∧ sectionSixThetaTwo epsilon < x.2 ∧
    x.2 <= 1 / 2 ∧ x.2 + 2 * x.1 <= 1 ∧
    sectionSixThetaTwo epsilon < x.2 + x.1 ∧
    x.2 + x.1 < 1 - sectionSixThetaTwo epsilon ∧
    1 - sectionSixThetaOne epsilon <= x.2 + 2 * x.1}

def sectionSixFirstLowFarSourceRegion (epsilon : Real) : Set (Real × Real) :=
  {x | sectionSixThetaGap epsilon < x.1 ∧
    x.1 < x.2 ∧ x.2 < sectionSixThetaOne epsilon ∧
    x.1 < (1 - x.2) / 2 ∧
    1 - sectionSixThetaOne epsilon < x.2 + x.1}

def sectionSixFirstHighFarSourceRegion (epsilon : Real) : Set (Real × Real) :=
  {x | sectionSixThetaTwo epsilon < x.2 ∧ x.2 < 1 / 2 ∧
    sectionSixThetaGap epsilon < x.1 ∧
    x.1 < (1 - x.2) / 2 ∧
    1 - sectionSixThetaOne epsilon < x.2 + x.1}

def sectionSixFirstHighCentralLargeSourceRegion
    (epsilon : Real) : Set (Real × Real) :=
  {x | sectionSixThetaTwo epsilon < x.2 ∧ x.2 < 1 / 2 ∧
    sectionSixThetaGap epsilon < x.1 ∧
    x.1 < (1 - x.2) / 2 ∧
    sectionSixThetaTwo epsilon < x.2 + x.1 ∧
    x.2 + x.1 < 1 - sectionSixThetaTwo epsilon ∧
    1 - sectionSixThetaOne epsilon < x.2 + 2 * x.1}

private abbrev pairFirst : (Real × Real) →ₗ[Real] Real :=
  LinearMap.fst Real Real Real

private abbrev pairSecond : (Real × Real) →ₗ[Real] Real :=
  LinearMap.snd Real Real Real

private theorem sectionSixFirstLowFarRegion_convex (epsilon : Real) :
    Convex Real (sectionSixFirstLowFarRegion epsilon) := by
  have h :=
    (convex_halfSpace_gt pairFirst.isLinear
      (sectionSixThetaGap epsilon)).inter
      ((convex_halfSpace_le (pairFirst - pairSecond).isLinear 0).inter
        ((convex_halfSpace_le pairSecond.isLinear
          (sectionSixThetaOne epsilon)).inter
          ((convex_halfSpace_le
            (pairSecond + (2 : Real) • pairFirst).isLinear 1).inter
            (convex_halfSpace_gt (pairSecond + pairFirst).isLinear
              (1 - sectionSixThetaOne epsilon)))))
  simpa [sectionSixFirstLowFarRegion, pairFirst, pairSecond, Set.inter_def,
    sub_nonpos] using h

private theorem sectionSixFirstHighFarRegion_convex (epsilon : Real) :
    Convex Real (sectionSixFirstHighFarRegion epsilon) := by
  have h :=
    (convex_halfSpace_gt pairFirst.isLinear
      (sectionSixThetaGap epsilon)).inter
      ((convex_halfSpace_le (pairFirst - pairSecond).isLinear 0).inter
        ((convex_halfSpace_gt pairSecond.isLinear
          (sectionSixThetaTwo epsilon)).inter
          ((convex_halfSpace_le pairSecond.isLinear (1 / 2)).inter
            ((convex_halfSpace_le
              (pairSecond + (2 : Real) • pairFirst).isLinear 1).inter
              (convex_halfSpace_gt (pairSecond + pairFirst).isLinear
                (1 - sectionSixThetaOne epsilon))))))
  simpa [sectionSixFirstHighFarRegion, pairFirst, pairSecond, Set.inter_def,
    sub_nonpos] using h

private theorem sectionSixFirstHighCentralLargeRegion_convex (epsilon : Real) :
    Convex Real (sectionSixFirstHighCentralLargeRegion epsilon) := by
  have h :=
    (convex_halfSpace_gt pairFirst.isLinear
      (sectionSixThetaGap epsilon)).inter
      ((convex_halfSpace_le (pairFirst - pairSecond).isLinear 0).inter
        ((convex_halfSpace_gt pairSecond.isLinear
          (sectionSixThetaTwo epsilon)).inter
          ((convex_halfSpace_le pairSecond.isLinear (1 / 2)).inter
            ((convex_halfSpace_le
              (pairSecond + (2 : Real) • pairFirst).isLinear 1).inter
              ((convex_halfSpace_gt (pairSecond + pairFirst).isLinear
                (sectionSixThetaTwo epsilon)).inter
                ((convex_halfSpace_lt (pairSecond + pairFirst).isLinear
                  (1 - sectionSixThetaTwo epsilon)).inter
                  (convex_halfSpace_ge
                    (pairSecond + (2 : Real) • pairFirst).isLinear
                    (1 - sectionSixThetaOne epsilon))))))))
  simpa [sectionSixFirstHighCentralLargeRegion, pairFirst, pairSecond,
    Set.inter_def, sub_nonpos] using h

theorem measurableSet_sectionSixFirstLowFarRegion (epsilon : Real) :
    MeasurableSet (sectionSixFirstLowFarRegion epsilon) := by
  unfold sectionSixFirstLowFarRegion
  measurability

theorem measurableSet_sectionSixFirstHighFarRegion (epsilon : Real) :
    MeasurableSet (sectionSixFirstHighFarRegion epsilon) := by
  unfold sectionSixFirstHighFarRegion
  measurability

theorem measurableSet_sectionSixFirstHighCentralLargeRegion (epsilon : Real) :
    MeasurableSet (sectionSixFirstHighCentralLargeRegion epsilon) := by
  unfold sectionSixFirstHighCentralLargeRegion
  measurability

theorem sectionSixFirstLowFarRegion_subset_logBox
    (epsilon : Real) (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowFarRegion epsilon ⊆
      Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) := by
  intro x hx
  rcases hx with ⟨hgap, horder, hu, _, _⟩
  have htheta : sectionSixThetaOne epsilon <= 1 / 2 := by
    simp only [sectionSixThetaOne]
    linarith
  exact ⟨⟨hgap, horder.trans (hu.trans htheta)⟩,
    ⟨hgap.trans_le horder, hu.trans htheta⟩⟩

theorem sectionSixFirstHighFarRegion_subset_logBox (epsilon : Real) :
    sectionSixFirstHighFarRegion epsilon ⊆
      Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) := by
  intro x hx
  exact ⟨⟨hx.1, hx.2.1.trans hx.2.2.2.1⟩,
    ⟨hx.1.trans_le hx.2.1, hx.2.2.2.1⟩⟩

theorem sectionSixFirstHighCentralLargeRegion_subset_logBox (epsilon : Real) :
    sectionSixFirstHighCentralLargeRegion epsilon ⊆
      Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) := by
  intro x hx
  exact ⟨⟨hx.1, hx.2.1.trans hx.2.2.2.1⟩,
    ⟨hx.1.trans_le hx.2.1, hx.2.2.2.1⟩⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

theorem volume_frontier_sectionSixFirstLowFarRegion (epsilon : Real) :
    volume (frontier (sectionSixFirstLowFarRegion epsilon)) = 0 :=
  (sectionSixFirstLowFarRegion_convex epsilon).addHaar_frontier volume

theorem volume_frontier_sectionSixFirstHighFarRegion (epsilon : Real) :
    volume (frontier (sectionSixFirstHighFarRegion epsilon)) = 0 :=
  (sectionSixFirstHighFarRegion_convex epsilon).addHaar_frontier volume

theorem volume_frontier_sectionSixFirstHighCentralLargeRegion (epsilon : Real) :
    volume (frontier (sectionSixFirstHighCentralLargeRegion epsilon)) = 0 :=
  (sectionSixFirstHighCentralLargeRegion_convex epsilon).addHaar_frontier volume

noncomputable def sectionSixFirstPairBuchstabKernel
    (x : Real × Real) : Real :=
  buchstabFunction ((1 - x.2 - x.1) / x.1) / (x.2 * x.1 ^ 2)

noncomputable def sectionSixFirstLowFarIntegral (epsilon : Real) : Real :=
  ∫ x in sectionSixFirstLowFarRegion epsilon,
    sectionSixFirstPairBuchstabKernel x

noncomputable def sectionSixFirstHighFarIntegral (epsilon : Real) : Real :=
  ∫ x in sectionSixFirstHighFarRegion epsilon,
    sectionSixFirstPairBuchstabKernel x

noncomputable def sectionSixFirstHighCentralLargeIntegral
    (epsilon : Real) : Real :=
  ∫ x in sectionSixFirstHighCentralLargeRegion epsilon,
    sectionSixFirstPairBuchstabKernel x

private noncomputable def sectionSixFirstPairClamp
    (epsilon t : Real) : Real :=
  max (sectionSixThetaGap epsilon) (min (1 / 2) t)

private noncomputable def sectionSixFirstPairSafeArgument
    (epsilon : Real) (x : Real × Real) : Real :=
  max 1 ((1 - sectionSixFirstPairClamp epsilon x.2 -
    sectionSixFirstPairClamp epsilon x.1) /
      sectionSixFirstPairClamp epsilon x.1)

private noncomputable def sectionSixFirstPairSafeKernel
    (epsilon : Real) (x : Real × Real) : Real :=
  buchstabFunction (sectionSixFirstPairSafeArgument epsilon x) /
    (sectionSixFirstPairClamp epsilon x.2 *
      sectionSixFirstPairClamp epsilon x.1 ^ 2)

private theorem sectionSixFirstPairSafeKernel_continuous
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon) :
    Continuous (sectionSixFirstPairSafeKernel epsilon) := by
  have hfirst : Continuous (fun x : Real × Real =>
      sectionSixFirstPairClamp epsilon x.1) :=
    continuous_const.max (continuous_const.min continuous_fst)
  have hsecond : Continuous (fun x : Real × Real =>
      sectionSixFirstPairClamp epsilon x.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  have hfirstPos (x : Real × Real) :
      0 < sectionSixFirstPairClamp epsilon x.1 :=
    hgap.trans_le (le_max_left _ _)
  have hsecondPos (x : Real × Real) :
      0 < sectionSixFirstPairClamp epsilon x.2 :=
    hgap.trans_le (le_max_left _ _)
  have harg : Continuous (sectionSixFirstPairSafeArgument epsilon) := by
    apply continuous_const.max
    exact ((continuous_const.sub hsecond).sub hfirst).div hfirst
      (fun x => (hfirstPos x).ne')
  have homega : Continuous (fun x : Real × Real =>
      buchstabFunction (sectionSixFirstPairSafeArgument epsilon x)) := by
    apply continuousOn_buchstabFunction.comp_continuous harg
    intro x
    exact le_max_left (1 : Real) _
  exact homega.div (hsecond.mul (hfirst.pow 2))
    (fun x => mul_ne_zero (hsecondPos x).ne'
      (pow_ne_zero _ (hfirstPos x).ne'))

private theorem sectionSixFirstPairSafeKernel_norm_le
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    (x : Real × Real) :
    ‖sectionSixFirstPairSafeKernel epsilon x‖ <=
      1 / sectionSixThetaGap epsilon ^ 3 := by
  have hv : sectionSixThetaGap epsilon <=
      sectionSixFirstPairClamp epsilon x.1 := le_max_left _ _
  have hu : sectionSixThetaGap epsilon <=
      sectionSixFirstPairClamp epsilon x.2 := le_max_left _ _
  have hvpos : 0 < sectionSixFirstPairClamp epsilon x.1 := hgap.trans_le hv
  have hupos : 0 < sectionSixFirstPairClamp epsilon x.2 := hgap.trans_le hu
  have hdenpos : 0 < sectionSixFirstPairClamp epsilon x.2 *
      sectionSixFirstPairClamp epsilon x.1 ^ 2 :=
    mul_pos hupos (sq_pos_of_pos hvpos)
  have hden : sectionSixThetaGap epsilon ^ 3 <=
      sectionSixFirstPairClamp epsilon x.2 *
        sectionSixFirstPairClamp epsilon x.1 ^ 2 := by
    have hvSq : sectionSixThetaGap epsilon ^ 2 <=
        sectionSixFirstPairClamp epsilon x.1 ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hgap.le hv
    have hmul := mul_le_mul hu hvSq (sq_nonneg _) hupos.le
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hgapCube : 0 < sectionSixThetaGap epsilon ^ 3 := pow_pos hgap _
  have homega := buchstabFunction_mem_Icc
    (show 1 <= sectionSixFirstPairSafeArgument epsilon x from
      le_max_left _ _)
  have homegaNonneg :
      0 <= buchstabFunction (sectionSixFirstPairSafeArgument epsilon x) := by
    linarith [homega.1]
  rw [sectionSixFirstPairSafeKernel, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg homegaNonneg hdenpos.le)]
  exact div_le_div₀ (by norm_num) homega.2 hgapCube hden

noncomputable def sectionSixFirstPairBuchstabKernelExtension
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    BoundedContinuousFunction (Real × Real) Real :=
  let hgap := (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  BoundedContinuousFunction.ofNormedAddCommGroup
    (sectionSixFirstPairSafeKernel epsilon)
    (sectionSixFirstPairSafeKernel_continuous epsilon hgap)
    (1 / sectionSixThetaGap epsilon ^ 3)
    (sectionSixFirstPairSafeKernel_norm_le epsilon hgap)

private theorem sectionSixFirstPairSafeKernel_eq
    (epsilon : Real) (hgap : 0 < sectionSixThetaGap epsilon)
    {x : Real × Real} (hfirst : sectionSixThetaGap epsilon < x.1)
    (horder : x.1 <= x.2) (hsecond : x.2 <= 1 / 2)
    (hcap : x.2 + 2 * x.1 <= 1) :
    sectionSixFirstPairSafeKernel epsilon x =
      sectionSixFirstPairBuchstabKernel x := by
  have hfirstPos : 0 < x.1 := hgap.trans hfirst
  have hfirstHalf : x.1 <= 1 / 2 := horder.trans hsecond
  have hclampFirst : sectionSixFirstPairClamp epsilon x.1 = x.1 := by
    rw [sectionSixFirstPairClamp, min_eq_right hfirstHalf,
      max_eq_right hfirst.le]
  have hclampSecond : sectionSixFirstPairClamp epsilon x.2 = x.2 := by
    rw [sectionSixFirstPairClamp, min_eq_right hsecond,
      max_eq_right (hfirst.le.trans horder)]
  have harg : 1 <= (1 - x.2 - x.1) / x.1 := by
    rw [le_div_iff₀ hfirstPos]
    linarith
  simp [sectionSixFirstPairSafeKernel, sectionSixFirstPairSafeArgument,
    sectionSixFirstPairBuchstabKernel, hclampFirst, hclampSecond,
    max_eq_right harg]

theorem sectionSixFirstPairBuchstabKernelExtension_eq_on_lowFarRegion
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Set.EqOn (sectionSixFirstPairBuchstabKernelExtension epsilon hepsilon
      hepsilonSmall) sectionSixFirstPairBuchstabKernel
      (sectionSixFirstLowFarRegion epsilon) := by
  intro x hx
  exact sectionSixFirstPairSafeKernel_eq epsilon
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1 hx.1 hx.2.1
      (hx.2.2.1.trans (by
        simp only [sectionSixThetaOne]
        linarith)) hx.2.2.2.1

theorem sectionSixFirstPairBuchstabKernelExtension_eq_on_highFarRegion
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Set.EqOn (sectionSixFirstPairBuchstabKernelExtension epsilon hepsilon
      hepsilonSmall) sectionSixFirstPairBuchstabKernel
      (sectionSixFirstHighFarRegion epsilon) := by
  intro x hx
  exact sectionSixFirstPairSafeKernel_eq epsilon
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1 hx.1 hx.2.1
      hx.2.2.2.1 hx.2.2.2.2.1

theorem sectionSixFirstPairBuchstabKernelExtension_eq_on_highCentralLargeRegion
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Set.EqOn (sectionSixFirstPairBuchstabKernelExtension epsilon hepsilon
      hepsilonSmall) sectionSixFirstPairBuchstabKernel
      (sectionSixFirstHighCentralLargeRegion epsilon) := by
  intro x hx
  exact sectionSixFirstPairSafeKernel_eq epsilon
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1 hx.1 hx.2.1
      hx.2.2.2.1 hx.2.2.2.2.1

end

end PrimesRestrictedDigits
