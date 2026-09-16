import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserArtificialBounds
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogTransform

/-!
# The second dimension-one Rosser weight

This file implements the cross-sign weight in Iwaniec's Eq. (8.11), including its restricted
large-parameter regularity.
-/

open Set

namespace PrimesRestrictedDigits

/-- The real-power factor `(1-1/t)^(-4/3)` in Eq. (8.11). -/
noncomputable def dimensionOneRosserSecondKernelFactor (t : Real) : Real :=
  Real.exp ((-4 / 3 : Real) * Real.log (1 - 1 / t))

/-- The target-plus second kernel, using the shifted minus auxiliary. -/
noncomputable def dimensionOneRosserPlusSecondKernel (L t : Real) : Real :=
  dimensionOneRosserSecondKernelFactor t *
    dimensionOneRosserMinusArtificialAux L 1 (t - 1)

/-- The target-minus second kernel, using the shifted plus auxiliary. -/
noncomputable def dimensionOneRosserMinusSecondKernel (L t : Real) : Real :=
  dimensionOneRosserSecondKernelFactor t *
    dimensionOneRosserPlusArtificialAux L 1 (t - 1)

theorem dimensionOneRosserSecondKernelFactor_eq_rpow
    {t : Real} (ht : 1 < t) :
    dimensionOneRosserSecondKernelFactor t =
      (1 - 1 / t) ^ (-4 / 3 : Real) := by
  have ht0 : 0 < t := by linarith
  have hbase : 0 < 1 - 1 / t := by
    rw [sub_pos, div_lt_one ht0]
    exact ht
  unfold dimensionOneRosserSecondKernelFactor
  rw [Real.rpow_def_of_pos hbase]
  congr 1
  ring

theorem dimensionOneRosserPlusSecondKernel_eq_source
    {L t : Real} (hL : 0 < L) (ht : 1 < t) :
    dimensionOneRosserPlusSecondKernel L t =
      (1 - 1 / t) ^ (-4 / 3 : Real) *
        (1 + t ^ 50 / L) ^ (t - 1) *
          dimensionOneDelayScaledMinus (t - 1) := by
  unfold dimensionOneRosserPlusSecondKernel
  rw [dimensionOneRosserSecondKernelFactor_eq_rpow ht]
  unfold dimensionOneRosserMinusArtificialAux
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  ring_nf

theorem dimensionOneRosserMinusSecondKernel_eq_source
    {L t : Real} (hL : 0 < L) (ht : 1 < t) :
    dimensionOneRosserMinusSecondKernel L t =
      (1 - 1 / t) ^ (-4 / 3 : Real) *
        (1 + t ^ 50 / L) ^ (t - 1) *
          dimensionOneDelayScaledPlus (t - 1) := by
  unfold dimensionOneRosserMinusSecondKernel
  rw [dimensionOneRosserSecondKernelFactor_eq_rpow ht]
  unfold dimensionOneRosserPlusArtificialAux
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  ring_nf

theorem dimensionOneRosserSecondKernelFactor_pos (t : Real) :
    0 < dimensionOneRosserSecondKernelFactor t := Real.exp_pos _

theorem dimensionOneRosserSecondKernelFactor_continuousOn :
    ContinuousOn dimensionOneRosserSecondKernelFactor (Ioi 1) := by
  have hbase : ContinuousOn (fun t : Real => 1 - 1 / t) (Ioi 1) := by
    apply continuousOn_const.sub
    apply continuousOn_const.div continuousOn_id
    intro t ht
    change 1 < t at ht
    change t ≠ 0
    linarith
  unfold dimensionOneRosserSecondKernelFactor
  exact Real.continuous_exp.comp_continuousOn
    (continuousOn_const.mul
      (Real.continuousOn_log.comp hbase (fun t ht => by
        change 1 < t at ht
        have ht0 : 0 < t := by linarith
        change 1 - 1 / t ≠ 0
        exact ne_of_gt (by
          rw [sub_pos, div_lt_one ht0]
          exact ht))))

theorem dimensionOneRosserSecondKernelFactor_antitoneOn :
    AntitoneOn dimensionOneRosserSecondKernelFactor (Ioi 1) := by
  intro x hx y hy hxy
  change 1 < x at hx
  change 1 < y at hy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hbaseX : 0 < 1 - 1 / x := by
    rw [sub_pos, div_lt_one hx0]
    exact hx
  have hbaseY : 0 < 1 - 1 / y := by
    rw [sub_pos, div_lt_one hy0]
    exact hy
  have hinv : 1 / y <= 1 / x := one_div_le_one_div_of_le hx0 hxy
  have hbase : 1 - 1 / x <= 1 - 1 / y := by linarith
  have hlog : Real.log (1 - 1 / x) <= Real.log (1 - 1 / y) :=
    Real.log_le_log hbaseX hbase
  unfold dimensionOneRosserSecondKernelFactor
  rw [Real.exp_le_exp]
  exact mul_le_mul_of_nonpos_left hlog (by norm_num)

theorem dimensionOneRosserPlusSecondKernel_continuousOn
    {L : Real} (hL : 0 < L) :
    ContinuousOn (dimensionOneRosserPlusSecondKernel L) (Ioi 1) := by
  have hfactor := dimensionOneRosserSecondKernelFactor_continuousOn
  have haux : ContinuousOn (fun t : Real =>
      dimensionOneRosserMinusArtificialAux L 1 (t - 1)) (Ioi 1) :=
    (dimensionOneRosserMinusArtificialAux_continuous hL).comp_continuousOn
      (continuous_id.sub continuous_const).continuousOn
  unfold dimensionOneRosserPlusSecondKernel
  exact hfactor.mul haux

theorem dimensionOneRosserMinusSecondKernel_continuousOn
    {L : Real} (hL : 0 < L) :
    ContinuousOn (dimensionOneRosserMinusSecondKernel L) (Ioi 1) := by
  have hfactor := dimensionOneRosserSecondKernelFactor_continuousOn
  have haux : ContinuousOn (fun t : Real =>
      dimensionOneRosserPlusArtificialAux L 1 (t - 1)) (Ioi 1) :=
    (dimensionOneRosserPlusArtificialAux_continuous hL).comp_continuousOn
      (continuous_id.sub continuous_const).continuousOn
  unfold dimensionOneRosserMinusSecondKernel
  exact hfactor.mul haux

theorem dimensionOneRosserPlusSecondKernel_pos
    {L t : Real} (hL : 0 < L) (ht : 1 < t) :
    0 < dimensionOneRosserPlusSecondKernel L t := by
  unfold dimensionOneRosserPlusSecondKernel
  exact mul_pos (dimensionOneRosserSecondKernelFactor_pos t)
    (dimensionOneRosserMinusArtificialAux_pos hL (by linarith))

theorem dimensionOneRosserMinusSecondKernel_pos
    {L t : Real} (hL : 0 < L) (ht : 1 < t) :
    0 < dimensionOneRosserMinusSecondKernel L t := by
  unfold dimensionOneRosserMinusSecondKernel
  exact mul_pos (dimensionOneRosserSecondKernelFactor_pos t)
    (dimensionOneRosserPlusArtificialAux_pos hL (by linarith))

theorem dimensionOneRosserPlusSecondKernel_antitoneOn_of_aux
    {L a b : Real} (hL : 0 < L) (ha : 3 <= a)
    (hAux : AntitoneOn (dimensionOneRosserMinusArtificialAux L 1)
      (Icc (a - 1) (b - 1))) :
    AntitoneOn (dimensionOneRosserPlusSecondKernel L) (Icc a b) := by
  intro x hx y hy hxy
  have hx1 : x ∈ Ioi (1 : Real) := by
    change 1 < x
    linarith [ha, hx.1]
  have hy1 : y ∈ Ioi (1 : Real) := by
    change 1 < y
    linarith [ha, hy.1]
  have hfactor := dimensionOneRosserSecondKernelFactor_antitoneOn
    hx1 hy1 hxy
  have hxShift : x - 1 ∈ Icc (a - 1) (b - 1) := by
    constructor <;> linarith [hx.1, hx.2]
  have hyShift : y - 1 ∈ Icc (a - 1) (b - 1) := by
    constructor <;> linarith [hy.1, hy.2]
  have haux := hAux hxShift hyShift (by linarith)
  unfold dimensionOneRosserPlusSecondKernel
  exact mul_le_mul hfactor haux
    (dimensionOneRosserMinusArtificialAux_pos hL
      (by linarith [ha, hy.1])).le
    (dimensionOneRosserSecondKernelFactor_pos x).le

theorem dimensionOneRosserMinusSecondKernel_antitoneOn_of_aux
    {L a b : Real} (hL : 0 < L) (ha : 3 <= a)
    (hAux : AntitoneOn (dimensionOneRosserPlusArtificialAux L 1)
      (Icc (a - 1) (b - 1))) :
    AntitoneOn (dimensionOneRosserMinusSecondKernel L) (Icc a b) := by
  intro x hx y hy hxy
  have hx1 : x ∈ Ioi (1 : Real) := by
    change 1 < x
    linarith [ha, hx.1]
  have hy1 : y ∈ Ioi (1 : Real) := by
    change 1 < y
    linarith [ha, hy.1]
  have hfactor := dimensionOneRosserSecondKernelFactor_antitoneOn
    hx1 hy1 hxy
  have hxShift : x - 1 ∈ Icc (a - 1) (b - 1) := by
    constructor <;> linarith [hx.1, hx.2]
  have hyShift : y - 1 ∈ Icc (a - 1) (b - 1) := by
    constructor <;> linarith [hy.1, hy.2]
  have haux := hAux hxShift hyShift (by linarith)
  unfold dimensionOneRosserMinusSecondKernel
  exact mul_le_mul hfactor haux
    (dimensionOneRosserPlusArtificialAux_pos hL
      (by linarith [ha, hy.1])).le
    (dimensionOneRosserSecondKernelFactor_pos x).le

theorem dimensionOneRosserPlusSecondKernel_antitoneOn
    {L s s0 : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) :
    AntitoneOn (dimensionOneRosserPlusSecondKernel L) (Icc s s0) := by
  apply dimensionOneRosserPlusSecondKernel_antitoneOn_of_aux hL (by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith)
  exact (dimensionOneRosserMinusArtificialAux_one_strictAntiOn
    hL hs hss0 hcap).antitoneOn

theorem dimensionOneRosserMinusSecondKernel_antitoneOn
    {L s s0 : Real} (hL : 0 < L)
    (hs : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) :
    AntitoneOn (dimensionOneRosserMinusSecondKernel L) (Icc s s0) := by
  apply dimensionOneRosserMinusSecondKernel_antitoneOn_of_aux hL (by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith)
  exact (dimensionOneRosserPlusArtificialAux_one_strictAntiOn
    hL hs hss0 hcap).antitoneOn

/-- The target-plus Eq. (8.11) weight in the original prime variable. -/
noncomputable def dimensionOneRosserPlusSecondWeight
    (level x : Real) : Real :=
  dimensionOneRosserPlusSecondKernel (Real.log level)
    (buchstabArgument level x + 1)

/-- The target-minus Eq. (8.11) weight in the original prime variable. -/
noncomputable def dimensionOneRosserMinusSecondWeight
    (level x : Real) : Real :=
  dimensionOneRosserMinusSecondKernel (Real.log level)
    (buchstabArgument level x + 1)

private theorem secondWeight_coordinate_mem
    {level z s s0 x : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLarge : 0 < s)
    (hss0 : s < s0)
    (hx : x ∈ Icc (level ^ (1 / s0)) z) :
    buchstabArgument level x + 1 ∈ Icc s s0 := by
  have hlevelOne : 1 < level := by linarith
  have hzOne : 1 < z := by linarith
  have hrange := buchstabArgument_mem_Icc_realEndpoints
    hlevelOne hzOne hsLarge hs hss0 hx
  constructor <;> linarith [hrange.1, hrange.2]

private theorem secondWeight_interval_above_one
    {level z s s0 x : Real} (hlevel : 2 <= level)
    (hsPositive : 0 < s) (hss0 : s < s0)
    (hx : x ∈ Icc (level ^ (1 / s0)) z) :
    1 < x := by
  have hlevelOne : 1 < level := by linarith
  have hs0Pos : 0 < s0 := hsPositive.trans hss0
  have hwOne : 1 < level ^ (1 / s0) :=
    Real.one_lt_rpow hlevelOne (one_div_pos.mpr hs0Pos)
  exact hwOne.trans_le hx.1

/-- Composition of a positive continuous antitone second kernel with the
decreasing Buchstab coordinate. -/
theorem dimensionOneRosserSecondWeight_properties_of_antitoneOn
    (kernel : Real -> Real -> Real)
    (hpos : ∀ {L t : Real}, 0 < L -> 1 < t -> 0 < kernel L t)
    (hcont : ∀ {L : Real}, 0 < L -> ContinuousOn (kernel L) (Ioi 1))
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsOne : 1 < s) (hss0 : s < s0)
    (hkernelAnti : AntitoneOn (kernel (Real.log level)) (Icc s s0)) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
        0 <= kernel (Real.log level) (buchstabArgument level x + 1)) ∧
      ContinuousOn
        (fun x => kernel (Real.log level) (buchstabArgument level x + 1))
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn
        (fun x => kernel (Real.log level) (buchstabArgument level x + 1))
        (Icc (level ^ (1 / s0)) z) := by
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hsPositive : 0 < s := by linarith
  have hargCont : ContinuousOn (fun x => buchstabArgument level x + 1)
      (Icc (level ^ (1 / s0)) z) :=
    ((continuousOn_buchstabArgument level).mono (fun x hx =>
      secondWeight_interval_above_one hlevel hsPositive hss0 hx)).add
      continuousOn_const
  have hmaps : MapsTo (fun x => buchstabArgument level x + 1)
      (Icc (level ^ (1 / s0)) z) (Icc s s0) := by
    intro x hx
    exact secondWeight_coordinate_mem hlevel hz hs hsPositive hss0 hx
  constructor
  · intro x hx
    exact (hpos hL (by
      have hrange := hmaps hx
      exact hsOne.trans_le hrange.1)).le
  constructor
  · exact (hcont hL).comp hargCont (fun x hx => by
      have hrange := hmaps hx
      change 1 < buchstabArgument level x + 1
      exact hsOne.trans_le hrange.1)
  · intro x hx y hy hxy
    have hlevelOne : 1 < level := by linarith
    have hxOne := secondWeight_interval_above_one hlevel hsPositive hss0 hx
    have hyOne := secondWeight_interval_above_one hlevel hsPositive hss0 hy
    have hcoord : buchstabArgument level y + 1 <=
        buchstabArgument level x + 1 := by
      simpa [add_comm] using add_le_add_right
        (buchstabArgument_antitoneOn hlevelOne hxOne hyOne hxy) 1
    exact hkernelAnti (hmaps hy) (hmaps hx) hcoord

theorem dimensionOneRosserPlusSecondWeight_properties
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= Real.log level) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
        0 <= dimensionOneRosserPlusSecondWeight level x) ∧
      ContinuousOn (dimensionOneRosserPlusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn (dimensionOneRosserPlusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) := by
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  apply dimensionOneRosserSecondWeight_properties_of_antitoneOn
    dimensionOneRosserPlusSecondKernel
    dimensionOneRosserPlusSecondKernel_pos
    dimensionOneRosserPlusSecondKernel_continuousOn hlevel hz hs
    (by nlinarith [Real.exp_pos (5000 : Real)]) hss0
  exact dimensionOneRosserPlusSecondKernel_antitoneOn
    hL hsLarge hss0 hcap

theorem dimensionOneRosserMinusSecondWeight_properties
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= Real.log level) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
        0 <= dimensionOneRosserMinusSecondWeight level x) ∧
      ContinuousOn (dimensionOneRosserMinusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn (dimensionOneRosserMinusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) := by
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  apply dimensionOneRosserSecondWeight_properties_of_antitoneOn
    dimensionOneRosserMinusSecondKernel
    dimensionOneRosserMinusSecondKernel_pos
    dimensionOneRosserMinusSecondKernel_continuousOn hlevel hz hs
    (by nlinarith [Real.exp_pos (5000 : Real)]) hss0
  exact dimensionOneRosserMinusSecondKernel_antitoneOn
    hL hsLarge hss0 hcap

end PrimesRestrictedDigits
