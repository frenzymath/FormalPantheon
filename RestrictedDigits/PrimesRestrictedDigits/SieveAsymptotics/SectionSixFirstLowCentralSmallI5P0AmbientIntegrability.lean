import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0AmbientBoxOrderedOuter
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# P0 ambient compact-carrier integrability

The compact carrier here is a technical support set for the fixed-delta ambient cells. Its
weak affine half-space is used only to keep the Buchstab argument in `Ici 1`; it is not a
source cap or a source-region assertion.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier :
    Set ((((Real × Real) × Real) × Real)) :=
  (sectionSixFirstLowCentralSmallI5P0AmbientBaseBox ×ˢ
      Set.Icc (sectionSixThetaGap (1 / 1000000 : Real))
        (sectionSixThetaOne (1 / 1000000 : Real))) ∩
    {x | x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1}

theorem sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier_compact :
    IsCompact sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier := by
  apply (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
    isCompact_Icc).inter_right
  exact isClosed_le (by fun_prop) continuous_const

theorem sectionSixFirstLowCentralSmallI5P0AmbientCell_subset_compactCarrier
    (b : Fin 3) :
    sectionSixFirstLowCentralSmallI5P0AmbientCell b ⊆
      sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier := by
  intro z hz
  change z.1 ∈ sectionSixFirstLowCentralSmallI5P0AmbientBaseBox ∧
      z.2 ∈ Set.Icc
        (sectionSixFirstLowCentralSmallI5P0AmbientLower b z.1)
        (sectionSixFirstLowCentralSmallI5P0AmbientUpper b z.1) at hz
  rcases hz with ⟨hbase, hfiber⟩
  refine ⟨?_, ?_⟩
  · change z.1 ∈ sectionSixFirstLowCentralSmallI5P0AmbientBaseBox ∧
      z.2 ∈ Set.Icc (sectionSixThetaGap (1 / 1000000 : Real))
        (sectionSixThetaOne (1 / 1000000 : Real))
    refine ⟨hbase, ?_⟩
    have hgap : sectionSixThetaGap (1 / 1000000 : Real) ≤
        sectionSixFirstLowCentralSmallI5P0AmbientLower b z.1 :=
      le_max_left _ _
    have htlow := hgap.trans hfiber.1
    have htupper : sectionSixFirstLowCentralSmallI5P0AmbientUpper b z.1 ≤
        z.1.2 := by
      unfold sectionSixFirstLowCentralSmallI5P0AmbientUpper
        sectionSixFirstLowCentralSmallI5P0CellUpper
      exact (min_le_left _ _).trans (min_le_left _ _)
    have htwupper : z.1.2 ≤
        sectionSixThetaOne (1 / 1000000 : Real) := by
      exact hbase.2.2
    have hthigh := hfiber.2.trans (htupper.trans htwupper)
    exact ⟨htlow, hthigh⟩
  · change z.1.1.1 + z.1.1.2 + z.1.2 + 2 * z.2 ≤ 1
    have hgappos : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
      norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
    have htpos : 0 < z.2 := hgappos.trans_le
      (le_trans (le_max_left _ _) hfiber.1)
    have hraw : z.2 ≤
        sectionSixFirstLowCentralSmallI5P0RawUpper
          z.1.1.1 z.1.1.2 z.1.2 b := by
      apply hfiber.2.trans
      unfold sectionSixFirstLowCentralSmallI5P0AmbientUpper
        sectionSixFirstLowCentralSmallI5P0CellUpper
      exact min_le_right _ _
    fin_cases b
    · change z.2 ≤ (1 - z.1.1.1 - z.1.1.2 - z.1.2) / 2 at hraw
      linarith
    · change z.2 ≤ (1 - z.1.1.1 - z.1.1.2 - z.1.2) / 3 at hraw
      linarith
    · change z.2 ≤ (1 - z.1.1.1 - z.1.1.2 - z.1.2) / 4 at hraw
      linarith

private theorem sectionSixFirstLowCentralSmallI5P0AmbientKernel_continuousOn_compact :
    ContinuousOn sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier := by
  unfold sectionSixFirstLowCentralSmallQuadrupleKernel
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have htPos : ∀ x ∈ sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier,
      0 < x.2 := by
    intro x hx
    exact hgap.trans_le hx.1.2.1
  have hratio : ContinuousOn
      (fun x : (((Real × Real) × Real) × Real) =>
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2)
      sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier := by
    apply ((((continuousOn_const.sub continuousOn_fst.fst.fst).sub
      continuousOn_fst.fst.snd).sub continuousOn_fst.snd).sub
      continuousOn_snd).div continuousOn_snd
    intro x hx
    exact (htPos x hx).ne'
  have hratio_mem : MapsTo
      (fun x : (((Real × Real) × Real) × Real) =>
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2)
      sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier (Ici 1) := by
    intro x hx
    have hcap : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1 :=
      hx.2
    rw [mem_Ici, le_div_iff₀ (htPos x hx)]
    linarith
  refine (continuousOn_buchstabFunction.comp hratio hratio_mem).div ?_ ?_
  · fun_prop
  · intro x hx
    have huPos : 0 < x.1.1.1 := hgap.trans_le hx.1.1.1.1.1
    have hvPos : 0 < x.1.1.2 := hgap.trans_le hx.1.1.1.2.1
    have hwPos : 0 < x.1.2 := hgap.trans_le hx.1.1.2.1
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero huPos.ne' hvPos.ne') hwPos.ne')
      (pow_ne_zero 2 (htPos x hx).ne')

theorem sectionSixFirstLowCentralSmallI5P0AmbientKernel_integrableOn :
    IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier
      (volume.prod volume) := by
  exact sectionSixFirstLowCentralSmallI5P0AmbientKernel_continuousOn_compact
    |>.integrableOn_compact (μ := volume.prod volume)
      sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier_compact

theorem sectionSixFirstLowCentralSmallI5P0AmbientCell_integrable
    (b : Fin 3) :
    IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixFirstLowCentralSmallI5P0AmbientCell b)
      (volume.prod volume) := by
  exact sectionSixFirstLowCentralSmallI5P0AmbientKernel_integrableOn.mono_set
    (sectionSixFirstLowCentralSmallI5P0AmbientCell_subset_compactCarrier b)

end

end PrimesRestrictedDigits
