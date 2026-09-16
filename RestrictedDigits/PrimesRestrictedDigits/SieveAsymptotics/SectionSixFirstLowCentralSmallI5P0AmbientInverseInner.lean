import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0AmbientFubini
import Mathlib.Tactic.NormNum

/-!
# Branch-zero inverse payload on the P0 ambient cell

This file only transports the existing native inverse-branch identity to the ordered ambient
base and then composes it with the unconditional product-measure transport. No numerical
estimate is asserted here.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralSmallI5P0AmbientInverseInner_eq
    {x : ((Real × Real) × Real)}
    (hx : x ∈
      sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (0 : Fin 3)) :
    (∫ t in
        sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x..
          sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x,
      sectionSixFirstLowCentralSmallQuadrupleKernel (x, t)) =
      1 / (x.1.1 * x.1.2 * x.2 *
        (1 - x.1.1 - x.1.2 - x.2)) *
        Real.log
          ((sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x *
              (1 - x.1.1 - x.1.2 - x.2 -
                sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x)) /
            (sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x *
              (1 - x.1.1 - x.1.2 - x.2 -
                sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x))) := by
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hxBase := hx.1
  have hpos : 0 < x.1.1 ∧ 0 < x.1.2 ∧ 0 < x.2 := by
    unfold sectionSixFirstLowCentralSmallI5P0AmbientBaseBox at hxBase
    simp only [Set.mem_prod, Set.mem_Icc] at hxBase
    exact ⟨hgap.trans_le hxBase.1.1.1,
      hgap.trans_le hxBase.1.2.1, hgap.trans_le hxBase.2.1⟩
  have hLU :
      sectionSixFirstLowCentralSmallI5P0CellLower
          x.1.1 x.1.2 x.2 (0 : Fin 3) <=
        sectionSixFirstLowCentralSmallI5P0CellUpper
          x.1.1 x.1.2 x.2 (0 : Fin 3) := by
    exact hx.2
  have hp := sectionSixFirstLowCentralSmallI5P0InverseCell_integral_eq
    (u := x.1.1) (v := x.1.2) (w := x.2)
    hpos.1 hpos.2.1 hpos.2.2 hLU
  simpa [sectionSixFirstLowCentralSmallI5P0AmbientLower,
    sectionSixFirstLowCentralSmallI5P0AmbientUpper,
    sectionSixFirstLowCentralSmallQuadrupleKernel] using hp

theorem sectionSixFirstLowCentralSmallI5P0AmbientInverseCell_setIntegral_eq_log :
    (∫ z in
        sectionSixFirstLowCentralSmallI5P0AmbientCell (0 : Fin 3),
      sectionSixFirstLowCentralSmallQuadrupleKernel z
        ∂(volume.prod volume)) =
      (∫ x in
          sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (0 : Fin 3),
          1 / (x.1.1 * x.1.2 * x.2 *
          (1 - x.1.1 - x.1.2 - x.2)) *
          Real.log
            ((sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x *
                (1 - x.1.1 - x.1.2 - x.2 -
                  sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x)) /
              (sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x *
                (1 - x.1.1 - x.1.2 - x.2 -
                  sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x)))
        ∂volume) := by
  rw [sectionSixFirstLowCentralSmallI5P0AmbientCell_setIntegral_eq_iterated_unconditional
    (0 : Fin 3)]
  refine setIntegral_congr_fun
    (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase_measurableSet 0) ?_
  intro x hx
  exact sectionSixFirstLowCentralSmallI5P0AmbientInverseInner_eq hx

end

end PrimesRestrictedDigits
