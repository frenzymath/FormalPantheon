import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0EndpointMeasurability
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberOrderedFubini
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Ambient P0 cells and ordered outer transport

This module supplies the rectangular native three-coordinate ambient box, its three
endpoint-indexed closed fibers, and the conditional ordered-outer Fubini transport. It does
not identify the box with a P0 projection or prove the product-cell integrability premise.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P0AmbientBaseBox :
    Set ((Real × Real) × Real) :=
  (Set.Icc (sectionSixThetaGap (1 / 1000000 : Real))
      (sectionSixThetaOne (1 / 1000000 : Real)) ×ˢ
   Set.Icc (sectionSixThetaGap (1 / 1000000 : Real))
      (sectionSixThetaOne (1 / 1000000 : Real))) ×ˢ
  Set.Icc (sectionSixThetaGap (1 / 1000000 : Real))
    (sectionSixThetaOne (1 / 1000000 : Real))

def sectionSixFirstLowCentralSmallI5P0AmbientLower (b : Fin 3) :
    ((Real × Real) × Real) → Real :=
  fun z => sectionSixFirstLowCentralSmallI5P0CellLower
    z.1.1 z.1.2 z.2 b

def sectionSixFirstLowCentralSmallI5P0AmbientUpper (b : Fin 3) :
    ((Real × Real) × Real) → Real :=
  fun z => sectionSixFirstLowCentralSmallI5P0CellUpper
    z.1.1 z.1.2 z.2 b

def sectionSixFirstLowCentralSmallI5P0AmbientCell (b : Fin 3) :
    Set ((((Real × Real) × Real) × Real)) :=
  closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
    (sectionSixFirstLowCentralSmallI5P0AmbientLower b)
    (sectionSixFirstLowCentralSmallI5P0AmbientUpper b)

def sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (b : Fin 3) :
    Set ((Real × Real) × Real) :=
  orderedOuter
    sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
    (sectionSixFirstLowCentralSmallI5P0AmbientLower b)
    (sectionSixFirstLowCentralSmallI5P0AmbientUpper b)

theorem sectionSixFirstLowCentralSmallI5P0AmbientCell_measurableSet
    (b : Fin 3) :
    MeasurableSet
      (sectionSixFirstLowCentralSmallI5P0AmbientCell b) := by
  apply measurableSet_closedIccFiberCell
  · unfold sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
    exact (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc
  · change Measurable (fun z : ((Real × Real) × Real) =>
      sectionSixFirstLowCentralSmallI5P0CellLower z.1.1 z.1.2 z.2 b)
    exact sectionSixFirstLowCentralSmallI5P0CellLower_measurable b
  · change Measurable (fun z : ((Real × Real) × Real) =>
      sectionSixFirstLowCentralSmallI5P0CellUpper z.1.1 z.1.2 z.2 b)
    exact sectionSixFirstLowCentralSmallI5P0CellUpper_measurable b

theorem sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase_measurableSet
    (b : Fin 3) :
    MeasurableSet
      (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase b) := by
  apply measurableSet_orderedOuter
  · unfold sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
    exact (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc
  · change Measurable (fun z : ((Real × Real) × Real) =>
      sectionSixFirstLowCentralSmallI5P0CellLower z.1.1 z.1.2 z.2 b)
    exact sectionSixFirstLowCentralSmallI5P0CellLower_measurable b
  · change Measurable (fun z : ((Real × Real) × Real) =>
      sectionSixFirstLowCentralSmallI5P0CellUpper z.1.1 z.1.2 z.2 b)
    exact sectionSixFirstLowCentralSmallI5P0CellUpper_measurable b

theorem sectionSixFirstLowCentralSmallI5P0AmbientCell_eq_ordered
    (b : Fin 3) :
    sectionSixFirstLowCentralSmallI5P0AmbientCell b =
      closedIccFiberCell
        (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase b)
        (sectionSixFirstLowCentralSmallI5P0AmbientLower b)
        (sectionSixFirstLowCentralSmallI5P0AmbientUpper b) := by
  unfold sectionSixFirstLowCentralSmallI5P0AmbientCell
    sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase
  exact closedIccFiberCell_eq_orderedOuter

theorem sectionSixFirstLowCentralSmallI5P0AmbientCell_setIntegral_eq_iterated
    (b : Fin 3)
    (hf : IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixFirstLowCentralSmallI5P0AmbientCell b)
      (volume.prod volume)) :
    (∫ z in sectionSixFirstLowCentralSmallI5P0AmbientCell b,
      sectionSixFirstLowCentralSmallQuadrupleKernel z
        ∂(volume.prod volume)) =
      ∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase b,
        (∫ t in
          sectionSixFirstLowCentralSmallI5P0AmbientLower b x..
            sectionSixFirstLowCentralSmallI5P0AmbientUpper b x,
          sectionSixFirstLowCentralSmallQuadrupleKernel (x, t)) ∂volume := by
  apply setIntegral_closedIccFiberCell_eq_iterated_orderedOuter
    sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
    (sectionSixFirstLowCentralSmallI5P0AmbientLower b)
    (sectionSixFirstLowCentralSmallI5P0AmbientUpper b)
    sectionSixFirstLowCentralSmallQuadrupleKernel
  · unfold sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
    exact (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc
  · exact sectionSixFirstLowCentralSmallI5P0CellLower_measurable b
  · exact sectionSixFirstLowCentralSmallI5P0CellUpper_measurable b
  · exact hf

end

end PrimesRestrictedDigits
