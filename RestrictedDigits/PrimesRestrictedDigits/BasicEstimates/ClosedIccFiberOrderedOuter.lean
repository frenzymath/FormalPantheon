import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral

/-!
# Ordered outer normalization for closed fibers

The closed-fiber set is empty when its upper endpoint is below its lower endpoint, while an
oriented interval integral is not generally zero there. This module normalizes the outer set
before a caller applies the existing closed-Icc Fubini API.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def orderedOuter {X : Type*}
    (outer : Set X) (lower upper : X → Real) : Set X :=
  outer ∩ {x | lower x ≤ upper x}

theorem measurableSet_orderedOuter
    {X : Type*} [MeasurableSpace X]
    {outer : Set X} {lower upper : X → Real}
    (houter : MeasurableSet outer) (hlower : Measurable lower)
    (hupper : Measurable upper) :
    MeasurableSet (orderedOuter outer lower upper) := by
  exact houter.inter (measurableSet_le hlower hupper)

theorem closedIccFiberCell_eq_orderedOuter
    {X : Type*} {outer : Set X} {lower upper : X → Real} :
    closedIccFiberCell outer lower upper =
      closedIccFiberCell (orderedOuter outer lower upper) lower upper := by
  ext z
  constructor
  · rintro ⟨hzouter, hzIcc⟩
    exact ⟨⟨hzouter, hzIcc.1.trans hzIcc.2⟩, hzIcc⟩
  · rintro ⟨hzordered, hzIcc⟩
    exact ⟨hzordered.1, hzIcc⟩

end

end PrimesRestrictedDigits
