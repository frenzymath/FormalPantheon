import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberOrderedOuter

/-!
# Normalized closed-fiber Fubini adapter

This adapter applies the existing closed-Icc Fubini theorem after restricting the outer set to
points where the fiber endpoints are ordered. Its iterated integral is therefore explicitly
over `orderedOuter`; it does not reinterpret an oriented reversed interval integral as an
empty set fiber.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem setIntegral_closedIccFiberCell_eq_iterated_orderedOuter
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (outer : Set X) (lower upper : X → Real) (f : X × Real → Real)
    (houter : MeasurableSet outer)
    (hlower : Measurable lower) (hupper : Measurable upper)
    (hf : IntegrableOn f (closedIccFiberCell outer lower upper)
      (μ.prod volume)) :
    (∫ z in closedIccFiberCell outer lower upper, f z ∂(μ.prod volume)) =
      ∫ x in orderedOuter outer lower upper,
        (∫ t in lower x..upper x, f (x, t)) ∂μ := by
  have houterNorm : MeasurableSet (orderedOuter outer lower upper) :=
    measurableSet_orderedOuter houter hlower hupper
  have horderedNorm : ∀ x ∈ orderedOuter outer lower upper,
      lower x ≤ upper x := by
    intro x hx
    exact hx.2
  have hcell :
      closedIccFiberCell outer lower upper =
        closedIccFiberCell (orderedOuter outer lower upper) lower upper :=
    closedIccFiberCell_eq_orderedOuter
  have hfNorm : IntegrableOn f
      (closedIccFiberCell (orderedOuter outer lower upper) lower upper)
      (μ.prod volume) := by
    rw [← hcell]
    exact hf
  calc
    (∫ z in closedIccFiberCell outer lower upper, f z ∂(μ.prod volume)) =
        ∫ z in closedIccFiberCell (orderedOuter outer lower upper) lower upper,
          f z ∂(μ.prod volume) := by
      rw [hcell]
    _ = ∫ x in orderedOuter outer lower upper,
        (∫ t in lower x..upper x, f (x, t)) ∂μ :=
      setIntegral_closedIccFiberCell_eq_iterated
        (orderedOuter outer lower upper) lower upper f houterNorm hlower hupper
        horderedNorm hfNorm

end

end PrimesRestrictedDigits
