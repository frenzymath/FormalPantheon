import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
Closed-fiber Fubini identities for the Section 6 integral certificates.
Null-face theorems identify these closed cells with Maynard's strict regions
up to sets of measure zero.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def closedIccFiberCell {X : Type*}
    (outer : Set X) (lower upper : X → Real) : Set (X × Real) :=
  {z | z.1 ∈ outer ∧ z.2 ∈ Icc (lower z.1) (upper z.1)}

theorem measurableSet_closedIccFiberCell
    {X : Type*} [MeasurableSpace X]
    {outer : Set X} {lower upper : X → Real}
    (houter : MeasurableSet outer)
    (hlower : Measurable lower) (hupper : Measurable upper) :
    MeasurableSet (closedIccFiberCell outer lower upper) := by
  unfold closedIccFiberCell
  exact (houter.preimage measurable_fst).inter
    ((measurableSet_le
      (hlower.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hupper.comp measurable_fst)))

private theorem fiberIntegral_eq
    {X : Type*} [MeasurableSpace X]
    (outer : Set X) (lower upper : X → Real) (f : X × Real → Real)
    (hordered : ∀ x ∈ outer, lower x ≤ upper x) (x : X) :
    (∫ t, (closedIccFiberCell outer lower upper).indicator f (x, t)) =
      outer.indicator (fun x => ∫ t in lower x..upper x, f (x, t)) x := by
  by_cases hx : x ∈ outer
  · rw [Set.indicator_of_mem hx,
      intervalIntegral.integral_of_le (hordered x hx),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Icc (lower x) (upper x)
    · have hcell : (x, t) ∈ closedIccFiberCell outer lower upper := ⟨hx, ht⟩
      rw [Set.indicator_of_mem hcell, Set.indicator_of_mem ht]
    · have hcell : (x, t) ∉ closedIccFiberCell outer lower upper :=
        fun hz => ht hz.2
      rw [Set.indicator_of_notMem hcell, Set.indicator_of_notMem ht]
  · rw [Set.indicator_of_notMem hx]
    simp [closedIccFiberCell, hx]

theorem integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (outer : Set X) (lower upper : X → Real) (f : X × Real → Real)
    (houter : MeasurableSet outer)
    (hlower : Measurable lower) (hupper : Measurable upper)
    (hordered : ∀ x ∈ outer, lower x ≤ upper x)
    (hf : IntegrableOn f (closedIccFiberCell outer lower upper)
      (μ.prod volume)) :
    IntegrableOn (fun x => ∫ t in lower x..upper x, f (x, t)) outer μ := by
  have hcellMeasurable :=
    measurableSet_closedIccFiberCell houter hlower hupper
  have hindicator : Integrable
      ((closedIccFiberCell outer lower upper).indicator f)
      (μ.prod volume) := hf.integrable_indicator hcellMeasurable
  apply (integrable_indicator_iff houter).1
  exact hindicator.integral_prod_left.congr
    (Filter.Eventually.of_forall fun x =>
      fiberIntegral_eq outer lower upper f hordered x)

theorem setIntegral_closedIccFiberCell_eq_iterated
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (outer : Set X) (lower upper : X → Real) (f : X × Real → Real)
    (houter : MeasurableSet outer)
    (hlower : Measurable lower) (hupper : Measurable upper)
    (hordered : ∀ x ∈ outer, lower x ≤ upper x)
    (hf : IntegrableOn f (closedIccFiberCell outer lower upper)
      (μ.prod volume)) :
    (∫ z in closedIccFiberCell outer lower upper, f z ∂(μ.prod volume)) =
      ∫ x in outer, (∫ t in lower x..upper x, f (x, t)) ∂μ := by
  have hcellMeasurable :=
    measurableSet_closedIccFiberCell houter hlower hupper
  have hindicator : Integrable
      ((closedIccFiberCell outer lower upper).indicator f)
      (μ.prod volume) := hf.integrable_indicator hcellMeasurable
  calc
    (∫ z in closedIccFiberCell outer lower upper, f z ∂(μ.prod volume)) =
        ∫ z, (closedIccFiberCell outer lower upper).indicator f z
          ∂(μ.prod volume) := (integral_indicator hcellMeasurable).symm
    _ = ∫ x, (∫ t,
        (closedIccFiberCell outer lower upper).indicator f (x, t)) ∂μ :=
      integral_prod _ hindicator
    _ = ∫ x, outer.indicator
        (fun x => ∫ t in lower x..upper x, f (x, t)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact fiberIntegral_eq outer lower upper f hordered x
    _ = ∫ x in outer, (∫ t in lower x..upper x, f (x, t)) ∂μ :=
      integral_indicator houter

end

end PrimesRestrictedDigits
