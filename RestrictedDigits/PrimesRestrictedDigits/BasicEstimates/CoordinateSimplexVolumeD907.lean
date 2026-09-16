import PrimesRestrictedDigits.BasicEstimates.CoordinateSimplexTransportD906
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # CoordinateSimplexVolumeD907 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private theorem coordinateSimplex3_subset_box :
    coordinateSimplex3 ⊆ Set.pi Set.univ (fun _ : Fin 3 => Icc (0 : Real) 1) := by
  intro x hx
  simp only [coordinateSimplex3, mem_setOf_eq] at hx
  rw [mem_pi]
  intro i _
  fin_cases i
  · change x 0 ∈ Icc (0 : Real) 1
    exact ⟨hx.1, by linarith [hx.2.1, hx.2.2.2.1]⟩
  · change x 1 ∈ Icc (0 : Real) 1
    exact ⟨hx.2.1, by linarith [hx.1, hx.2.2.2.1]⟩
  · change x 2 ∈ Icc (0 : Real) 1
    exact ⟨hx.2.2.1, by linarith [hx.1, hx.2.1, hx.2.2.2.2]⟩

private theorem coordinateSimplex3_measure_ne_top :
    (volume : Measure (Fin 3 → Real)) coordinateSimplex3 ≠ (⊤ : ENNReal) := by
  apply measure_ne_top_of_subset coordinateSimplex3_subset_box
  exact (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc)).measure_ne_top

theorem coordinateSimplex3_volume :
    (volume : Measure (Fin 3 → Real)) coordinateSimplex3 =
      ENNReal.ofReal ((1 : Real) / 6) := by
  have htransport :=
    coordinateNestedEquiv_setIntegral_preimage (f := fun _ : ((Real × Real) × Real) => (1 : Real))
  have hone :
      (∫ x in coordinateSimplex3, (1 : Real) ∂(volume : Measure (Fin 3 → Real))) =
        (1 : Real) / 6 := by
    rw [← coordinateNestedEquiv_preimage_standardSimplex3]
    calc
      (∫ x in coordinateNestedEquiv ⁻¹' standardSimplex3,
          (1 : Real) ∂(volume : Measure (Fin 3 → Real))) =
          ∫ z in standardSimplex3, (1 : Real)
            ∂((volume : Measure (Real × Real)).prod (volume : Measure Real)) := htransport
      _ = (1 : Real) / 6 := standardSimplex3_setIntegral_one
  symm
  rw [← ofReal_setIntegral_one_of_measure_ne_top coordinateSimplex3_measure_ne_top]
  rw [hone]

end
end PrimesRestrictedDigits
