import PrimesRestrictedDigits.BasicEstimates.StandardSimplexVolumeD904
import PrimesRestrictedDigits.BasicEstimates.CoordinateNestedEquivD905
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
/-! # CoordinateSimplexTransportD906 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def coordinateSimplex3 : Set (Fin 3 → Real) :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧ x 0 + x 1 ≤ 1 ∧
    x 0 + x 1 + x 2 ≤ 1}

theorem coordinateNestedEquiv_preimage_standardSimplex3 :
    coordinateNestedEquiv ⁻¹' standardSimplex3 = coordinateSimplex3 := by
  ext x
  rw [mem_preimage]
  rw [coordinateNestedEquiv_apply]
  change ((((x 0, x 1), x 2) ∈ closedIccFiberCell (closedIccFiberCell (Icc (0 : Real) 1)
      (fun _ : Real => 0) (fun x => 1 - x)) (fun _ : Real × Real => 0)
      (fun p => 1 - p.1 - p.2)) ↔ _)
  change ((x 0 ∈ Icc (0 : Real) 1 ∧ x 1 ∈ Icc (0 : Real) (1 - x 0)) ∧
      x 2 ∈ Icc (0 : Real) (1 - x 0 - x 1)) ↔ _
  simp only [mem_Icc, coordinateSimplex3, mem_setOf_eq]
  constructor
  · rintro ⟨⟨⟨hx0, hx0u⟩, hx1, hx1u⟩, hx2, hx2u⟩
    exact ⟨hx0, hx1, hx2, by linarith, by linarith⟩
  · rintro ⟨hx0, hx1, hx2, hsum, htotal⟩
    exact ⟨⟨⟨hx0, by linarith⟩, hx1, by linarith⟩, hx2, by linarith⟩

theorem coordinateNestedEquiv_setIntegral_preimage (f : ((Real × Real) × Real) → Real) :
    (∫ x in coordinateNestedEquiv ⁻¹' standardSimplex3, f (coordinateNestedEquiv x)
      ∂(volume : Measure (Fin 3 → Real))) =
      ∫ z in standardSimplex3, f z
        ∂((volume : Measure (Real × Real)).prod (volume : Measure Real)) := by
  exact coordinateNestedEquiv_preserving.setIntegral_preimage_emb
    coordinateNestedEquiv.measurableEmbedding f standardSimplex3

end

end PrimesRestrictedDigits
