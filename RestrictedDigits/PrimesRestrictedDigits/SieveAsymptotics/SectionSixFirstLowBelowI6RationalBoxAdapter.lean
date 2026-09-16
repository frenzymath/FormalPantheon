import PrimesRestrictedDigits.BasicEstimates.FiniteRationalGeometry
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6TailCellPayload
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6TailCellBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# One-row rational-box adapter for the I6 tail cell

This is a coordinate/image and local row-weight bridge only. It does not introduce a
subdivision tree, a change-of-variables theorem, or a global replay/cover claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def i6D686NestedPoint (z : Fin 4 -> Real) :
    (((Real × Real) × Real) × Real) :=
  (((z 0, z 1), z 2), z 3)

def i6D686Coordinates
    (x : (((Real × Real) × Real) × Real)) : Fin 4 -> Real :=
  ![x.1.1.1, x.1.1.2, x.1.2, x.2]

theorem i6D686Coordinates_nestedPoint (z : Fin 4 -> Real) :
    i6D686Coordinates (i6D686NestedPoint z) = z := by
  funext i
  fin_cases i <;> rfl

theorem i6D686NestedPoint_coordinates
    (x : (((Real × Real) × Real) × Real)) :
    i6D686NestedPoint (i6D686Coordinates x) = x := by
  rcases x with ⟨⟨⟨u, v⟩, w⟩, t⟩
  rfl

def i6D686Box : RationalBox 4 where
  lower := ![(1794 / 10000 : Rat), (1789 / 10000 : Rat),
    (169 / 1000 : Rat), (114 / 1000 : Rat)]
  upper := ![(1796 / 10000 : Rat), (1791 / 10000 : Rat),
    (171 / 1000 : Rat), (116 / 1000 : Rat)]

theorem i6D686Box_ordered : i6D686Box.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [i6D686Box]

theorem i6D686Box_volumeRat :
    i6D686Box.volumeRat = (1 / 6250000000000 : Rat) := by
  norm_num [i6D686Box, RationalBox.volumeRat, Fin.prod_univ_succ]

theorem i6D686Box_volume_real :
    volume.real i6D686Box.region = (1 / 6250000000000 : Real) := by
  rw [i6D686Box.volume_real i6D686Box_ordered,
    i6D686Box_volumeRat]
  norm_num

theorem i6D686_coordinates_preimage_native :
    {x | i6D686Coordinates x ∈ i6D686Box.region} =
      sectionSixFirstLowBelowI6TailCell := by
  ext x
  rcases x with ⟨⟨⟨u, v⟩, w⟩, t⟩
  simp only [i6D686Coordinates, i6D686Box, RationalBox.region,
    Set.mem_setOf_eq, Set.mem_Icc]
  simp only [sectionSixFirstLowBelowI6TailCell, Set.mem_prod, Set.mem_Icc]
  norm_num
  constructor
  · rintro ⟨hl, hu⟩
    have h0l := hl (0 : Fin 4)
    have h1l := hl (1 : Fin 4)
    have h2l := hl (2 : Fin 4)
    have h3l := hl (3 : Fin 4)
    have h0u := hu (0 : Fin 4)
    have h1u := hu (1 : Fin 4)
    have h2u := hu (2 : Fin 4)
    have h3u := hu (3 : Fin 4)
    simp [Matrix.cons_val] at h0l h1l h2l h3l h0u h1u h2u h3u
    norm_num at h0l h1l h2l h3l h0u h1u h2u h3u
    exact ⟨⟨⟨⟨h0l, h0u⟩, ⟨h1l, h1u⟩⟩,
      ⟨h2l, h2u⟩⟩, ⟨h3l, h3u⟩⟩
  · rintro ⟨⟨⟨⟨h0l, h0u⟩, ⟨h1l, h1u⟩⟩,
      ⟨h2l, h2u⟩⟩, ⟨h3l, h3u⟩⟩
    constructor
    · intro i
      fin_cases i
      · simpa using h0l
      · simpa using h1l
      · simpa using h2l
      · simpa using h3l
    · intro i
      fin_cases i
      · simpa using h0u
      · simpa using h1u
      · simpa using h2u
      · simpa using h3u

theorem i6D686_nestedPoint_mem_native
    {z : Fin 4 -> Real} (hz : z ∈ i6D686Box.region) :
    i6D686NestedPoint z ∈ sectionSixFirstLowBelowI6TailCell := by
  have hz' : i6D686NestedPoint z ∈
      i6D686Coordinates ⁻¹' i6D686Box.region := by
    simpa [Set.mem_preimage, i6D686Coordinates_nestedPoint] using hz
  have hz'' : i6D686NestedPoint z ∈
      {x | i6D686Coordinates x ∈ i6D686Box.region} := by
    change i6D686Coordinates (i6D686NestedPoint z) ∈ i6D686Box.region
    exact hz'
  rw [i6D686_coordinates_preimage_native] at hz''
  exact hz''

theorem i6D686_coordinates_mem_box
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowBelowI6TailCell) :
    i6D686Coordinates x ∈ i6D686Box.region := by
  have hx' : x ∈ {x | i6D686Coordinates x ∈ i6D686Box.region} := by
    rw [i6D686_coordinates_preimage_native]
    exact hx
  exact hx'

theorem i6D686_nestedPoint_image_eq_native :
    i6D686NestedPoint '' i6D686Box.region =
      sectionSixFirstLowBelowI6TailCell := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact i6D686_nestedPoint_mem_native hz
  · intro hx
    refine ⟨i6D686Coordinates x, i6D686_coordinates_mem_box hx, ?_⟩
    exact i6D686NestedPoint_coordinates x

theorem i6D686_mapped_volume_real :
    volume.real (i6D686NestedPoint '' i6D686Box.region) =
      (i6D686Box.volumeRat : Real) := by
  rw [i6D686_nestedPoint_image_eq_native,
    sectionSixFirstLowBelowI6TailCell_volume_real,
    i6D686Box_volumeRat]
  norm_num

theorem i6D686_box_image_mem_delta6AllHighTailCell :
    i6D686NestedPoint '' i6D686Box.region ⊆
      {x | sectionSixFirstLowBelowI6BaseFamily
          x.1.1.1 x.1.1.2 x.1.2 true ∧
        x.2 ∈ sectionSixFirstLowBelowI6FiberCell
          x.1.1.1 x.1.1.2 x.1.2 (2 : Fin 3)
          (fun _ : Fin 5 => true)} := by
  rw [i6D686_nestedPoint_image_eq_native]
  exact sectionSixFirstLowBelowI6TailCell_subset_delta6AllHighTailCell

def i6D686PayloadWeight : RationalBox 4 -> Rat := fun _ => 8100

theorem i6D686PayloadWeight_nonneg :
    0 <= i6D686PayloadWeight i6D686Box := by
  norm_num [i6D686PayloadWeight]

theorem i6D686_row_weightRat :
    i6D686Box.volumeRat * i6D686PayloadWeight i6D686Box =
      (81 / 62500000000 : Rat) := by
  norm_num [i6D686Box_volumeRat, i6D686PayloadWeight]

theorem i6D686_row_weightReal :
    ((i6D686Box.volumeRat * i6D686PayloadWeight i6D686Box : Rat) : Real) =
      (81 / 62500000000 : Real) := by
  rw [i6D686_row_weightRat]
  norm_num

theorem i6D686_native_integral_le_row_weight :
    (∫ x in sectionSixFirstLowBelowI6TailCell,
      sectionSixFirstLowBelowQuadrupleKernel x) <=
      ((i6D686Box.volumeRat * i6D686PayloadWeight i6D686Box : Rat) : Real) := by
  rw [i6D686_row_weightReal]
  exact sectionSixFirstLowBelowI6TailCell_integral_le

end

end PrimesRestrictedDigits
