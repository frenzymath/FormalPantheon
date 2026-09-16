import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6RationalBoxAdapter
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Generic native cells for four-dimensional I6 rational boxes

This module only reassociates an arbitrary `RationalBox 4` into the native left-associated
tuple type. It makes no assertion that the box lies in the I6 carrier or satisfies any branch
or payload condition.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The native left-associated cell corresponding to an arbitrary `RationalBox 4`. -/
def i6D688NestedBoxCell (box : RationalBox 4) :
    Set (((Real × Real) × Real) × Real) :=
  ((Icc (box.lower 0 : Real) (box.upper 0 : Real) ×ˢ
      Icc (box.lower 1 : Real) (box.upper 1 : Real)) ×ˢ
    Icc (box.lower 2 : Real) (box.upper 2 : Real)) ×ˢ
  Icc (box.lower 3 : Real) (box.upper 3 : Real)

theorem i6D688_mem_nestedBoxCell_iff
    {box : RationalBox 4}
    {x : (((Real × Real) × Real) × Real)} :
    x ∈ i6D688NestedBoxCell box ↔
      i6D686Coordinates x ∈ box.region := by
  rcases x with ⟨⟨⟨u, v⟩, w⟩, t⟩
  simp only [i6D688NestedBoxCell, i6D686Coordinates, RationalBox.region,
    Set.mem_prod, Set.mem_Icc]
  constructor
  · intro h
    constructor
    · intro i
      fin_cases i
      · exact h.1.1.1.1
      · exact h.1.1.2.1
      · exact h.1.2.1
      · exact h.2.1
    · intro i
      fin_cases i
      · exact h.1.1.1.2
      · exact h.1.1.2.2
      · exact h.1.2.2
      · exact h.2.2
  · intro h
    have h0 : (box.lower 0 : Real) ≤ u ∧ u ≤ (box.upper 0 : Real) := by
      simpa [Matrix.cons_val] using
        And.intro (h.1 (0 : Fin 4)) (h.2 (0 : Fin 4))
    have h1 : (box.lower 1 : Real) ≤ v ∧ v ≤ (box.upper 1 : Real) := by
      simpa [Matrix.cons_val] using
        And.intro (h.1 (1 : Fin 4)) (h.2 (1 : Fin 4))
    have h2 : (box.lower 2 : Real) ≤ w ∧ w ≤ (box.upper 2 : Real) := by
      simpa [Matrix.cons_val] using
        And.intro (h.1 (2 : Fin 4)) (h.2 (2 : Fin 4))
    have h3 : (box.lower 3 : Real) ≤ t ∧ t ≤ (box.upper 3 : Real) := by
      simpa [Matrix.cons_val] using
        And.intro (h.1 (3 : Fin 4)) (h.2 (3 : Fin 4))
    exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩

theorem i6D688_nestedPoint_image_region (box : RationalBox 4) :
    i6D686NestedPoint '' box.region = i6D688NestedBoxCell box := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply i6D688_mem_nestedBoxCell_iff.mpr
    simpa [i6D686Coordinates_nestedPoint] using hz
  · intro hx
    refine ⟨i6D686Coordinates x, ?_, ?_⟩
    · exact i6D688_mem_nestedBoxCell_iff.mp hx
    · exact i6D686NestedPoint_coordinates x

theorem i6D688NestedBoxCell_measurable (box : RationalBox 4) :
    MeasurableSet (i6D688NestedBoxCell box) := by
  unfold i6D688NestedBoxCell
  exact ((measurableSet_Icc.prod measurableSet_Icc).prod
    measurableSet_Icc).prod measurableSet_Icc

theorem i6D688NestedBoxCell_finite (box : RationalBox 4) :
    volume (i6D688NestedBoxCell box) ≠ (⊤ : ENNReal) := by
  unfold i6D688NestedBoxCell
  exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
    isCompact_Icc).measure_ne_top

theorem i6D688NestedBoxCell_volume_real
    (box : RationalBox 4) (hordered : box.IsOrdered) :
    volume.real (i6D688NestedBoxCell box) =
      (box.volumeRat : Real) := by
  have h0 : (box.lower 0 : Real) ≤ (box.upper 0 : Real) :=
    (Rat.cast_le (K := Real)).2 (hordered 0)
  have h1 : (box.lower 1 : Real) ≤ (box.upper 1 : Real) :=
    (Rat.cast_le (K := Real)).2 (hordered 1)
  have h2 : (box.lower 2 : Real) ≤ (box.upper 2 : Real) :=
    (Rat.cast_le (K := Real)).2 (hordered 2)
  have h3 : (box.lower 3 : Real) ≤ (box.upper 3 : Real) :=
    (Rat.cast_le (K := Real)).2 (hordered 3)
  unfold i6D688NestedBoxCell
  change (((volume.prod volume).prod volume).prod volume).real
      (((Icc (box.lower 0 : Real) (box.upper 0 : Real) ×ˢ
        Icc (box.lower 1 : Real) (box.upper 1 : Real)) ×ˢ
      Icc (box.lower 2 : Real) (box.upper 2 : Real)) ×ˢ
      Icc (box.lower 3 : Real) (box.upper 3 : Real)) = _
  rw [MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod]
  rw [Real.volume_real_Icc_of_le h0,
    Real.volume_real_Icc_of_le h1,
    Real.volume_real_Icc_of_le h2,
    Real.volume_real_Icc_of_le h3]
  simp [RationalBox.volumeRat, Fin.prod_univ_four, mul_assoc]

end

end PrimesRestrictedDigits
