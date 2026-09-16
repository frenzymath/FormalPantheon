import PrimesRestrictedDigits.BasicEstimates.FiniteRationalGeometry
import PrimesRestrictedDigits.BasicEstimates.FiniteRationalSubdivision
import PrimesRestrictedDigits.BasicEstimates.FiniteRationalIntegralReplay
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
neutral three-dimensional rational replay adapter.

This module translates the coordinate/image/measure bridge for the native left-associated P0
carrier ((Real x Real) x Real). It transports externally supplied rational subdivision covers
and replay inequalities; it does not construct a tree or establish source-specific analytic
bounds.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

variable {alpha : Type*}

def sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 (z : Fin 3 → Real) : ((Real × Real) × Real) :=
  ((z 0, z 1), z 2)

def sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 (x : ((Real × Real) × Real)) : Fin 3 → Real :=
  ![x.1.1, x.1.2, x.2]

def sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 (box : RationalBox 3) :
    Set ((Real × Real) × Real) :=
  (Icc (box.lower 0 : Real) (box.upper 0 : Real) ×ˢ
      Icc (box.lower 1 : Real) (box.upper 1 : Real)) ×ˢ
    Icc (box.lower 2 : Real) (box.upper 2 : Real)

theorem sectionSixFirstLowCentralSmallI5P0RationalCoordinates3_nestedPoint3 (z : Fin 3 → Real) :
    sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 (sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 z) = z := by
  funext i
  fin_cases i <;> rfl

theorem sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3_coordinates3
    (x : ((Real × Real) × Real)) :
    sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x) = x := by
  rcases x with ⟨⟨u, v⟩, w⟩
  rfl

theorem sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3_measurable (box : RationalBox 3) :
    MeasurableSet (sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 box) := by
  unfold sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3
  exact (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc

theorem sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3_finite (box : RationalBox 3) :
    volume (sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 box) ≠ (⊤ : ENNReal) := by
  unfold sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3
  exact ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).measure_ne_top

theorem sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3_volume_real (box : RationalBox 3)
    (hordered : box.IsOrdered) :
    volume.real (sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 box) = (box.volumeRat : Real) := by
  have h0 : (box.lower 0 : Real) ≤ (box.upper 0 : Real) :=
    (Rat.cast_le (K := Real)).2 (hordered 0)
  have h1 : (box.lower 1 : Real) ≤ (box.upper 1 : Real) :=
    (Rat.cast_le (K := Real)).2 (hordered 1)
  have h2 : (box.lower 2 : Real) ≤ (box.upper 2 : Real) :=
    (Rat.cast_le (K := Real)).2 (hordered 2)
  unfold sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3
  change ((volume.prod volume).prod volume).real
      ((Icc (box.lower 0 : Real) (box.upper 0 : Real) ×ˢ
        Icc (box.lower 1 : Real) (box.upper 1 : Real)) ×ˢ
        Icc (box.lower 2 : Real) (box.upper 2 : Real)) = _
  rw [MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod]
  rw [Real.volume_real_Icc_of_le h0,
    Real.volume_real_Icc_of_le h1,
    Real.volume_real_Icc_of_le h2]
  simp [RationalBox.volumeRat, Fin.prod_univ_succ, mul_assoc]

theorem sectionSixFirstLowCentralSmallI5P0RationalCoordinates3_preimage_eq_cell (box : RationalBox 3) :
    {x : ((Real × Real) × Real) | sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x ∈ box.region} =
      sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 box := by
  ext x
  rcases x with ⟨⟨u, v⟩, w⟩
  simp only [sectionSixFirstLowCentralSmallI5P0RationalCoordinates3, RationalBox.region, sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3,
    Set.mem_setOf_eq, Set.mem_Icc, Set.mem_prod]
  constructor
  · intro h
    have h0l := h.1 0
    have h1l := h.1 1
    have h2l := h.1 2
    have h0u := h.2 0
    have h1u := h.2 1
    have h2u := h.2 2
    simp [Matrix.cons_val] at h0l h1l h2l h0u h1u h2u
    exact ⟨⟨⟨h0l, h0u⟩, h1l, h1u⟩, h2l, h2u⟩
  · rintro ⟨⟨⟨h0l, h0u⟩, h1l, h1u⟩, h2l, h2u⟩
    constructor
    · intro i
      fin_cases i
      · simpa using h0l
      · simpa using h1l
      · simpa using h2l
    · intro i
      fin_cases i
      · simpa using h0u
      · simpa using h1u
      · simpa using h2u

private theorem sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3_mem_cell
    {box : RationalBox 3} {z : Fin 3 → Real}
    (hz : z ∈ box.region) :
    sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 z ∈ sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 box := by
  have hz' : sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 z ∈
      {x : ((Real × Real) × Real) |
        sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x ∈ box.region} := by
    change sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 (sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 z) ∈ box.region
    simpa only [sectionSixFirstLowCentralSmallI5P0RationalCoordinates3_nestedPoint3] using hz
  rw [sectionSixFirstLowCentralSmallI5P0RationalCoordinates3_preimage_eq_cell] at hz'
  exact hz'

theorem sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3_image_region (box : RationalBox 3) :
    sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 '' box.region = sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 box := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3_mem_cell hz
  · intro hx
    refine ⟨sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x, ?_, ?_⟩
    · have hx' : x ∈
        {x : ((Real × Real) × Real) |
          sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x ∈ box.region} := by
        rw [sectionSixFirstLowCentralSmallI5P0RationalCoordinates3_preimage_eq_cell]
        exact hx
      exact hx'
    · exact sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3_coordinates3 x

/-
  Coordinate transport of the generic subdivision cover.  This theorem is
  deliberately only a cover statement: it does not supply cell measures,
  payload bounds, or an integral estimate.
-/
theorem sectionSixFirstLowCentralSmallI5P0RationalNestedRetainedCover
    (constraints : List (RationalAffineConstraint 3))
    (payloadValid : RationalBox 3 → alpha → Bool)
    (box : RationalBox 3) (tree : RationalSubdivision 3 alpha)
    (target : Set ((Real × Real) × Real))
    (hvalid : tree.coverValid constraints payloadValid box = true)
    (hconstraints : ∀ x ∈ target, ∀ c ∈ constraints,
      c.holds (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x))
    (hroot : target ⊆ sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 box) :
    target ⊆ ⋃ i : Fin (tree.retainedLeaves box).length,
      sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 ((tree.retainedLeaves box).get i).1 := by
  let targetCoords : Set (Fin 3 → Real) :=
    {z | sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 z ∈ target}
  have hconstraintsCoords : ∀ z ∈ targetCoords, ∀ c ∈ constraints,
      c.holds z := by
    intro z hz c hc
    exact hconstraints (sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 z) hz c hc
  have hrootCoords : targetCoords ⊆ box.region := by
    intro z hz
    have hzCell : sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 z ∈ sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 box := hroot hz
    have hzPre : sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 z ∈
        {x : ((Real × Real) × Real) |
          sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x ∈ box.region} := by
      rw [sectionSixFirstLowCentralSmallI5P0RationalCoordinates3_preimage_eq_cell]
      exact hzCell
    change sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 (sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 z) ∈ box.region at hzPre
    simpa only [sectionSixFirstLowCentralSmallI5P0RationalCoordinates3_nestedPoint3] using hzPre
  intro x hx
  have hzMem : sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x ∈ targetCoords := by
    change sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x) ∈ target
    simpa only [sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3_coordinates3] using hx
  have hcoordCover := RationalSubdivision.target_subset_retainedLeaves
    constraints payloadValid box tree targetCoords hvalid
      hconstraintsCoords hrootCoords
  have hleafUnion : sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x ∈
      ⋃ i : Fin (tree.retainedLeaves box).length,
        ((tree.retainedLeaves box).get i).1.region := hcoordCover hzMem
  rcases Set.mem_iUnion.mp hleafUnion with ⟨i, hi⟩
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  have hxPre : x ∈ {y : ((Real × Real) × Real) |
      sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 y ∈ ((tree.retainedLeaves box).get i).1.region} := by
    exact hi
  rw [sectionSixFirstLowCentralSmallI5P0RationalCoordinates3_preimage_eq_cell] at hxPre
  exact hxPre

/-
  Full generic replay transport for the nested three-dimensional carrier.
  All analytic information remains explicit hypotheses (`hf`, `hbound`,
  and nonnegative rational payloads); this is an adapter, not a certificate
  for any particular P0 tree.
-/
theorem sectionSixFirstLowCentralSmallI5P0Rational_setIntegral_le_nestedReplayWeight
    (constraints : List (RationalAffineConstraint 3))
    (payloadValid : RationalBox 3 → alpha → Bool)
    (box : RationalBox 3) (tree : RationalSubdivision 3 alpha)
    (payloadWeight : RationalBox 3 → alpha → Rat)
    (target : Set ((Real × Real) × Real))
    (f : ((Real × Real) × Real) → Real)
    (hvalid : tree.coverValid constraints payloadValid box = true)
    (htarget : MeasurableSet target)
    (hf : IntegrableOn f target volume)
    (hconstraints : ∀ x ∈ target, ∀ c ∈ constraints,
      c.holds (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 x))
    (hroot : target ⊆ sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 box)
    (hweightNonneg : ∀ i : Fin (tree.retainedLeaves box).length,
      0 ≤ payloadWeight ((tree.retainedLeaves box).get i).1
        ((tree.retainedLeaves box).get i).2)
    (hbound : ∀ i : Fin (tree.retainedLeaves box).length,
      ∀ x ∈ target ∩
        sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 ((tree.retainedLeaves box).get i).1,
        f x ≤ (payloadWeight ((tree.retainedLeaves box).get i).1
          ((tree.retainedLeaves box).get i).2 : Real)) :
    (∫ x in target, f x ∂volume) ≤
      (tree.replayWeightRat box payloadWeight : Real) := by
  let nestedCell : Fin (tree.retainedLeaves box).length →
      Set ((Real × Real) × Real) :=
    fun i => sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3 ((tree.retainedLeaves box).get i).1
  have hcover : target ⊆ ⋃ i, nestedCell i := by
    simpa only [nestedCell] using
      sectionSixFirstLowCentralSmallI5P0RationalNestedRetainedCover constraints payloadValid box tree target
        hvalid hconstraints hroot
  apply RationalSubdivision.setIntegral_le_replayWeightRat_of_retainedLeaves_cover
    (μ := volume) (tree := tree) (box := box)
    (payloadWeight := payloadWeight) (target := target)
    (cell := nestedCell) (f := f)
  · exact htarget
  · intro i
    exact sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3_measurable _
  · intro i
    exact sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3_finite _
  · exact hf
  · exact hweightNonneg
  · intro i
    have hleaf := RationalSubdivision.valid_of_mem_retainedLeaves
      constraints payloadValid box tree hvalid
      (List.get_mem (tree.retainedLeaves box) i)
    simpa [nestedCell] using
      sectionSixFirstLowCentralSmallI5P0RationalNestedBoxCell3_volume_real _ hleaf.1
  · exact hcover
  · intro i x hx
    exact hbound i x hx

/- A concrete nondegenerate box catches coordinate order and volume casts. -/
