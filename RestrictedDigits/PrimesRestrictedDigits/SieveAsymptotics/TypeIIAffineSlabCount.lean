import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineHalfspaces
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite Type II affine-slab counts

This file proves the project-specific grid count behind the boundary estimate on published p.
166. It counts only nonzero affine normals and uses the coarse, endpoint-safe fiber constant
`4 * k + 1`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The `l1` mass of a finite affine normal. -/
def typeIIAffineNormalMass {k : Nat} (normal : Fin k -> Real) : Real :=
  ∑ i, |normal i|

/-- A coordinate at which the absolute value of a nonempty finite normal is
maximal. -/
noncomputable def typeIIAffineMaxAbsCoordinate {n : Nat}
    (normal : Fin (n + 1) -> Real) : Fin (n + 1) :=
  Classical.choose <|
    Finset.exists_max_image Finset.univ (fun i => |normal i|)
      Finset.univ_nonempty

/-- Every coefficient is bounded by the selected maximal coefficient. -/
theorem abs_typeIIAffineMaxAbsCoordinate_ge {n : Nat}
    (normal : Fin (n + 1) -> Real) (i : Fin (n + 1)) :
    |normal i| <= |normal (typeIIAffineMaxAbsCoordinate normal)| := by
  exact (Classical.choose_spec <|
    Finset.exists_max_image Finset.univ (fun j => |normal j|)
      Finset.univ_nonempty).2 i (Finset.mem_univ i)

/-- A nonzero normal has a strictly positive maximal absolute coefficient. -/
theorem abs_typeIIAffineMaxAbsCoordinate_pos {n : Nat}
    {normal : Fin (n + 1) -> Real} (hnormal : normal ≠ 0) :
    0 < |normal (typeIIAffineMaxAbsCoordinate normal)| := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hnormal
  exact (abs_pos.mpr hi).trans_le
    (abs_typeIIAffineMaxAbsCoordinate_ge normal i)

/-- The `l1` mass is at most dimension times the maximal coefficient. -/
theorem typeIIAffineNormalMass_le_card_mul_max {n : Nat}
    (normal : Fin (n + 1) -> Real) :
    typeIIAffineNormalMass normal <=
      ((n + 1 : Nat) : Real) *
        |normal (typeIIAffineMaxAbsCoordinate normal)| := by
  calc
    typeIIAffineNormalMass normal <=
        ∑ _i : Fin (n + 1),
          |normal (typeIIAffineMaxAbsCoordinate normal)| := by
      apply Finset.sum_le_sum
      intro i hi
      exact abs_typeIIAffineMaxAbsCoordinate_ge normal i
    _ = ((n + 1 : Nat) : Real) *
        |normal (typeIIAffineMaxAbsCoordinate normal)| := by simp

/-- Natural grid anchors whose scaled bases lie in the absolute slab forced
by a doubled cube crossing one affine constraint.  Zero normals are excluded
because their slabs need not be codimension one. -/
noncomputable def typeIIAffineConstraintSlabAnchors {k : Nat}
    (delta : Real) (normal : Fin k -> Real) (bound : Real) :
    Finset (Fin k -> Nat) := by
  classical
  exact (typeIINaturalCubeGrid k delta).filter fun anchor =>
    normal ≠ 0 ∧
      |typeIIAffineValue normal
          (scaledNaturalCubeAnchor delta anchor) - bound| <=
        2 * delta * typeIIAffineNormalMass normal

@[simp] theorem mem_typeIIAffineConstraintSlabAnchors
    {k : Nat} {delta bound : Real} {normal : Fin k -> Real}
    {anchor : Fin k -> Nat} :
    anchor ∈ typeIIAffineConstraintSlabAnchors delta normal bound <->
      anchor ∈ typeIINaturalCubeGrid k delta ∧ normal ≠ 0 ∧
        |typeIIAffineValue normal
            (scaledNaturalCubeAnchor delta anchor) - bound| <=
          2 * delta * typeIIAffineNormalMass normal := by
  classical
  simp [typeIIAffineConstraintSlabAnchors]

/-- A finite set of naturals with diameter at most `width` has at most
`width + 1` elements. -/
theorem card_nat_finset_le_add_one_of_sub_le
    (s : Finset Nat) (width : Nat)
    (hdiameter : ∀ a ∈ s, ∀ b ∈ s, a <= b -> b - a <= width) :
    s.card <= width + 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  let lo := s.min' hs
  let hi := s.max' hs
  have hlo : lo ∈ s := s.min'_mem hs
  have hhi : hi ∈ s := s.max'_mem hs
  have hlohi : lo <= hi := s.min'_le_max' hs
  have hwidth : hi - lo <= width :=
    hdiameter lo hlo hi hhi hlohi
  have hsubset : s ⊆ Finset.Icc lo hi := by
    intro a ha
    exact Finset.mem_Icc.mpr ⟨s.min'_le a ha, s.le_max' a ha⟩
  calc
    s.card <= (Finset.Icc lo hi).card := Finset.card_le_card hsubset
    _ = hi + 1 - lo := Nat.card_Icc lo hi
    _ <= width + 1 := by omega

/-- In one `removeNth` fiber, the affine-value difference is exactly the
pivot contribution. -/
theorem typeIIAffineValue_scaled_sub_eq_of_removeNth_eq
    {n : Nat} (normal : Fin (n + 1) -> Real) (delta : Real)
    (pivot : Fin (n + 1)) (u v : Fin (n + 1) -> Nat)
    (hremove : pivot.removeNth u = pivot.removeNth v) :
    typeIIAffineValue normal (scaledNaturalCubeAnchor delta u) -
        typeIIAffineValue normal (scaledNaturalCubeAnchor delta v) =
      normal pivot * (((u pivot : Nat) : Real) - (v pivot : Nat)) * delta := by
  have htail :
      (∑ i : Fin n,
          normal (pivot.succAbove i) *
            scaledNaturalCubeAnchor delta u (pivot.succAbove i)) =
        ∑ i : Fin n,
          normal (pivot.succAbove i) *
            scaledNaturalCubeAnchor delta v (pivot.succAbove i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have huv : u (pivot.succAbove i) = v (pivot.succAbove i) := by
      simpa only [Fin.removeNth_apply] using congrFun hremove i
    simp only [scaledNaturalCubeAnchor, huv]
  rw [typeIIAffineValue, typeIIAffineValue,
    Fin.sum_univ_succAbove _ pivot, Fin.sum_univ_succAbove _ pivot,
    htail]
  simp only [scaledNaturalCubeAnchor]
  ring

/-- Two anchors in the same maximal-coordinate fiber of one absolute slab
have pivot values differing by at most `4 * (n + 1)`. -/
theorem typeIIAffineConstraintSlabAnchor_sub_le
    {n : Nat} {delta bound : Real}
    {normal : Fin (n + 1) -> Real}
    {u v : Fin (n + 1) -> Nat}
    (hdelta : 0 < delta)
    (hu : u ∈ typeIIAffineConstraintSlabAnchors delta normal bound)
    (hv : v ∈ typeIIAffineConstraintSlabAnchors delta normal bound)
    (hremove :
      (typeIIAffineMaxAbsCoordinate normal).removeNth u =
        (typeIIAffineMaxAbsCoordinate normal).removeNth v)
    (huv : u (typeIIAffineMaxAbsCoordinate normal) <=
      v (typeIIAffineMaxAbsCoordinate normal)) :
    v (typeIIAffineMaxAbsCoordinate normal) -
        u (typeIIAffineMaxAbsCoordinate normal) <=
      4 * (n + 1) := by
  let pivot := typeIIAffineMaxAbsCoordinate normal
  have hnormal : normal ≠ 0 :=
    (mem_typeIIAffineConstraintSlabAnchors.mp hu).2.1
  have hpivot : 0 < |normal pivot| :=
    abs_typeIIAffineMaxAbsCoordinate_pos hnormal
  have huSlab := (mem_typeIIAffineConstraintSlabAnchors.mp hu).2.2
  have hvSlab := (mem_typeIIAffineConstraintSlabAnchors.mp hv).2.2
  have hdiff :
      |typeIIAffineValue normal (scaledNaturalCubeAnchor delta u) -
          typeIIAffineValue normal (scaledNaturalCubeAnchor delta v)| <=
        4 * delta * typeIIAffineNormalMass normal := by
    calc
      |typeIIAffineValue normal (scaledNaturalCubeAnchor delta u) -
          typeIIAffineValue normal (scaledNaturalCubeAnchor delta v)| <=
          |typeIIAffineValue normal (scaledNaturalCubeAnchor delta u) - bound| +
            |bound - typeIIAffineValue normal
              (scaledNaturalCubeAnchor delta v)| := abs_sub_le _ _ _
      _ = |typeIIAffineValue normal
              (scaledNaturalCubeAnchor delta u) - bound| +
            |typeIIAffineValue normal
              (scaledNaturalCubeAnchor delta v) - bound| := by
          rw [abs_sub_comm bound]
      _ <= 2 * delta * typeIIAffineNormalMass normal +
            2 * delta * typeIIAffineNormalMass normal :=
          add_le_add huSlab hvSlab
      _ = 4 * delta * typeIIAffineNormalMass normal := by ring
  have hvalue := typeIIAffineValue_scaled_sub_eq_of_removeNth_eq
    normal delta pivot u v hremove
  rw [hvalue, abs_mul, abs_mul, abs_of_pos hdelta] at hdiff
  have hcancelDelta :
      |normal pivot| *
          |((u pivot : Nat) : Real) - (v pivot : Nat)| <=
        4 * typeIIAffineNormalMass normal := by
    apply le_of_mul_le_mul_left _ hdelta
    calc
      delta *
          (|normal pivot| *
            |((u pivot : Nat) : Real) - (v pivot : Nat)|) =
          |normal pivot| *
            |((u pivot : Nat) : Real) - (v pivot : Nat)| * delta := by ring
      _ <= 4 * delta * typeIIAffineNormalMass normal := hdiff
      _ = delta * (4 * typeIIAffineNormalMass normal) := by ring
  have hmass := typeIIAffineNormalMass_le_card_mul_max normal
  have hwithMax :
      |normal pivot| *
          |((u pivot : Nat) : Real) - (v pivot : Nat)| <=
        |normal pivot| * (4 * ((n + 1 : Nat) : Real)) := by
    calc
      |normal pivot| *
          |((u pivot : Nat) : Real) - (v pivot : Nat)| <=
          4 * typeIIAffineNormalMass normal := hcancelDelta
      _ <= 4 * (((n + 1 : Nat) : Real) * |normal pivot|) := by
        exact mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ = |normal pivot| * (4 * ((n + 1 : Nat) : Real)) := by ring
  have hgap :
      |((u pivot : Nat) : Real) - (v pivot : Nat)| <=
        4 * ((n + 1 : Nat) : Real) :=
    le_of_mul_le_mul_left hwithMax hpivot
  have hgapCast :
      (((v pivot - u pivot : Nat) : Nat) : Real) <=
        ((4 * (n + 1) : Nat) : Real) := by
    rw [Nat.cast_sub huv]
    have hnonneg :
        0 <= ((v pivot : Nat) : Real) - (u pivot : Nat) := by
      apply sub_nonneg.mpr
      exact_mod_cast huv
    rw [abs_sub_comm, abs_of_nonneg hnonneg] at hgap
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hgap
  exact_mod_cast hgapCast

/-- One nonzero affine slab meets only codimension-one many bounded natural
grid anchors. -/
theorem card_typeIIAffineConstraintSlabAnchors_le
    {n : Nat} {delta : Real} (hdelta : 0 < delta)
    (normal : Fin (n + 1) -> Real) (bound : Real) :
    (typeIIAffineConstraintSlabAnchors delta normal bound).card <=
      (4 * (n + 1) + 1) *
        typeIINaturalCubeGridSide delta ^ n := by
  classical
  by_cases hnormal : normal = 0
  · simp [typeIIAffineConstraintSlabAnchors, hnormal]
  let pivot := typeIIAffineMaxAbsCoordinate normal
  let slab := typeIIAffineConstraintSlabAnchors delta normal bound
  let tailGrid := typeIINaturalCubeGrid n delta
  change slab.card <=
    (4 * (n + 1) + 1) * typeIINaturalCubeGridSide delta ^ n
  rw [← card_typeIINaturalCubeGrid n delta]
  change slab.card <= (4 * (n + 1) + 1) * tailGrid.card
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := fun anchor => pivot.removeNth anchor)
    (s := slab) (t := tailGrid) ?_ (4 * (n + 1) + 1) ?_
  · intro anchor hanchor
    rw [mem_typeIINaturalCubeGrid]
    intro i
    have hgrid :=
      (mem_typeIIAffineConstraintSlabAnchors.mp hanchor).1
    exact (mem_typeIINaturalCubeGrid.mp hgrid) (pivot.succAbove i)
  · intro tail htail
    let fiber := {anchor ∈ slab | pivot.removeNth anchor = tail}
    let values := fiber.image fun anchor => anchor pivot
    have hinjective : Set.InjOn
        (fun anchor : Fin (n + 1) -> Nat => anchor pivot)
        (↑fiber : Set (Fin (n + 1) -> Nat)) := by
      intro u hu v hv huv
      have huremove : pivot.removeNth u = tail :=
        (Finset.mem_filter.mp hu).2
      have hvremove : pivot.removeNth v = tail :=
        (Finset.mem_filter.mp hv).2
      apply (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Nat) pivot).symm.injective
      rw [Fin.insertNthEquiv_symm_apply, Fin.insertNthEquiv_symm_apply]
      exact Prod.ext huv (huremove.trans hvremove.symm)
    have hcard : fiber.card = values.card := by
      exact (Finset.card_image_iff.mpr hinjective).symm
    have hdiameter :
        ∀ a ∈ values, ∀ b ∈ values, a <= b ->
          b - a <= 4 * (n + 1) := by
      intro a ha b hb hab
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      have huSlab : u ∈ slab := (Finset.mem_filter.mp hu).1
      have hvSlab : v ∈ slab := (Finset.mem_filter.mp hv).1
      have hremove : pivot.removeNth u = pivot.removeNth v :=
        (Finset.mem_filter.mp hu).2.trans
          (Finset.mem_filter.mp hv).2.symm
      exact typeIIAffineConstraintSlabAnchor_sub_le hdelta
        huSlab hvSlab hremove hab
    calc
      {anchor ∈ slab | pivot.removeNth anchor = tail}.card =
          fiber.card := rfl
      _ = values.card := hcard
      _ <= 4 * (n + 1) + 1 :=
        card_nat_finset_le_add_one_of_sub_le values
          (4 * (n + 1)) hdiameter

end

end PrimesRestrictedDigits
