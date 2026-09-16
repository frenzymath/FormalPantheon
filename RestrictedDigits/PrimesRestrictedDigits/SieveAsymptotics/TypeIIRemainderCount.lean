import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineSlabCount

/-!
# Type II source-region remainder counts

This file covers every remainder anchor by a slab from a fixed finite affine presentation and
proves the codimension-one count used on published p. 166.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Moving from the base of a doubled cube to any point of that cube changes
an affine value by at most two widths times the `l1` mass of its normal. -/
theorem abs_typeIIAffineValue_scaled_sub_le_of_mem_doubledProjectedCube
    {k : Nat} {delta : Real} {anchor : Fin k -> Nat}
    {x normal : Fin k -> Real} (_hdelta : 0 <= delta)
    (hx : x ∈ typeIIDoubledProjectedCube delta anchor) :
    |typeIIAffineValue normal (scaledNaturalCubeAnchor delta anchor) -
        typeIIAffineValue normal x| <=
      2 * delta * typeIIAffineNormalMass normal := by
  have hcoordinate (i : Fin k) :
      |scaledNaturalCubeAnchor delta anchor i - x i| <= 2 * delta := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hx i).1.le)]
    linarith [(hx i).2]
  rw [typeIIAffineValue, typeIIAffineValue]
  calc
    |(∑ i, normal i * scaledNaturalCubeAnchor delta anchor i) -
        ∑ i, normal i * x i| =
        |∑ i, normal i *
          (scaledNaturalCubeAnchor delta anchor i - x i)| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ <= ∑ i, |normal i *
          (scaledNaturalCubeAnchor delta anchor i - x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |normal i| *
          |scaledNaturalCubeAnchor delta anchor i - x i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
    _ <= ∑ i, |normal i| * (2 * delta) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hcoordinate i) (abs_nonneg _)
    _ = 2 * delta * typeIIAffineNormalMass normal := by
      rw [typeIIAffineNormalMass, ← Finset.sum_mul]
      ring

/-- The finite union of nonzero constraint slabs from one affine
presentation. -/
noncomputable def typeIIAffinePresentationSlabAnchors
    {k : Nat} {projectedRegion : Set (Fin k -> Real)} (delta : Real)
    (presentation : TypeIIAffineHalfspacePresentation projectedRegion) :
    Finset (Fin k -> Nat) := by
  classical
  exact Finset.univ.biUnion fun j =>
    typeIIAffineConstraintSlabAnchors delta
      (presentation.normal j) (presentation.bound j)

@[simp] theorem mem_typeIIAffinePresentationSlabAnchors
    {k : Nat} {projectedRegion : Set (Fin k -> Real)} {delta : Real}
    {presentation : TypeIIAffineHalfspacePresentation projectedRegion}
    {anchor : Fin k -> Nat} :
    anchor ∈ typeIIAffinePresentationSlabAnchors delta presentation <->
      ∃ j, anchor ∈ typeIIAffineConstraintSlabAnchors delta
        (presentation.normal j) (presentation.bound j) := by
  classical
  simp [typeIIAffinePresentationSlabAnchors]

/-- A doubled cube meeting a finitely presented region but not contained in
it has its anchor in one of the presentation's nonzero absolute slabs. -/
theorem mem_typeIIAffinePresentationSlabAnchors_of_crosses
    {k : Nat} {delta : Real} {anchor : Fin k -> Nat}
    {projectedRegion : Set (Fin k -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation projectedRegion)
    (hdelta : 0 < delta)
    (hgrid : anchor ∈ typeIINaturalCubeGrid k delta)
    (hmeets : (typeIIDoubledProjectedCube delta anchor ∩
      projectedRegion).Nonempty)
    (hnotSubset : ¬typeIIDoubledProjectedCube delta anchor ⊆
      projectedRegion) :
    anchor ∈ typeIIAffinePresentationSlabAnchors delta presentation := by
  rcases hmeets with ⟨x, hxCube, hxRegion⟩
  obtain ⟨y, hyCube, hyRegion⟩ := Set.not_subset.mp hnotSubset
  have hxConstraints := (presentation.mem_iff x).mp hxRegion
  have hyViolation : ∃ j,
      presentation.bound j <
        typeIIAffineValue (presentation.normal j) y := by
    by_contra hviolation
    apply hyRegion
    apply (presentation.mem_iff y).mpr
    intro j
    exact not_lt.mp (not_exists.mp hviolation j)
  obtain ⟨j, hyj⟩ := hyViolation
  have hxj := hxConstraints j
  have hnormal : presentation.normal j ≠ 0 := by
    intro hzero
    simp only [hzero, typeIIAffineValue, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero] at hxj hyj
    linarith
  have hxDistance :=
    abs_typeIIAffineValue_scaled_sub_le_of_mem_doubledProjectedCube
      hdelta.le (normal := presentation.normal j) hxCube
  have hyDistance :=
    abs_typeIIAffineValue_scaled_sub_le_of_mem_doubledProjectedCube
      hdelta.le (normal := presentation.normal j) hyCube
  have hslab :
      |typeIIAffineValue (presentation.normal j)
          (scaledNaturalCubeAnchor delta anchor) - presentation.bound j| <=
        2 * delta * typeIIAffineNormalMass (presentation.normal j) := by
    rw [abs_le]
    constructor
    · have hlower := neg_le_abs
        (typeIIAffineValue (presentation.normal j)
          (scaledNaturalCubeAnchor delta anchor) -
            typeIIAffineValue (presentation.normal j) y)
      linarith
    · have hupper := le_abs_self
        (typeIIAffineValue (presentation.normal j)
          (scaledNaturalCubeAnchor delta anchor) -
            typeIIAffineValue (presentation.normal j) x)
      linarith
  exact mem_typeIIAffinePresentationSlabAnchors.mpr
    ⟨j, mem_typeIIAffineConstraintSlabAnchors.mpr
      ⟨hgrid, hnormal, hslab⟩⟩

/--
remainder anchors are covered by the projected constraints pulled back from a full affine
presentation.
-/
theorem typeIIRemainderCubeAnchors_subset_affinePresentationSlabAnchors
    {k : Nat} {delta : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region)
    (hdelta : 0 < delta) :
    typeIIRemainderCubeAnchors delta region ⊆
      typeIIAffinePresentationSlabAnchors delta presentation.projected := by
  intro anchor hanchor
  have hremainder := mem_typeIIRemainderCubeAnchors.mp hanchor
  have hrelevant := mem_typeIIRelevantCubeAnchors.mp hremainder.1
  exact mem_typeIIAffinePresentationSlabAnchors_of_crosses
    presentation.projected hdelta hrelevant.1 hrelevant.2 hremainder.2

/-- In projected dimension zero, relevance already forces containment, so
there are no remainder anchors. -/
@[simp] theorem typeIIRemainderCubeAnchors_zero_eq_empty
    (delta : Real) (region : Set (Fin 1 -> Real)) :
    typeIIRemainderCubeAnchors delta region = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro anchor hanchor
  have hremainder := mem_typeIIRemainderCubeAnchors.mp hanchor
  rcases (mem_typeIIRelevantCubeAnchors.mp hremainder.1).2 with
    ⟨x, hxCube, hxRegion⟩
  apply hremainder.2
  intro y hyCube
  have hyx : y = x := Subsingleton.elim _ _
  simpa only [hyx] using hxRegion

/-- The exact finite remainder count in every projected dimension. -/
theorem card_typeIIRemainderCubeAnchors_le
    {k : Nat} {delta : Real} {region : Set (Fin (k + 1) -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region)
    (hdelta : 0 < delta) :
    (typeIIRemainderCubeAnchors delta region).card <=
      presentation.constraintCount * (4 * k + 1) *
        typeIINaturalCubeGridSide delta ^ (k - 1) := by
  cases k with
  | zero => simp
  | succ n =>
      let slabs :=
        typeIIAffinePresentationSlabAnchors delta presentation.projected
      have hsubset : typeIIRemainderCubeAnchors delta region ⊆ slabs :=
        typeIIRemainderCubeAnchors_subset_affinePresentationSlabAnchors
          presentation hdelta
      have hslabs : slabs.card <=
          presentation.constraintCount *
            ((4 * (n + 1) + 1) *
              typeIINaturalCubeGridSide delta ^ n) := by
        dsimp only [slabs, typeIIAffinePresentationSlabAnchors]
        calc
          (Finset.univ.biUnion fun j =>
              typeIIAffineConstraintSlabAnchors delta
                (presentation.projected.normal j)
                (presentation.projected.bound j)).card <=
              (Finset.univ : Finset
                (Fin presentation.constraintCount)).card *
                ((4 * (n + 1) + 1) *
                  typeIINaturalCubeGridSide delta ^ n) := by
            apply Finset.card_biUnion_le_card_mul
            intro j hj
            exact card_typeIIAffineConstraintSlabAnchors_le hdelta
              (presentation.projected.normal j)
              (presentation.projected.bound j)
          _ = presentation.constraintCount *
              ((4 * (n + 1) + 1) *
                typeIINaturalCubeGridSide delta ^ n) := by simp
      calc
        (typeIIRemainderCubeAnchors delta region).card <= slabs.card :=
          Finset.card_le_card hsubset
        _ <= presentation.constraintCount *
            ((4 * (n + 1) + 1) *
              typeIINaturalCubeGridSide delta ^ n) := hslabs
        _ = presentation.constraintCount * (4 * (n + 1) + 1) *
            typeIINaturalCubeGridSide delta ^ n := by simp [Nat.mul_assoc]

/-- Source-shaped codimension-one estimate: the positive constant is fixed
from the presentation before the width is quantified. -/
theorem exists_typeIIRemainderCubeAnchorCard_upper
    {k : Nat} {region : Set (Fin (k + 1) -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region) :
    ∃ Cregion : Real, 0 < Cregion ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 ->
        ((typeIIRemainderCubeAnchors delta region).card : Real) <=
          Cregion * delta⁻¹ ^ (k - 1) := by
  let coefficient : Real :=
    (presentation.constraintCount : Real) * ((4 * k + 1 : Nat) : Real)
  refine ⟨1 + coefficient * 2 ^ (k - 1), by positivity, ?_⟩
  intro delta hdelta hdeltaOne
  have hcardNat := card_typeIIRemainderCubeAnchors_le presentation hdelta
  have hcardReal :
      ((typeIIRemainderCubeAnchors delta region).card : Real) <=
        coefficient * (typeIINaturalCubeGridSide delta : Real) ^ (k - 1) := by
    dsimp only [coefficient]
    exact_mod_cast hcardNat
  have hsidePow :
      (typeIINaturalCubeGridSide delta : Real) ^ (k - 1) <=
        (2 / delta) ^ (k - 1) :=
    pow_le_pow_left₀ (by positivity)
      (typeIINaturalCubeGridSide_cast_le_two_div hdelta hdeltaOne) _
  have hinvPow : 0 <= delta⁻¹ ^ (k - 1) := by positivity
  calc
    ((typeIIRemainderCubeAnchors delta region).card : Real) <=
        coefficient * (typeIINaturalCubeGridSide delta : Real) ^ (k - 1) :=
      hcardReal
    _ <= coefficient * (2 / delta) ^ (k - 1) :=
      mul_le_mul_of_nonneg_left hsidePow (by positivity)
    _ = coefficient * 2 ^ (k - 1) * delta⁻¹ ^ (k - 1) := by
      rw [div_eq_mul_inv, mul_pow]
      ring
    _ <= (1 + coefficient * 2 ^ (k - 1)) * delta⁻¹ ^ (k - 1) := by
      nlinarith

end

end PrimesRestrictedDigits
