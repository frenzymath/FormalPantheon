import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineSlabCount
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIProjectedZeroNormal
import Mathlib.Tactic.Linarith

/-!
# Embedded Type II affine normals

Source-coordinate affine forms are extended by zero to the stable factor tuple. This preserves
both their value and their `l1` mass, and supplies the weak wall-crossing bridge used before
projected slab counting.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Extend a source normal by zero away from an injective coordinate embedding. -/
noncomputable def typeIIAffineLiftNormal {s r : Nat}
    (embedding : Fin s ↪ Fin r) (normal : Fin s -> Real) : Fin r -> Real :=
  Function.extend embedding normal 0

/-- The full-coordinate preimage of a source region along an embedding. -/
def typeIIAffineEmbeddingPreimageRegion {s r : Nat}
    (embedding : Fin s ↪ Fin r)
    (region : Set (Fin s -> Real)) : Set (Fin r -> Real) :=
  {x | (fun i => x (embedding i)) ∈ region}

@[simp] theorem typeIIAffineLiftNormal_apply {s r : Nat}
    (embedding : Fin s ↪ Fin r) (normal : Fin s -> Real) (i : Fin s) :
    typeIIAffineLiftNormal embedding normal (embedding i) = normal i := by
  change Function.extend embedding normal
      (fun _ : Fin r => (0 : Real)) (embedding i) = normal i
  exact embedding.injective.extend_apply normal (fun _ : Fin r => (0 : Real)) i

theorem typeIIAffineLiftNormal_apply_of_not_mem_range {s r : Nat}
    (embedding : Fin s ↪ Fin r) (normal : Fin s -> Real) {j : Fin r}
    (hj : j ∉ Set.range embedding) :
    typeIIAffineLiftNormal embedding normal j = 0 := by
  have hno : ¬ ∃ i, embedding i = j := by
    intro h
    exact hj h
  change Function.extend embedding normal
      (fun _ : Fin r => (0 : Real)) j = 0
  rw [Function.extend_apply' normal (fun _ : Fin r => (0 : Real)) j hno]

@[simp] theorem typeIIAffineLiftNormal_eq_zero_iff {s r : Nat}
    (embedding : Fin s ↪ Fin r) (normal : Fin s -> Real) :
    typeIIAffineLiftNormal embedding normal = 0 ↔ normal = 0 := by
  constructor
  · intro hzero
    funext i
    have hi := congrFun hzero (embedding i)
    simpa only [typeIIAffineLiftNormal_apply, Pi.zero_apply] using hi
  · intro hzero
    funext j
    by_cases hj : j ∈ Set.range embedding
    · obtain ⟨i, rfl⟩ := hj
      simp [hzero]
    · exact typeIIAffineLiftNormal_apply_of_not_mem_range embedding normal hj

private theorem sum_typeIIAffineLiftNormal_mul {s r : Nat}
    (embedding : Fin s ↪ Fin r) (normal : Fin s -> Real)
    (x : Fin r -> Real) :
    (∑ j, typeIIAffineLiftNormal embedding normal j * x j) =
      (∑ i, normal i * x (embedding i)) := by
  classical
  let image : Finset (Fin r) := Finset.univ.image embedding
  have himage : image ⊆ (Finset.univ : Finset (Fin r)) := by
    intro j hj
    simp only [image, Finset.mem_image] at hj
    simp
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin r)) \ image,
      typeIIAffineLiftNormal embedding normal j * x j = 0 := by
    intro j hj
    have hjnot : j ∉ image := (Finset.mem_sdiff.mp hj).2
    have hno : ¬ ∃ i, embedding i = j := by
      intro hex
      rcases hex with ⟨i, hi⟩
      apply hjnot
      simpa [image] using
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    change Function.extend embedding normal
      (fun _ : Fin r => (0 : Real)) j * x j = 0
    rw [Function.extend_apply' normal (fun _ : Fin r => (0 : Real)) j hno]
    simp
  have hsum :
      (∑ j ∈ image,
        typeIIAffineLiftNormal embedding normal j * x j) =
        (∑ j, typeIIAffineLiftNormal embedding normal j * x j) := by
    exact Finset.sum_subset_zero_on_sdiff (s₁ := image)
      (s₂ := Finset.univ)
      (f := fun j => typeIIAffineLiftNormal embedding normal j * x j)
      (g := fun j => typeIIAffineLiftNormal embedding normal j * x j)
      himage hzero (by intro j hj; rfl)
  calc
    (∑ j, typeIIAffineLiftNormal embedding normal j * x j) =
        (∑ j ∈ image,
          typeIIAffineLiftNormal embedding normal j * x j) := hsum.symm
    _ = (∑ i,
        typeIIAffineLiftNormal embedding normal (embedding i) * x (embedding i)) := by
      dsimp only [image]
      rw [Finset.sum_image]
      exact embedding.injective.injOn
    _ = (∑ i, normal i * x (embedding i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp

theorem typeIIAffineValue_liftNormal {s r : Nat}
    (embedding : Fin s ↪ Fin r) (normal : Fin s -> Real)
    (x : Fin r -> Real) :
    typeIIAffineValue (typeIIAffineLiftNormal embedding normal) x =
      typeIIAffineValue normal (fun i => x (embedding i)) := by
  exact sum_typeIIAffineLiftNormal_mul embedding normal x

theorem typeIIAffineNormalMass_liftNormal {s r : Nat}
    (embedding : Fin s ↪ Fin r) (normal : Fin s -> Real) :
    typeIIAffineNormalMass (typeIIAffineLiftNormal embedding normal) =
      typeIIAffineNormalMass normal := by
  classical
  have habs : ∀ j : Fin r,
      |typeIIAffineLiftNormal embedding normal j| =
        typeIIAffineLiftNormal embedding (fun i => |normal i|) j := by
    intro j
    by_cases hj : j ∈ Set.range embedding
    · obtain ⟨i, rfl⟩ := hj
      simp
    · rw [typeIIAffineLiftNormal_apply_of_not_mem_range embedding normal hj,
        typeIIAffineLiftNormal_apply_of_not_mem_range embedding (fun i => |normal i|) hj]
      simp
  rw [typeIIAffineNormalMass, typeIIAffineNormalMass]
  calc
    (∑ j, |typeIIAffineLiftNormal embedding normal j|) =
        ∑ j, typeIIAffineLiftNormal embedding (fun i => |normal i|) j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact habs j
    _ = (∑ j, typeIIAffineLiftNormal embedding (fun i => |normal i|) j *
        (1 : Real)) := by simp
    _ = ∑ i, |normal i| * (1 : Real) := by
      exact sum_typeIIAffineLiftNormal_mul embedding (fun i => |normal i|)
        (fun _ => (1 : Real))
    _ = ∑ i, |normal i| := by simp

def TypeIIAffineHalfspacePresentation.liftAlongEmbedding
    {s r : Nat} {region : Set (Fin s -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region)
    (embedding : Fin s ↪ Fin r) :
    TypeIIAffineHalfspacePresentation
      (typeIIAffineEmbeddingPreimageRegion embedding region) where
  constraintCount := presentation.constraintCount
  normal := fun j => typeIIAffineLiftNormal embedding (presentation.normal j)
  bound := presentation.bound
  mem_iff := by
    intro x
    change (fun i => x (embedding i)) ∈ region ↔ _
    rw [presentation.mem_iff]
    constructor
    · intro hx j
      simpa only [typeIIAffineValue_liftNormal] using hx j
    · intro hx j
      have hj := hx j
      simpa only [typeIIAffineValue_liftNormal] using hj

theorem typeIIProjectedAffineNormal_ne_zero_of_apply_eq_zero
    {k : Nat} {normal : Fin (k + 1) -> Real} {j : Fin (k + 1)}
    (hnormal : normal ≠ 0) (hj : normal j = 0) :
    typeIIProjectedAffineNormal normal ≠ 0 := by
  intro hzero
  apply hnormal
  have hcoeff := (typeIIProjectedAffineNormal_eq_zero_iff normal).mp hzero
  have hlast : normal (Fin.last k) = 0 := by
    cases j using Fin.lastCases with
    | last => exact hj
    | cast jj =>
      have heq := hcoeff jj
      exact heq.symm.trans hj
  funext a
  refine Fin.lastCases hlast (fun aa => ?_) a
  exact (hcoeff aa).trans hlast

theorem typeIIProjectedAffineNormal_lift_ne_zero_of_offRange
    {s k : Nat} (embedding : Fin s ↪ Fin (k + 1))
    (normal : Fin s -> Real)
    (hnormal : normal ≠ 0) {spare : Fin (k + 1)}
    (hspare : spare ∉ Set.range embedding) :
    typeIIProjectedAffineNormal
      (typeIIAffineLiftNormal embedding normal) ≠ 0 := by
  apply typeIIProjectedAffineNormal_ne_zero_of_apply_eq_zero
  · intro hzero
    apply hnormal
    exact (typeIIAffineLiftNormal_eq_zero_iff embedding normal).mp hzero
  · exact typeIIAffineLiftNormal_apply_of_not_mem_range embedding normal hspare

theorem exists_typeIIAffineLiftedCrossingSlab
    {s k : Nat} {region : Set (Fin s -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region)
    (embedding : Fin s ↪ Fin (k + 1)) {spare : Fin (k + 1)}
    (hspare : spare ∉ Set.range embedding)
    {xSource xTarget : Fin (k + 1) -> Real} {gamma : Real}
    (hxSource : (fun i => xSource (embedding i)) ∈ region)
    (hxTarget : (fun i => xTarget (embedding i)) ∉ region)
    (herror : forall j,
      abs (typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
        typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource)
        <= gamma) :
    exists j,
      typeIIProjectedAffineNormal
          (typeIIAffineLiftNormal embedding (presentation.normal j)) ≠ 0 ∧
      abs (typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
        presentation.bound j) <= gamma := by
  have hsourceAll : ∀ j,
      typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource <=
        presentation.bound j := by
    intro j
    have hj := (presentation.mem_iff (fun i => xSource (embedding i))).mp
      hxSource j
    simpa only [typeIIAffineValue_liftNormal] using hj
  have htargetExists : ∃ j,
      presentation.bound j <
        typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget := by
    classical
    by_contra hnone
    apply hxTarget
    apply (presentation.mem_iff _).mpr
    intro j
    have hjnot : ¬ presentation.bound j <
        typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget := by
      intro hj
      exact hnone ⟨j, hj⟩
    have hjle := le_of_not_gt hjnot
    simpa only [typeIIAffineValue_liftNormal] using hjle
  obtain ⟨j, hjtarget⟩ := htargetExists
  have hsourceNormal : presentation.normal j ≠ 0 := by
    intro hzero
    have hliftZero :
        typeIIAffineLiftNormal embedding (presentation.normal j) = 0 :=
      (typeIIAffineLiftNormal_eq_zero_iff embedding (presentation.normal j)).2 hzero
    have hsourceZero :
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource = 0 := by
      rw [hliftZero]
      simp [typeIIAffineValue]
    have htargetZero :
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget = 0 := by
      rw [hliftZero]
      simp [typeIIAffineValue]
    linarith [hsourceAll j]
  have hliftNormal :
      typeIIAffineLiftNormal embedding (presentation.normal j) ≠ 0 := by
    intro hzero
    apply hsourceNormal
    exact (typeIIAffineLiftNormal_eq_zero_iff embedding (presentation.normal j)).mp hzero
  refine ⟨j, ?_, ?_⟩
  · exact typeIIProjectedAffineNormal_ne_zero_of_apply_eq_zero
      hliftNormal
      (typeIIAffineLiftNormal_apply_of_not_mem_range embedding
        (presentation.normal j) hspare)
  · have hnonneg : 0 <=
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          presentation.bound j := by linarith
    rw [abs_of_nonneg hnonneg]
    have hgap :
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          presentation.bound j <=
        abs (typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource) := by
      have hle := le_abs_self
        (typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource)
      linarith [hsourceAll j]
    exact hgap.trans (herror j)

end

end PrimesRestrictedDigits
