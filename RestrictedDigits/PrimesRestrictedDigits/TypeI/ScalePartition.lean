import PrimesRestrictedDigits.TypeI.DecadePartition

/-!
# Small and large Type I scale partition

This splits the active real-capped decimal scales at the threshold used in the proof of
published Proposition 7.1. Equality belongs to the small branch.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Active Type I scales above the strict source large-band threshold. -/
def typeILargeDecadeScales
    (saving : Real) (length : Nat) (Q : Real) : Finset Real :=
  (typeIDecadeScalesBelow Q).filter fun R =>
    Real.log (((10 ^ length : Nat) : Real)) ^ (4 * saving + 8) < R

/-- Active Type I scales at or below the source small-band threshold. -/
def typeISmallDecadeScales
    (saving : Real) (length : Nat) (Q : Real) : Finset Real :=
  (typeIDecadeScalesBelow Q).filter fun R =>
    R ≤ Real.log (((10 ^ length : Nat) : Real)) ^ (4 * saving + 8)

theorem mem_typeISmallDecadeScales_iff
    {saving : Real} {length : Nat} {Q R : Real} :
    R ∈ typeISmallDecadeScales saving length Q ↔
      R ∈ typeIDecadeScalesBelow Q ∧
        R ≤ Real.log (((10 ^ length : Nat) : Real)) ^
          (4 * saving + 8) := by
  exact Finset.mem_filter

theorem mem_typeILargeDecadeScales_iff
    {saving : Real} {length : Nat} {Q R : Real} :
    R ∈ typeILargeDecadeScales saving length Q ↔
      R ∈ typeIDecadeScalesBelow Q ∧
        Real.log (((10 ^ length : Nat) : Real)) ^
          (4 * saving + 8) < R := by
  exact Finset.mem_filter

/-- On the active carrier, large membership is failure of weak small
membership. -/
theorem mem_typeILargeDecadeScales_iff_not_mem_small
    {saving : Real} {length : Nat} {Q R : Real}
    (hR : R ∈ typeIDecadeScalesBelow Q) :
    R ∈ typeILargeDecadeScales saving length Q ↔
      R ∉ typeISmallDecadeScales saving length Q := by
  rw [mem_typeILargeDecadeScales_iff, mem_typeISmallDecadeScales_iff]
  simp only [hR, true_and, not_le]

/-- Equality with the threshold is assigned to the small branch. -/
theorem mem_typeISmallDecadeScales_of_eq_threshold
    {saving : Real} {length : Nat} {Q R : Real}
    (hR : R ∈ typeIDecadeScalesBelow Q)
    (hEq : R = Real.log (((10 ^ length : Nat) : Real)) ^
      (4 * saving + 8)) :
    R ∈ typeISmallDecadeScales saving length Q := by
  rw [mem_typeISmallDecadeScales_iff]
  exact ⟨hR, hEq.le⟩

theorem not_mem_typeILargeDecadeScales_of_eq_threshold
    {saving : Real} {length : Nat} {Q R : Real}
    (hEq : R = Real.log (((10 ^ length : Nat) : Real)) ^
      (4 * saving + 8)) :
    R ∉ typeILargeDecadeScales saving length Q := by
  rw [mem_typeILargeDecadeScales_iff]
  rintro ⟨_, hlt⟩
  subst R
  exact (lt_irrefl _) hlt

theorem typeISmallDecadeScales_subset
    (saving : Real) (length : Nat) (Q : Real) :
    typeISmallDecadeScales saving length Q ⊆ typeIDecadeScalesBelow Q :=
  Finset.filter_subset _ _

theorem typeILargeDecadeScales_subset
    (saving : Real) (length : Nat) (Q : Real) :
    typeILargeDecadeScales saving length Q ⊆ typeIDecadeScalesBelow Q :=
  Finset.filter_subset _ _

/-- The weak small branch and strict large branch are disjoint. -/
theorem typeISmallDecadeScales_disjoint_typeILargeDecadeScales
    (saving : Real) (length : Nat) (Q : Real) :
    Disjoint (typeISmallDecadeScales saving length Q)
      (typeILargeDecadeScales saving length Q) := by
  classical
  simpa only [typeISmallDecadeScales, typeILargeDecadeScales, not_le] using
    (Finset.disjoint_filter_filter_not
      (typeIDecadeScalesBelow Q) (typeIDecadeScalesBelow Q)
      (fun R => R ≤
        Real.log (((10 ^ length : Nat) : Real)) ^ (4 * saving + 8)))

/-- The two threshold branches recover every active real decade scale. -/
theorem typeISmallDecadeScales_union_typeILargeDecadeScales
    (saving : Real) (length : Nat) (Q : Real) :
    typeISmallDecadeScales saving length Q ∪
        typeILargeDecadeScales saving length Q =
      typeIDecadeScalesBelow Q := by
  classical
  simpa only [typeISmallDecadeScales, typeILargeDecadeScales, not_le] using
    (Finset.filter_union_filter_not_eq
      (p := fun R => R ≤
        Real.log (((10 ^ length : Nat) : Real)) ^ (4 * saving + 8))
      (typeIDecadeScalesBelow Q))

/-- Exact additive reassembly across the weak/strict threshold split. -/
theorem sum_typeISmallDecadeScales_add_sum_typeILargeDecadeScales
    {M : Type*} [AddCommMonoid M]
    (saving : Real) (length : Nat) (Q : Real) (f : Real → M) :
    (∑ R ∈ typeISmallDecadeScales saving length Q, f R) +
        ∑ R ∈ typeILargeDecadeScales saving length Q, f R =
      ∑ R ∈ typeIDecadeScalesBelow Q, f R := by
  classical
  simpa only [typeISmallDecadeScales, typeILargeDecadeScales, not_le] using
    (typeIDecadeScalesBelow Q).sum_filter_add_sum_filter_not
      (fun R => R ≤
        Real.log (((10 ^ length : Nat) : Real)) ^ (4 * saving + 8)) f

/-- The corresponding reassembly for the equality fibers. -/
theorem sum_typeIDecadeFiber_small_add_large
    (saving : Real) (length : Nat) (Q : Real) (w : Nat → Real) :
    (∑ R ∈ typeISmallDecadeScales saving length Q,
        ∑ q ∈ typeIDecadeFiber Q R, w q) +
        ∑ R ∈ typeILargeDecadeScales saving length Q,
          ∑ q ∈ typeIDecadeFiber Q R, w q =
      ∑ q ∈ typeIReducedDenominatorsBelow Q, w q := by
  rw [sum_typeISmallDecadeScales_add_sum_typeILargeDecadeScales]
  exact sum_typeIDecadeFiber Q w

end

end PrimesRestrictedDigits
