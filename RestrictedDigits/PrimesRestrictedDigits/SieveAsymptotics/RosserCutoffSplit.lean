import PrimesRestrictedDigits.SieveAsymptotics.RosserPartialRecurrence

/-!
# Exact cutoff shells in the finite Rosser recurrences

This splits the unrestricted recurrences at a distant lower cutoff while preserving the
weak-lower/strict-upper shell used in Iwaniec's Eq. (8.8).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem filter_lt_eq_union_cutoffShell
    (P : Finset Nat) {w z : Real} (hwz : w <= z) :
    P.filter (fun p : Nat => (p : Real) < z) =
      P.filter (fun p : Nat => (p : Real) < w) ∪
        P.filter (fun p : Nat => w <= (p : Real) ∧ (p : Real) < z) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hpP, hpz⟩
    by_cases hpw : (p : Real) < w
    · exact Or.inl ⟨hpP, hpw⟩
    · exact Or.inr ⟨hpP, le_of_not_gt hpw, hpz⟩
  · rintro (⟨hpP, hpw⟩ | ⟨hpP, _hpw, hpz⟩)
    · exact ⟨hpP, hpw.trans_le hwz⟩
    · exact ⟨hpP, hpz⟩

private theorem filter_lt_disjoint_cutoffShell
    (P : Finset Nat) (w z : Real) :
    Disjoint
      (P.filter (fun p : Nat => (p : Real) < w))
      (P.filter (fun p : Nat => w <= (p : Real) ∧ (p : Real) < z)) := by
  rw [Finset.disjoint_left]
  intro p hpLeft hpShell
  simp only [Finset.mem_filter] at hpLeft hpShell
  exact (not_lt_of_ge hpShell.2.1) hpLeft.2

/-- The lower partial recurrence split at the exact shell `[w,z)`. The target
rank is `R+1`, and every shell term contains the upper partial sum through
rank `R`. -/
theorem lowerRosserFailurePartialSum_succ_eq_cutoff_add_sum_upper
    (P : Finset Nat) (nu : Nat -> Real) (level w z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hwz : w <= z) :
    lowerRosserFailurePartialSum P nu level z (R + 1) =
      lowerRosserFailurePartialSum P nu level w (R + 1) +
        ∑ p ∈ P.filter (fun p : Nat =>
          w <= (p : Real) ∧ (p : Real) < z),
          nu p * upperRosserFailurePartialSum P nu (level / p) p R := by
  rw [lowerRosserFailurePartialSum_succ_eq_sum_upper_unrestricted
      P nu level z R hprime,
    lowerRosserFailurePartialSum_succ_eq_sum_upper_unrestricted
      P nu level w R hprime,
    filter_lt_eq_union_cutoffShell P hwz,
    Finset.sum_union (filter_lt_disjoint_cutoffShell P w z)]

/-- The upper partial recurrence split at the exact shell `[w,z)`. The cubic
gate at `z` and nonnegativity of `w` supply the corresponding gate at the
lower cutoff. -/
theorem upperRosserFailurePartialSum_eq_cutoff_add_sum_lower_of_cube_le
    (P : Finset Nat) (nu : Nat -> Real) (level w z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hw0 : 0 <= w) (hwz : w <= z)
    (hcube : z ^ 3 <= level) :
    upperRosserFailurePartialSum P nu level z R =
      upperRosserFailurePartialSum P nu level w R +
        ∑ p ∈ P.filter (fun p : Nat =>
          w <= (p : Real) ∧ (p : Real) < z),
          nu p * lowerRosserFailurePartialSum P nu (level / p) p R := by
  have hwCube : w ^ 3 <= level :=
    (pow_le_pow_left₀ hw0 hwz 3).trans hcube
  rw [upperRosserFailurePartialSum_eq_sum_lower_of_cube_le
      P nu level z R hprime hcube,
    upperRosserFailurePartialSum_eq_sum_lower_of_cube_le
      P nu level w R hprime hwCube,
    filter_lt_eq_union_cutoffShell P hwz,
    Finset.sum_union (filter_lt_disjoint_cutoffShell P w z)]

end PrimesRestrictedDigits
