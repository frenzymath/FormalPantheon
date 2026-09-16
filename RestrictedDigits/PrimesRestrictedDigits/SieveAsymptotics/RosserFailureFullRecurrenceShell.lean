import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureFullRecurrence

/-!
# Half-open shells for complete finite Rosser recurrences

These finite identities split the full recurrences at `[w,z)`. The upper cubic head gate
is retained until a cube cutoff proves it everywhere.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem filter_lt_eq_union_shell
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
  · rintro (⟨hpP, hpw⟩ | ⟨hpP, hpw, hpz⟩)
    · exact ⟨hpP, hpw.trans_le hwz⟩
    · exact ⟨hpP, hpz⟩

private theorem filter_lt_disjoint_shell
    (P : Finset Nat) (w z : Real) :
    Disjoint
      (P.filter (fun p : Nat => (p : Real) < w))
      (P.filter (fun p : Nat => w <= (p : Real) ∧ (p : Real) < z)) := by
  rw [Finset.disjoint_left]
  intro p hpw hpShell
  exact (not_lt_of_ge (Finset.mem_filter.mp hpShell).2.1)
    (Finset.mem_filter.mp hpw).2

private theorem filter_gate_eq_union_shell
    (P : Finset Nat) {w z level : Real} (hwz : w <= z) :
    P.filter (fun p : Nat =>
        (p : Real) < z ∧ (p : Real) ^ 3 < level) =
      P.filter (fun p : Nat =>
          (p : Real) < w ∧ (p : Real) ^ 3 < level) ∪
        P.filter (fun p : Nat =>
          w <= (p : Real) ∧ (p : Real) < z ∧
            (p : Real) ^ 3 < level) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hpP, hpz, hgate⟩
    by_cases hpw : (p : Real) < w
    · exact Or.inl ⟨hpP, hpw, hgate⟩
    · exact Or.inr ⟨hpP, le_of_not_gt hpw, hpz, hgate⟩
  · rintro (⟨hpP, hpw, hgate⟩ | ⟨hpP, hpw, hpz, hgate⟩)
    · exact ⟨hpP, hpw.trans_le hwz, hgate⟩
    · exact ⟨hpP, hpz, hgate⟩

private theorem filter_gate_disjoint_shell
    (P : Finset Nat) (w z level : Real) :
    Disjoint
      (P.filter (fun p : Nat =>
        (p : Real) < w ∧ (p : Real) ^ 3 < level))
      (P.filter (fun p : Nat =>
        w <= (p : Real) ∧ (p : Real) < z ∧
          (p : Real) ^ 3 < level)) := by
  rw [Finset.disjoint_left]
  intro p hpw hpShell
  exact (not_lt_of_ge (Finset.mem_filter.mp hpShell).2.1)
    (Finset.mem_filter.mp hpw).2.1

/-- The complete lower correction split at the strict half-open shell `[w,z)`. -/
theorem lowerRosserFailureSum_eq_cutoff_add_sum_upper_full
    (P : Finset Nat) (nu : Nat → Real) (level w z : Real)
    (hprime : ∀ p ∈ P, p.Prime) (hwz : w <= z) :
    lowerRosserFailureSum P nu level z =
      lowerRosserFailureSum P nu level w +
        ∑ p ∈ P.filter (fun p : Nat =>
          w <= (p : Real) ∧ (p : Real) < z),
          nu p * upperRosserFailureSum P nu (level / p) p := by
  rw [lowerRosserFailureSum_eq_sum_upper_full P nu level z hprime,
    lowerRosserFailureSum_eq_sum_upper_full P nu level w hprime,
    filter_lt_eq_union_shell P hwz,
    Finset.sum_union (filter_lt_disjoint_shell P w z)]

/-- The complete upper correction split with its exact weak cubic head gate. -/
theorem upperRosserFailureSum_eq_cutoff_add_sum_lower_full_gated
    (P : Finset Nat) (nu : Nat → Real) (level w z : Real)
    (hprime : ∀ p ∈ P, p.Prime) (hwz : w <= z) :
    upperRosserFailureSum P nu level z =
      upperRosserFailureSum P nu level w +
        (upperRosserFailureSumAtRank P nu level z 0 -
          upperRosserFailureSumAtRank P nu level w 0) +
        ∑ p ∈ P.filter (fun p : Nat =>
          w <= (p : Real) ∧ (p : Real) < z ∧
            (p : Real) ^ 3 < level),
          nu p * lowerRosserFailureSum P nu (level / p) p := by
  rw [upperRosserFailureSum_eq_rankZero_add_sum_lower_gated
        P nu level z hprime,
    upperRosserFailureSum_eq_rankZero_add_sum_lower_gated
        P nu level w hprime,
    filter_gate_eq_union_shell P hwz,
    Finset.sum_union (filter_gate_disjoint_shell P w z level)]
  ring

private theorem cube_le_of_nonneg_le
    {w z level : Real} (hw0 : 0 <= w) (hwz : w <= z)
    (hcube : z ^ 3 <= level) : w ^ 3 <= level := by
  exact (pow_le_pow_left₀ hw0 hwz 3).trans hcube

/-- Under a weak cube cutoff, the upper shell is ungated as well. -/
theorem upperRosserFailureSum_eq_cutoff_add_sum_lower_full_of_cube_le
    (P : Finset Nat) (nu : Nat → Real) (level w z : Real)
    (hprime : ∀ p ∈ P, p.Prime) (hw0 : 0 <= w) (hwz : w <= z)
    (hcube : z ^ 3 <= level) :
    upperRosserFailureSum P nu level z =
      upperRosserFailureSum P nu level w +
        (upperRosserFailureSumAtRank P nu level z 0 -
          upperRosserFailureSumAtRank P nu level w 0) +
        ∑ p ∈ P.filter (fun p : Nat =>
          w <= (p : Real) ∧ (p : Real) < z),
          nu p * lowerRosserFailureSum P nu (level / p) p := by
  rw [upperRosserFailureSum_eq_rankZero_add_sum_lower_of_cube_le
        P nu level z hprime hcube,
    upperRosserFailureSum_eq_rankZero_add_sum_lower_of_cube_le
        P nu level w hprime (cube_le_of_nonneg_le hw0 hwz hcube),
    filter_lt_eq_union_shell P hwz,
    Finset.sum_union (filter_lt_disjoint_shell P w z)]
  ring

end PrimesRestrictedDigits
