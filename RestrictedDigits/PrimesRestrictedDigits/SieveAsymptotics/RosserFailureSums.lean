import PrimesRestrictedDigits.SieveAsymptotics.IwaniecDensity
import PrimesRestrictedDigits.SieveDecomposition.RosserWeightSupport
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Finset.Sort

/-!
# Finite Rosser first-failure sums

This is the beta-two finite tuple statement behind Iwaniec's equations (4.1)--(4.2). Passing
gates are strict and the first failed gate is weak.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- A nonempty tuple whose proper checked prefixes pass and whose terminal
checked prefix is the first failure. -/
def IsFirstRosserFailure (checked : Nat → Prop)
    (level : Real) (xs : List Nat) : Prop :=
  xs ≠ [] ∧
    IsParityAdmissible checked (RosserBoundary level) xs.dropLast ∧
    checked xs.length ∧ ¬RosserBoundary level xs

/-- An upper first failure has odd length `2 * r + 1`. -/
def IsUpperRosserFailure (level : Real) (r : Nat)
    (xs : List Nat) : Prop :=
  xs.length = 2 * r + 1 ∧
    IsParityAdmissible UpperRosserRank
      (RosserBoundary level) xs.dropLast ∧
    ¬RosserBoundary level xs

/-- A lower first failure has positive even length `2 * r`. -/
def IsLowerRosserFailure (level : Real) (r : Nat)
    (xs : List Nat) : Prop :=
  0 < r ∧ xs.length = 2 * r ∧
    IsParityAdmissible LowerRosserRank
      (RosserBoundary level) xs.dropLast ∧
    ¬RosserBoundary level xs

private theorem admissible_of_append_singleton_admissible
    {alpha : Type*} (checked : Nat → Prop)
    (condition : List alpha → Prop) (xs : List alpha) (x : alpha)
    (h : IsParityAdmissible checked condition (xs ++ [x])) :
    IsParityAdmissible checked condition xs := by
  intro ys hys hchecked
  apply h ys
  · rw [List.mem_inits] at hys ⊢
    exact hys.trans (by simp)
  · exact hchecked

theorem isParityAdmissible_append_singleton_iff {alpha : Type*}
    (checked : Nat → Prop) (condition : List alpha → Prop)
    (xs : List alpha) (x : alpha) :
    IsParityAdmissible checked condition (xs ++ [x]) ↔
      IsParityAdmissible checked condition xs ∧
        (checked (xs.length + 1) → condition (xs ++ [x])) := by
  constructor
  · intro h
    constructor
    · exact admissible_of_append_singleton_admissible
        checked condition xs x h
    · intro hchecked
      exact h (xs ++ [x]) (by simp) (by simpa using hchecked)
  · rintro ⟨hxs, hlast⟩ ys hys hchecked
    have hcases : ys ∈ xs.inits ∨ ys = xs ++ [x] := by
      simpa [List.inits_append] using hys
    rcases hcases with hprefix | rfl
    · exact hxs ys hprefix hchecked
    · exact hlast (by simpa using hchecked)

theorem isFirstRosserFailure_append_singleton_iff
    (checked : Nat → Prop) (level : Real) (xs : List Nat) (p : Nat) :
    IsFirstRosserFailure checked level (xs ++ [p]) ↔
      IsParityAdmissible checked (RosserBoundary level) xs ∧
        ¬IsParityAdmissible checked (RosserBoundary level) (xs ++ [p]) := by
  rw [isParityAdmissible_append_singleton_iff]
  constructor
  · rintro ⟨hne, hadmissibleTail, hchecked, hfailure⟩
    have hadmissible : IsParityAdmissible checked
        (RosserBoundary level) xs := by
      simpa using hadmissibleTail
    have hchecked' : checked (xs.length + 1) := by
      simpa using hchecked
    refine ⟨hadmissible, ?_⟩
    rintro ⟨hprefix, hlast⟩
    exact hfailure (hlast hchecked')
  · rintro ⟨hadmissible, hnot⟩
    have hchecked : checked (xs.length + 1) := by
      by_contra hchecked
      exact hnot ⟨hadmissible, fun h ↦ (hchecked h).elim⟩
    have hfailure : ¬RosserBoundary level (xs ++ [p]) := by
      intro hboundary
      exact hnot ⟨hadmissible, fun _ ↦ hboundary⟩
    refine ⟨by simp, ?_, by simpa using hchecked, hfailure⟩
    simpa using hadmissible

theorem isUpperRosserFailure_iff_first (level : Real) (r : Nat)
    (xs : List Nat) :
    IsUpperRosserFailure level r xs ↔
      xs.length = 2 * r + 1 ∧
        IsFirstRosserFailure UpperRosserRank level xs := by
  constructor
  · rintro ⟨hlen, hadmissible, hfailure⟩
    refine ⟨hlen, ?_⟩
    refine ⟨by simp [List.ne_nil_iff_length_pos, hlen],
      hadmissible, ?_, hfailure⟩
    simp [UpperRosserRank, hlen, Odd]
  · rintro ⟨hlen, hfirst⟩
    exact ⟨hlen, hfirst.2.1, hfirst.2.2.2⟩

theorem isLowerRosserFailure_iff_first (level : Real) (r : Nat)
    (xs : List Nat) :
    IsLowerRosserFailure level r xs ↔
      0 < r ∧ xs.length = 2 * r ∧
        IsFirstRosserFailure LowerRosserRank level xs := by
  constructor
  · rintro ⟨hr, hlen, hadmissible, hfailure⟩
    refine ⟨hr, hlen, ?_⟩
    refine ⟨by simp [List.ne_nil_iff_length_pos, hlen, hr],
      hadmissible, ?_, hfailure⟩
    exact ⟨by omega, ⟨r, by omega⟩⟩
  · rintro ⟨hr, hlen, hfirst⟩
    exact ⟨hr, hlen, hfirst.2.1, hfirst.2.2.2⟩

theorem upperRosserFailure_cubic {level : Real} {r : Nat}
    {xs : List Nat} (h : IsUpperRosserFailure level r xs) :
    level ≤ ((xs.dropLast.prod * xs.getLastD 1 ^ 3 : Nat) : Real) := by
  have hne : xs ≠ [] := by
    simp [List.ne_nil_iff_length_pos, h.1]
  apply le_of_not_gt
  intro hcubic
  exact h.2.2 ((rosserBoundary_iff_dropLast_cube hne).mpr hcubic)

theorem lowerRosserFailure_cubic {level : Real} {r : Nat}
    {xs : List Nat} (h : IsLowerRosserFailure level r xs) :
    level ≤ ((xs.dropLast.prod * xs.getLastD 1 ^ 3 : Nat) : Real) := by
  have hne : xs ≠ [] := by
    simp [List.ne_nil_iff_length_pos, h.1, h.2.1]
  apply le_of_not_gt
  intro hcubic
  exact h.2.2.2 ((rosserBoundary_iff_dropLast_cube hne).mpr hcubic)

@[simp] theorem isUpperRosserFailure_zero_singleton
    (level : Real) (p : Nat) :
    IsUpperRosserFailure level 0 [p] ↔ level ≤ (p : Real) ^ 3 := by
  simp [IsUpperRosserFailure, IsParityAdmissible, UpperRosserRank,
    RosserBoundary]
  constructor <;> intro h <;> nlinarith

/-- Ambient factors below `z`, in the source's strict decreasing order. -/
noncomputable def sieveFactorsBelow
    (P : Finset Nat) (z : Real) : List Nat :=
  (P.filter (fun p : Nat ↦ (p : Real) < z)).sort (fun a b ↦ a ≥ b)

theorem sieveFactorsBelow_sortedGT (P : Finset Nat) (z : Real) :
    (sieveFactorsBelow P z).SortedGT := by
  exact Finset.sortedGT_sort _

theorem mem_sieveFactorsBelow {P : Finset Nat} {z : Real} {p : Nat} :
    p ∈ sieveFactorsBelow P z ↔ p ∈ P ∧ (p : Real) < z := by
  simp [sieveFactorsBelow]

theorem sourceTuple_of_sublist_sieveFactorsBelow
    {P : Finset Nat} {z : Real} {xs : List Nat}
    (hxs : List.Sublist xs (sieveFactorsBelow P z)) :
    xs.SortedGT ∧ ∀ p ∈ xs, p ∈ P ∧ (p : Real) < z := by
  constructor
  · exact ((sieveFactorsBelow_sortedGT P z).pairwise.sublist hxs).sortedGT
  · intro p hp
    exact mem_sieveFactorsBelow.mp (hxs.subset hp)

/-- The unsigned local correction attached to a first-failure tuple. -/
noncomputable def rosserFailureMass
    (P : Finset Nat) (nu : Nat → Real) (xs : List Nat) : Real :=
  (xs.map nu).prod * sieveDensityBelow P nu (xs.getLastD 1)

/-- The upper correction at the source rank `r`. -/
noncomputable def upperRosserFailureSumAtRank
    (P : Finset Nat) (nu : Nat → Real) (level z : Real)
    (r : Nat) : Real := by
  classical
  exact (((sieveFactorsBelow P z).sublists.filter
      (fun xs ↦ decide (IsUpperRosserFailure level r xs))).map fun xs ↦
        rosserFailureMass P nu xs).sum

/-- The lower correction at the source rank `r`. -/
noncomputable def lowerRosserFailureSumAtRank
    (P : Finset Nat) (nu : Nat → Real) (level z : Real)
    (r : Nat) : Real := by
  classical
  exact (((sieveFactorsBelow P z).sublists.filter
      (fun xs ↦ decide (IsLowerRosserFailure level r xs))).map fun xs ↦
        rosserFailureMass P nu xs).sum

/-- The exact finite replacement for the upper sum over `r ≥ 0`. -/
noncomputable def upperRosserFailureSum
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) : Real :=
  ∑ r ∈ Finset.range (((sieveFactorsBelow P z).length + 1) / 2),
    upperRosserFailureSumAtRank P nu level z r

/-- The exact finite replacement for the lower sum over `r ≥ 1`. -/
noncomputable def lowerRosserFailureSum
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) : Real :=
  ∑ r ∈ Finset.Icc 1 ((sieveFactorsBelow P z).length / 2),
    lowerRosserFailureSumAtRank P nu level z r

/-- The unsigned sum over all first failures for one selected parity. -/
noncomputable def rosserFirstFailureSum (checked : Nat → Prop)
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) : Real := by
  classical
  exact ∑ xs ∈ (sieveFactorsBelow P z).sublists.toFinset,
    if IsFirstRosserFailure checked level xs then
      rosserFailureMass P nu xs
    else 0

@[simp] theorem lowerRosserFailureSumAtRank_zero
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) :
    lowerRosserFailureSumAtRank P nu level z 0 = 0 := by
  simp [lowerRosserFailureSumAtRank, IsLowerRosserFailure]

theorem upperRosserFailureSumAtRank_eq_zero_of_length_lt
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat)
    (h : (sieveFactorsBelow P z).length < 2 * r + 1) :
    upperRosserFailureSumAtRank P nu level z r = 0 := by
  classical
  rw [upperRosserFailureSumAtRank]
  have hfilter :
      (sieveFactorsBelow P z).sublists.filter
        (fun xs ↦ decide (IsUpperRosserFailure level r xs)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro xs hxs
    simp only [decide_eq_true_eq]
    intro hfailure
    have hlen := (List.mem_sublists.mp hxs).length_le
    rw [hfailure.1] at hlen
    omega
  rw [hfilter]
  simp

theorem lowerRosserFailureSumAtRank_eq_zero_of_length_lt
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat)
    (h : (sieveFactorsBelow P z).length < 2 * r) :
    lowerRosserFailureSumAtRank P nu level z r = 0 := by
  classical
  rw [lowerRosserFailureSumAtRank]
  have hfilter :
      (sieveFactorsBelow P z).sublists.filter
        (fun xs ↦ decide (IsLowerRosserFailure level r xs)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro xs hxs
    simp only [decide_eq_true_eq]
    intro hfailure
    have hlen := (List.mem_sublists.mp hxs).length_le
    rw [hfailure.2.1] at hlen
    omega
  rw [hfilter]
  simp

private noncomputable def upperFailureValue
    (P : Finset Nat) (nu : Nat → Real) (level : Real)
    (r : Nat) (xs : List Nat) : Real := by
  classical
  exact if IsUpperRosserFailure level r xs then rosserFailureMass P nu xs else 0

private noncomputable def lowerFailureValue
    (P : Finset Nat) (nu : Nat → Real) (level : Real)
    (r : Nat) (xs : List Nat) : Real := by
  classical
  exact if IsLowerRosserFailure level r xs then rosserFailureMass P nu xs else 0

private theorem sum_map_filter_eq_sum_map_ite {alpha : Type*}
    (p : alpha → Bool) (f : alpha → Real) (l : List alpha) :
    ((l.filter p).map f).sum =
      (l.map fun x ↦ if p x then f x else 0).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : p x <;> simp [hx, ih]

private theorem upperSumAtRank_eq_sum_value
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat) :
    upperRosserFailureSumAtRank P nu level z r =
      ∑ xs ∈ (sieveFactorsBelow P z).sublists.toFinset,
        upperFailureValue P nu level r xs := by
  classical
  rw [upperRosserFailureSumAtRank, sum_map_filter_eq_sum_map_ite]
  rw [← List.sum_toFinset _ (sieveFactorsBelow_sortedGT P z).nodup.sublists]
  apply Finset.sum_congr rfl
  intro xs hxs
  simp [upperFailureValue]

private theorem lowerSumAtRank_eq_sum_value
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat) :
    lowerRosserFailureSumAtRank P nu level z r =
      ∑ xs ∈ (sieveFactorsBelow P z).sublists.toFinset,
        lowerFailureValue P nu level r xs := by
  classical
  rw [lowerRosserFailureSumAtRank, sum_map_filter_eq_sum_map_ite]
  rw [← List.sum_toFinset _ (sieveFactorsBelow_sortedGT P z).nodup.sublists]
  apply Finset.sum_congr rfl
  intro xs hxs
  simp [lowerFailureValue]

theorem upperRosserFailureSum_eq_firstFailureSum
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) :
    upperRosserFailureSum P nu level z =
      rosserFirstFailureSum UpperRosserRank P nu level z := by
  classical
  rw [upperRosserFailureSum, rosserFirstFailureSum]
  simp_rw [upperSumAtRank_eq_sum_value]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xs hxs
  by_cases hfirst : IsFirstRosserFailure UpperRosserRank level xs
  · obtain ⟨r, hr⟩ := hfirst.2.2.1
    have hlen : xs.length = 2 * r + 1 := by omega
    have hsub : List.Sublist xs (sieveFactorsBelow P z) :=
      List.mem_sublists.mp (List.mem_toFinset.mp hxs)
    have hrange : r ∈ Finset.range
        (((sieveFactorsBelow P z).length + 1) / 2) := by
      rw [Finset.mem_range]
      have hle := hsub.length_le
      omega
    have hfailure : IsUpperRosserFailure level r xs :=
      (isUpperRosserFailure_iff_first level r xs).mpr ⟨hlen, hfirst⟩
    calc
      (∑ r' ∈ Finset.range (((sieveFactorsBelow P z).length + 1) / 2),
          upperFailureValue P nu level r' xs) =
          upperFailureValue P nu level r xs := by
        apply Finset.sum_eq_single r
        · intro r' hrange' hne
          rw [upperFailureValue, if_neg]
          intro hfailure'
          apply hne
          have hlen' := hfailure'.1
          omega
        · intro hrnot
          exact (hrnot hrange).elim
      _ = _ := by
        rw [upperFailureValue, if_pos hfailure, if_pos hfirst]
  · rw [if_neg hfirst]
    apply Finset.sum_eq_zero
    intro r hr
    rw [upperFailureValue, if_neg]
    exact fun hfailure ↦ hfirst
      ((isUpperRosserFailure_iff_first level r xs).mp hfailure).2

theorem lowerRosserFailureSum_eq_firstFailureSum
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) :
    lowerRosserFailureSum P nu level z =
      rosserFirstFailureSum LowerRosserRank P nu level z := by
  classical
  rw [lowerRosserFailureSum, rosserFirstFailureSum]
  simp_rw [lowerSumAtRank_eq_sum_value]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xs hxs
  by_cases hfirst : IsFirstRosserFailure LowerRosserRank level xs
  · rcases hfirst.2.2.1 with ⟨hlenPos, r, hlenEven⟩
    have hr : 0 < r := by omega
    have hlen : xs.length = 2 * r := by omega
    have hsub : List.Sublist xs (sieveFactorsBelow P z) :=
      List.mem_sublists.mp (List.mem_toFinset.mp hxs)
    have hrange : r ∈ Finset.Icc 1 ((sieveFactorsBelow P z).length / 2) := by
      rw [Finset.mem_Icc]
      have hle := hsub.length_le
      omega
    have hfailure : IsLowerRosserFailure level r xs :=
      (isLowerRosserFailure_iff_first level r xs).mpr
        ⟨hr, hlen, hfirst⟩
    calc
      (∑ r' ∈ Finset.Icc 1 ((sieveFactorsBelow P z).length / 2),
          lowerFailureValue P nu level r' xs) =
          lowerFailureValue P nu level r xs := by
        apply Finset.sum_eq_single r
        · intro r' hrange' hne
          rw [lowerFailureValue, if_neg]
          intro hfailure'
          apply hne
          have hlen' := hfailure'.2.1
          omega
        · intro hrnot
          exact (hrnot hrange).elim
      _ = _ := by
        rw [lowerFailureValue, if_pos hfailure, if_pos hfirst]
  · rw [if_neg hfirst]
    apply Finset.sum_eq_zero
    intro r hr
    rw [lowerFailureValue, if_neg]
    exact fun hfailure ↦ hfirst
      ((isLowerRosserFailure_iff_first level r xs).mp hfailure).2.2

theorem upperRosserFailureSumAtRank_zero_eq_cubic_sum
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) :
    upperRosserFailureSumAtRank P nu level z 0 =
      ∑ p ∈ P.filter (fun p : Nat ↦
        (p : Real) < z ∧ level ≤ (p : Real) ^ 3),
        nu p * sieveDensityBelow P nu p := by
  classical
  rw [upperSumAtRank_eq_sum_value]
  simp_rw [upperFailureValue]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun xs _ ↦ xs.getLastD 1)
  · intro xs hxs
    have hfailure := (Finset.mem_filter.mp hxs).2
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hfailure.1)
    have hsub : List.Sublist [p] (sieveFactorsBelow P z) :=
      List.mem_sublists.mp
        (List.mem_toFinset.mp (Finset.mem_filter.mp hxs).1)
    have hpData := (sourceTuple_of_sublist_sieveFactorsBelow hsub).2 p (by simp)
    rw [Finset.mem_filter]
    simpa only [List.getLastD_cons, List.getLastD_nil] using
      ⟨hpData.1, hpData.2,
        (isUpperRosserFailure_zero_singleton level p).mp hfailure⟩
  · intro xs hxs ys hys heq
    have hxfailure := (Finset.mem_filter.mp hxs).2
    have hyfailure := (Finset.mem_filter.mp hys).2
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hxfailure.1)
    obtain ⟨q, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hyfailure.1)
    simp only [List.getLastD_cons, List.getLastD_nil] at heq
    rw [heq]
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpAmbient : p ∈ sieveFactorsBelow P z :=
      mem_sieveFactorsBelow.mpr ⟨hpData.1, hpData.2.1⟩
    refine ⟨[p], Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact List.mem_toFinset.mpr
        (List.mem_sublists.mpr (List.singleton_sublist.mpr hpAmbient))
    · exact (isUpperRosserFailure_zero_singleton level p).mpr hpData.2.2
    · simp
  · intro xs hxs
    have hfailure := (Finset.mem_filter.mp hxs).2
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hfailure.1)
    simp [rosserFailureMass]

end PrimesRestrictedDigits
