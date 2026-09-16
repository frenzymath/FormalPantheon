import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Sublists
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Parity pairing for dimension-one Rosser weights

The alternating sublist sums here are the combinatorial core of the upper and lower divisor
inequalities.
-/

namespace PrimesRestrictedDigits

variable {alpha : Type*}

/-- Every prefix whose length satisfies `checked` passes `condition`. -/
def IsParityAdmissible (checked : Nat → Prop)
    (condition : List alpha → Prop) (xs : List alpha) : Prop :=
  ∀ ys, ys ∈ xs.inits → checked ys.length → condition ys

theorem isParityAdmissible_nil (checked : Nat → Prop)
    (condition : List alpha → Prop) (hzero : ¬checked 0) :
    IsParityAdmissible checked condition [] := by
  simp [IsParityAdmissible, hzero]

private theorem isParityAdmissible_concat_iff (checked : Nat → Prop)
    (condition : List alpha → Prop) (xs : List alpha) (x : alpha) :
    IsParityAdmissible checked condition (xs ++ [x]) ↔
      IsParityAdmissible checked condition xs ∧
        (checked (xs.length + 1) → condition (xs ++ [x])) := by
  constructor
  · intro h
    constructor
    · intro ys hys hchecked
      exact h ys (by
        rw [List.mem_inits] at hys ⊢
        exact hys.trans (by simp)) hchecked
    · intro hchecked
      exact h (xs ++ [x]) (by simp) (by simpa using hchecked)
  · rintro ⟨hxs, hlast⟩ ys hys hchecked
    have hcases : ys ∈ xs.inits ∨ ys = xs ++ [x] := by
      simpa [List.inits_append] using hys
    rcases hcases with hprefix | rfl
    · exact hxs ys hprefix hchecked
    · exact hlast (by simpa using hchecked)

/-- The signed contribution of one selected sublist. -/
noncomputable def rosserSignedContribution (checked : Nat → Prop)
    (condition : List alpha → Prop) (xs : List alpha) : Real := by
  classical
  exact if IsParityAdmissible checked condition xs then
    (-1 : Real) ^ xs.length
  else 0

/-- Alternating sum over all sublists of an ordered ambient list. -/
noncomputable def rosserAlternatingSublistSum (checked : Nat → Prop)
    (condition : List alpha → Prop) (ambient : List alpha) : Real :=
  (ambient.sublists.map
    (rosserSignedContribution checked condition)).sum

private noncomputable def rosserFailureContribution (checked : Nat → Prop)
    (condition : List alpha → Prop) (x : alpha) (xs : List alpha) : Real := by
  classical
  exact if IsParityAdmissible checked condition xs ∧
      ¬IsParityAdmissible checked condition (xs ++ [x]) then
    (-1 : Real) ^ xs.length
  else 0

private theorem signedContribution_add_concat_eq (checked : Nat → Prop)
    (condition : List alpha → Prop) (xs : List alpha) (x : alpha) :
    rosserSignedContribution checked condition xs +
        rosserSignedContribution checked condition (xs ++ [x]) =
      rosserFailureContribution checked condition x xs := by
  classical
  rw [rosserSignedContribution, rosserSignedContribution,
    rosserFailureContribution]
  by_cases hxs : IsParityAdmissible checked condition xs
  · by_cases hx : IsParityAdmissible checked condition (xs ++ [x])
    · simp only [hxs, hx, true_and, not_true_eq_false, if_true, if_false]
      rw [List.length_append, List.length_singleton, pow_succ]
      ring
    · simp [hxs, hx]
  · have hconcat : ¬IsParityAdmissible checked condition (xs ++ [x]) := by
      intro h
      exact hxs ((isParityAdmissible_concat_iff checked condition xs x).mp h).1
    simp [hxs, hconcat]

private theorem alternatingSublistSum_concat (checked : Nat → Prop)
    (condition : List alpha → Prop) (ambient : List alpha) (x : alpha) :
    rosserAlternatingSublistSum checked condition (ambient ++ [x]) =
      (ambient.sublists.map
        (rosserFailureContribution checked condition x)).sum := by
  classical
  simp only [rosserAlternatingSublistSum, List.sublists_concat,
    List.map_append, List.sum_append, List.map_map]
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro xs hxs
  exact signedContribution_add_concat_eq checked condition xs x

/-- Upper Rosser weights check odd-length prefixes. -/
def UpperRosserRank (n : Nat) : Prop := Odd n

/-- Lower Rosser weights check positive even-length prefixes. -/
def LowerRosserRank (n : Nat) : Prop := 0 < n ∧ Even n

theorem upperRosserRank_zero : ¬UpperRosserRank 0 := by
  simp [UpperRosserRank]

theorem lowerRosserRank_zero : ¬LowerRosserRank 0 := by
  simp [LowerRosserRank]

theorem lower_singleton_admissible (condition : List alpha → Prop)
    (x : alpha) :
    IsParityAdmissible LowerRosserRank condition [x] := by
  simp [IsParityAdmissible, LowerRosserRank]

private theorem upper_failure_length_even (condition : List alpha → Prop)
    (xs : List alpha) (x : alpha)
    (hxs : IsParityAdmissible UpperRosserRank condition xs)
    (hbad : ¬IsParityAdmissible UpperRosserRank condition (xs ++ [x])) :
    Even xs.length := by
  rw [isParityAdmissible_concat_iff] at hbad
  have hnot : ¬(UpperRosserRank (xs.length + 1) →
      condition (xs ++ [x])) := fun himp => hbad ⟨hxs, himp⟩
  have hrank : UpperRosserRank (xs.length + 1) := by
    by_contra hrank
    exact hnot (fun h => (hrank h).elim)
  rcases hrank with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  omega

private theorem lower_failure_length_odd (condition : List alpha → Prop)
    (xs : List alpha) (x : alpha)
    (hxs : IsParityAdmissible LowerRosserRank condition xs)
    (hbad : ¬IsParityAdmissible LowerRosserRank condition (xs ++ [x])) :
    Odd xs.length := by
  rw [isParityAdmissible_concat_iff] at hbad
  have hnot : ¬(LowerRosserRank (xs.length + 1) →
      condition (xs ++ [x])) := fun himp => hbad ⟨hxs, himp⟩
  have hrank : LowerRosserRank (xs.length + 1) := by
    by_contra hrank
    exact hnot (fun h => (hrank h).elim)
  rcases hrank.2 with ⟨k, hk⟩
  refine ⟨k - 1, ?_⟩
  omega

/-- Odd-prefix Rosser selection has a nonnegative alternating sum. -/
theorem rosserAlternatingSublistSum_upper_nonneg_of_ne_nil
    (condition : List alpha → Prop) {ambient : List alpha}
    (h : ambient ≠ []) :
    0 ≤ rosserAlternatingSublistSum UpperRosserRank condition ambient := by
  classical
  induction ambient using List.reverseRecOn with
  | nil => simp at h
  | append_singleton xs x ih =>
      rw [alternatingSublistSum_concat]
      apply List.sum_nonneg
      intro term hterm
      simp only [List.mem_map] at hterm
      obtain ⟨ys, hys, rfl⟩ := hterm
      rw [rosserFailureContribution]
      split_ifs with hfail
      · have heven :=
          upper_failure_length_even condition ys x hfail.1 hfail.2
        rw [heven.neg_one_pow]
        simp
      · simp

/-- Positive-even-prefix Rosser selection has a nonpositive alternating sum. -/
theorem rosserAlternatingSublistSum_lower_nonpos_of_ne_nil
    (condition : List alpha → Prop) {ambient : List alpha}
    (h : ambient ≠ []) :
    rosserAlternatingSublistSum LowerRosserRank condition ambient ≤ 0 := by
  classical
  induction ambient using List.reverseRecOn with
  | nil => simp at h
  | append_singleton xs x ih =>
      rw [alternatingSublistSum_concat, ← neg_nonneg, List.sum_neg]
      apply List.sum_nonneg
      intro term hterm
      simp only [List.mem_map] at hterm
      obtain ⟨value, hvalue, rfl⟩ := hterm
      obtain ⟨ys, hys, rfl⟩ := hvalue
      change 0 ≤ -rosserFailureContribution LowerRosserRank condition x ys
      unfold rosserFailureContribution
      split_ifs with hfail
      · have hodd :=
          lower_failure_length_odd condition ys x hfail.1 hfail.2
        rw [hodd.neg_one_pow]
        simp
      · simp

end PrimesRestrictedDigits
