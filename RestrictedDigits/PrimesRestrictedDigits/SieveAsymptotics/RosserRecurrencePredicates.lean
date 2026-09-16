import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureSums
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Head-tail predicates for the finite Rosser recurrences

This file supplies the tuple-level identities used to derive Iwaniec's finite beta-two
recurrences (4.4)--(4.6). Removing the largest factor divides the level by that factor and
switches the selected parity.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The upper first-failure correction through rank `R`. -/
noncomputable def upperRosserFailurePartialSum
    (P : Finset Nat) (nu : Nat → Real) (level z : Real)
    (R : Nat) : Real :=
  ∑ r ∈ Finset.range (R + 1),
    upperRosserFailureSumAtRank P nu level z r

/-- The lower first-failure correction through rank `R`. -/
noncomputable def lowerRosserFailurePartialSum
    (P : Finset Nat) (nu : Nat → Real) (level z : Real)
    (R : Nat) : Real :=
  ∑ r ∈ Finset.Icc 1 R,
    lowerRosserFailureSumAtRank P nu level z r

@[simp] theorem upperRosserFailurePartialSum_zero
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) :
    upperRosserFailurePartialSum P nu level z 0 =
      upperRosserFailureSumAtRank P nu level z 0 := by
  simp [upperRosserFailurePartialSum]

@[simp] theorem lowerRosserFailurePartialSum_zero
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) :
    lowerRosserFailurePartialSum P nu level z 0 = 0 := by
  simp [lowerRosserFailurePartialSum]

/-- Removing a positive head from a nonempty boundary tuple divides its
level by that head. -/
theorem rosserBoundary_cons_iff {level : Real} {p : Nat}
    {xs : List Nat} (hp : 0 < (p : Real)) (hxs : xs ≠ []) :
    RosserBoundary level (p :: xs) ↔
      RosserBoundary (level / p) xs := by
  obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hxs
  simp only [RosserBoundary, List.prod_cons, List.getLastD_cons,
    Nat.cast_mul]
  rw [lt_div_iff₀ hp]
  ring_nf

private theorem lowerAdmissible_cons_iff_upperAdmissible
    {level : Real} {p : Nat} (hp : 0 < (p : Real))
    (xs : List Nat) :
    IsParityAdmissible LowerRosserRank (RosserBoundary level) (p :: xs) ↔
      IsParityAdmissible UpperRosserRank
        (RosserBoundary (level / p)) xs := by
  constructor
  · intro h ys hys hodd
    have hysne : ys ≠ [] :=
      List.ne_nil_iff_length_pos.mpr (Odd.pos hodd)
    apply (rosserBoundary_cons_iff hp hysne).mp
    apply h (p :: ys)
    · simp [hys]
    · refine ⟨by simp, ?_⟩
      unfold UpperRosserRank at hodd
      rcases hodd with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      simp only [List.length_cons] at hk ⊢
      omega
  · intro h ys hys hlower
    rw [List.inits_cons] at hys
    simp only [List.mem_cons, List.mem_map] at hys
    rcases hys with rfl | ⟨tail, htail, rfl⟩
    · simp [LowerRosserRank] at hlower
    · have htailOdd : UpperRosserRank tail.length := by
        unfold UpperRosserRank
        have heven : Even (tail.length + 1) := by
          simpa only [List.length_cons, Nat.add_comm 1] using hlower.2
        rcases heven with ⟨k, hk⟩
        refine ⟨k - 1, ?_⟩
        omega
      exact (rosserBoundary_cons_iff hp
        (List.ne_nil_iff_length_pos.mpr (Odd.pos htailOdd))).mpr
        (h tail htail htailOdd)

private theorem upperAdmissible_cons_iff_lowerAdmissible
    {level : Real} {p : Nat} (hp : 0 < (p : Real))
    (xs : List Nat) :
    IsParityAdmissible UpperRosserRank (RosserBoundary level) (p :: xs) ↔
      RosserBoundary level [p] ∧
        IsParityAdmissible LowerRosserRank
          (RosserBoundary (level / p)) xs := by
  constructor
  · intro h
    constructor
    · exact h [p] (by simp) (by simp [UpperRosserRank])
    · intro ys hys hlower
      have hysne : ys ≠ [] :=
        List.ne_nil_iff_length_pos.mpr hlower.1
      apply (rosserBoundary_cons_iff hp hysne).mp
      apply h (p :: ys)
      · simp [hys]
      · unfold UpperRosserRank
        rcases hlower.2 with ⟨k, hk⟩
        have hodd : Odd (ys.length + 1) := ⟨k, by omega⟩
        simpa only [List.length_cons] using hodd
  · rintro ⟨hsingle, h⟩ ys hys hupper
    rw [List.inits_cons] at hys
    simp only [List.mem_cons, List.mem_map] at hys
    rcases hys with rfl | ⟨tail, htail, rfl⟩
    · simp [UpperRosserRank] at hupper
    · have htailEven : Even tail.length := by
        unfold UpperRosserRank at hupper
        have hodd : Odd (tail.length + 1) := by
          simpa only [List.length_cons, Nat.add_comm 1] using hupper
        rcases hodd with ⟨k, hk⟩
        exact ⟨k, by omega⟩
      by_cases htailNil : tail = []
      · subst tail
        simpa using hsingle
      · have htailLower : LowerRosserRank tail.length :=
          ⟨List.length_pos_of_ne_nil htailNil, htailEven⟩
        exact (rosserBoundary_cons_iff hp htailNil).mpr
          (h tail htail htailLower)

/-- Deleting the largest factor of a lower failure decreases its rank by one
and produces an upper failure at the divided level. -/
theorem isLowerRosserFailure_cons_iff
    {level : Real} {p : Nat} (hp : 0 < (p : Real))
    (r : Nat) (xs : List Nat) :
    IsLowerRosserFailure level (r + 1) (p :: xs) ↔
      IsUpperRosserFailure (level / p) r xs := by
  constructor
  · rintro ⟨hr, hlen, hadmissible, hfailure⟩
    have hlen' : xs.length = 2 * r + 1 := by
      simp only [List.length_cons] at hlen
      omega
    have hxs : xs ≠ [] :=
      List.ne_nil_iff_length_pos.mpr (by omega)
    have hdrop : (p :: xs).dropLast = p :: xs.dropLast := by
      obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hxs
      simp
    refine ⟨hlen', ?_, ?_⟩
    · apply (lowerAdmissible_cons_iff_upperAdmissible hp _).mp
      rwa [← hdrop]
    · exact fun hboundary => hfailure
        ((rosserBoundary_cons_iff hp hxs).mpr hboundary)
  · rintro ⟨hlen, hadmissible, hfailure⟩
    have hxs : xs ≠ [] :=
      List.ne_nil_iff_length_pos.mpr (by omega)
    have hdrop : (p :: xs).dropLast = p :: xs.dropLast := by
      obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hxs
      simp
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · rw [hdrop]
      exact (lowerAdmissible_cons_iff_upperAdmissible hp _).mpr hadmissible
    · exact fun hboundary => hfailure
        ((rosserBoundary_cons_iff hp hxs).mp hboundary)

/-- Deleting the largest factor of a positive-rank upper failure produces a
lower failure at the divided level. The first upper gate remains separate. -/
theorem isUpperRosserFailure_cons_iff
    {level : Real} {p : Nat} (hp : 0 < (p : Real))
    (r : Nat) (xs : List Nat) :
    IsUpperRosserFailure level (r + 1) (p :: xs) ↔
      RosserBoundary level [p] ∧
        IsLowerRosserFailure (level / p) (r + 1) xs := by
  constructor
  · rintro ⟨hlen, hadmissible, hfailure⟩
    have hlen' : xs.length = 2 * (r + 1) := by
      simp only [List.length_cons] at hlen
      omega
    have hxs : xs ≠ [] :=
      List.ne_nil_iff_length_pos.mpr (by omega)
    have hdrop : (p :: xs).dropLast = p :: xs.dropLast := by
      obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hxs
      simp
    have hadmissible' :=
      (upperAdmissible_cons_iff_lowerAdmissible hp xs.dropLast).mp
        (by rwa [← hdrop])
    refine ⟨hadmissible'.1, by omega, hlen', hadmissible'.2, ?_⟩
    exact fun hboundary => hfailure
      ((rosserBoundary_cons_iff hp hxs).mpr hboundary)
  · rintro ⟨hsingle, hr, hlen, hadmissible, hfailure⟩
    have hxs : xs ≠ [] :=
      List.ne_nil_iff_length_pos.mpr (by omega)
    have hdrop : (p :: xs).dropLast = p :: xs.dropLast := by
      obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hxs
      simp
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · rw [hdrop]
      exact (upperAdmissible_cons_iff_lowerAdmissible hp _).mpr
        ⟨hsingle, hadmissible⟩
    · exact fun hboundary => hfailure
        ((rosserBoundary_cons_iff hp hxs).mp hboundary)

/-- The local first-failure mass factors through any nonempty tail. -/
theorem rosserFailureMass_cons
    (P : Finset Nat) (nu : Nat → Real) (p : Nat)
    {xs : List Nat} (hxs : xs ≠ []) :
    rosserFailureMass P nu (p :: xs) =
      nu p * rosserFailureMass P nu xs := by
  obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hxs
  simp [rosserFailureMass, mul_assoc]

/-- A canonical decreasing source tuple headed by `p` is equivalent to a
source head below `z` and a canonical tail below the strict cutoff `p`. -/
theorem sourceTuple_cons_iff {P : Finset Nat} {z : Real}
    {p : Nat} {xs : List Nat} :
    List.Sublist (p :: xs) (sieveFactorsBelow P z) ↔
      p ∈ P ∧ (p : Real) < z ∧
        List.Sublist xs (sieveFactorsBelow P p) := by
  constructor
  · intro htuple
    have hsource := sourceTuple_of_sublist_sieveFactorsBelow htuple
    have hpData := hsource.2 p (by simp)
    refine ⟨hpData.1, hpData.2, ?_⟩
    have htailSorted : xs.SortedGT := hsource.1.pairwise.tail.sortedGT
    apply List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset htailSorted.nodup ?_)
      htailSorted.pairwise (sieveFactorsBelow_sortedGT P p).pairwise
    intro q hq
    apply mem_sieveFactorsBelow.mpr
    have hqData := hsource.2 q (by simp [hq])
    have hpq : p > q :=
      (List.pairwise_cons.mp hsource.1.pairwise).1 q hq
    exact ⟨hqData.1, by exact_mod_cast hpq⟩
  · rintro ⟨hpP, hpz, htail⟩
    have htailSource := sourceTuple_of_sublist_sieveFactorsBelow htail
    have hconsSorted : (p :: xs).SortedGT := by
      rw [List.sortedGT_iff_pairwise, List.pairwise_cons]
      refine ⟨?_, htailSource.1.pairwise⟩
      intro q hq
      exact_mod_cast (htailSource.2 q hq).2
    apply List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset hconsSorted.nodup ?_)
      hconsSorted.pairwise (sieveFactorsBelow_sortedGT P z).pairwise
    intro q hq
    rw [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact mem_sieveFactorsBelow.mpr ⟨hpP, hpz⟩
    · have hqData := htailSource.2 q hq
      exact mem_sieveFactorsBelow.mpr ⟨hqData.1, hqData.2.trans hpz⟩

/-- The beta-two cutoff suppressed in Iwaniec's printed equation (4.6). -/
noncomputable def iwaniecBaseCutoff (level : Real) : Real :=
  level ^ (1 / 3 : Real)

theorem iwaniecBaseCutoff_nonneg {level : Real} (hlevel : 0 ≤ level) :
    0 ≤ iwaniecBaseCutoff level := by
  exact Real.rpow_nonneg hlevel _

theorem iwaniecBaseCutoff_pow_three {level : Real}
    (hlevel : 0 ≤ level) :
    iwaniecBaseCutoff level ^ (3 : Nat) = level := by
  rw [iwaniecBaseCutoff, show (1 / 3 : Real) = (3 : Real)⁻¹ by norm_num]
  exact Real.rpow_inv_natCast_pow hlevel (by norm_num)

theorem lt_iwaniecBaseCutoff_iff_cube_lt
    {x level : Real} (hx : 0 ≤ x) (hlevel : 0 ≤ level) :
    x < iwaniecBaseCutoff level ↔ x ^ (3 : Nat) < level := by
  rw [iwaniecBaseCutoff, show (1 / 3 : Real) = (3 : Real)⁻¹ by norm_num,
    Real.lt_rpow_inv_iff_of_pos hx hlevel (by norm_num : (0 : Real) < 3)]
  have hpow : x ^ (3 : Real) = x ^ (3 : Nat) :=
    Real.rpow_natCast x 3
  rw [hpow]

theorem lt_iwaniecBaseCutoff_of_cube_lt
    {x level : Real} (hx : 0 ≤ x) (hlevel : 0 ≤ level)
    (hcube : x ^ (3 : Nat) < level) :
    x < iwaniecBaseCutoff level :=
  (lt_iwaniecBaseCutoff_iff_cube_lt hx hlevel).mpr hcube

/-- The head of every positive-rank upper failure lies below the base cutoff. -/
theorem upperRosserFailure_cons_head_lt_baseCutoff
    {level : Real} {r p : Nat} {xs : List Nat}
    (hlevel : 0 ≤ level) (hp : 0 < (p : Real))
    (hfailure : IsUpperRosserFailure level (r + 1) (p :: xs)) :
    (p : Real) < iwaniecBaseCutoff level := by
  have htail : xs ≠ [] := by
    have hlength := hfailure.1
    simp only [List.length_cons] at hlength
    exact List.ne_nil_iff_length_pos.mpr (by omega)
  have hsingle :=
    ((isUpperRosserFailure_cons_iff hp r xs).mp hfailure).1
  apply lt_iwaniecBaseCutoff_of_cube_lt (by positivity) hlevel
  rw [show (p : Real) ^ (3 : Nat) = (p : Real) * (p : Real) ^ 2 by ring]
  simpa [RosserBoundary] using hsingle

end PrimesRestrictedDigits
