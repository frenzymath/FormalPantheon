import PrimesRestrictedDigits.SieveAsymptotics.RosserRecurrencePredicates
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Rank recurrences for finite Rosser failure sums

Deleting the largest prime gives exact finite recurrences between lower and upper
first-failure sums. The cutoff in each inner sum is the deleted prime, and the level is
divided by that prime.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private noncomputable def upperRankCarrier
    (P : Finset Nat) (level z : Real) (r : Nat) : Finset (List Nat) := by
  classical
  exact ((sieveFactorsBelow P z).sublists.filter
    (fun xs ↦ decide (IsUpperRosserFailure level r xs))).toFinset

private noncomputable def lowerRankCarrier
    (P : Finset Nat) (level z : Real) (r : Nat) : Finset (List Nat) := by
  classical
  exact ((sieveFactorsBelow P z).sublists.filter
    (fun xs ↦ decide (IsLowerRosserFailure level r xs))).toFinset

private theorem mem_upperRankCarrier
    {P : Finset Nat} {level z : Real} {r : Nat} {xs : List Nat} :
    xs ∈ upperRankCarrier P level z r ↔
      List.Sublist xs (sieveFactorsBelow P z) ∧
        IsUpperRosserFailure level r xs := by
  classical
  simp [upperRankCarrier]

private theorem mem_lowerRankCarrier
    {P : Finset Nat} {level z : Real} {r : Nat} {xs : List Nat} :
    xs ∈ lowerRankCarrier P level z r ↔
      List.Sublist xs (sieveFactorsBelow P z) ∧
        IsLowerRosserFailure level r xs := by
  classical
  simp [lowerRankCarrier]

private theorem upperSumAtRank_eq_sum_carrier
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat) :
    upperRosserFailureSumAtRank P nu level z r =
      ∑ xs ∈ upperRankCarrier P level z r,
        rosserFailureMass P nu xs := by
  classical
  rw [upperRosserFailureSumAtRank, upperRankCarrier]
  exact (List.sum_toFinset (rosserFailureMass P nu)
    ((sieveFactorsBelow_sortedGT P z).nodup.sublists.filter _)).symm

private theorem lowerSumAtRank_eq_sum_carrier
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat) :
    lowerRosserFailureSumAtRank P nu level z r =
      ∑ xs ∈ lowerRankCarrier P level z r,
        rosserFailureMass P nu xs := by
  classical
  rw [lowerRosserFailureSumAtRank, lowerRankCarrier]
  exact (List.sum_toFinset (rosserFailureMass P nu)
    ((sieveFactorsBelow_sortedGT P z).nodup.sublists.filter _)).symm

private theorem upperFailure_ne_nil {level : Real} {r : Nat}
    {xs : List Nat} (h : IsUpperRosserFailure level r xs) : xs ≠ [] := by
  apply List.ne_nil_iff_length_pos.mpr
  rw [h.1]
  omega

private theorem lowerFailure_ne_nil {level : Real} {r : Nat}
    {xs : List Nat} (h : IsLowerRosserFailure level r xs) : xs ≠ [] := by
  have hr := h.1
  apply List.ne_nil_iff_length_pos.mpr
  rw [h.2.1]
  omega

/-- Removing the largest prime from a lower failure of rank `r + 1` gives
an upper failure of rank `r` at the divided level and strict head cutoff. -/
theorem lowerRosserFailureSumAtRank_succ_eq_sum_upper
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat)
    (hprime : ∀ p ∈ P, p.Prime) :
    lowerRosserFailureSumAtRank P nu level z (r + 1) =
      ∑ p ∈ P.filter (fun p : Nat ↦ (p : Real) < z),
        nu p * upperRosserFailureSumAtRank P nu (level / p) p r := by
  classical
  rw [lowerSumAtRank_eq_sum_carrier]
  simp_rw [upperSumAtRank_eq_sum_carrier, Finset.mul_sum]
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun xs _ ↦
    (⟨xs.headD 0, xs.tail⟩ : Σ _ : Nat, List Nat))
  · intro xs hxs
    have hx := mem_lowerRankCarrier.mp hxs
    have hxne := lowerFailure_ne_nil hx.2
    obtain ⟨p, tail, rfl⟩ := List.exists_cons_of_ne_nil hxne
    have hpData := sourceTuple_cons_iff.mp hx.1
    have hpPrime := hprime p hpData.1
    have hpReal : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr ⟨hpData.1, hpData.2.1⟩, ?_⟩
    exact mem_upperRankCarrier.mpr ⟨hpData.2.2,
      (isLowerRosserFailure_cons_iff hpReal r tail).mp hx.2⟩
  · intro xs hxs ys hys hxy
    have hx := (mem_lowerRankCarrier.mp hxs).2
    have hy := (mem_lowerRankCarrier.mp hys).2
    obtain ⟨p, xtail, rfl⟩ :=
      List.exists_cons_of_ne_nil (lowerFailure_ne_nil hx)
    obtain ⟨q, ytail, rfl⟩ :=
      List.exists_cons_of_ne_nil (lowerFailure_ne_nil hy)
    exact congrArg (fun a : Σ _ : Nat, List Nat ↦ a.1 :: a.2) hxy
  · rintro ⟨p, tail⟩ hpair
    have hpair' := Finset.mem_sigma.mp hpair
    have hpData := Finset.mem_filter.mp hpair'.1
    have htail := mem_upperRankCarrier.mp hpair'.2
    have hpPrime := hprime p hpData.1
    have hpReal : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    refine ⟨p :: tail, mem_lowerRankCarrier.mpr ⟨?_, ?_⟩, rfl⟩
    · exact sourceTuple_cons_iff.mpr
        ⟨hpData.1, hpData.2, htail.1⟩
    · exact (isLowerRosserFailure_cons_iff hpReal r tail).mpr htail.2
  · intro xs hxs
    have hx := (mem_lowerRankCarrier.mp hxs).2
    have hxne := lowerFailure_ne_nil hx
    obtain ⟨p, tail, rfl⟩ := List.exists_cons_of_ne_nil hxne
    have hpData := (sourceTuple_cons_iff.mp
      (mem_lowerRankCarrier.mp hxs).1).1
    have hpPrime := hprime p hpData
    have hpReal : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have htail := (isLowerRosserFailure_cons_iff hpReal r tail).mp hx
    exact rosserFailureMass_cons P nu p (upperFailure_ne_nil htail)

/-- Removing the largest prime from a positive-rank upper failure gives a
lower failure at the divided level. The separate singleton boundary is part
of the outer carrier. -/
theorem upperRosserFailureSumAtRank_succ_eq_sum_lower
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat)
    (hprime : ∀ p ∈ P, p.Prime) :
    upperRosserFailureSumAtRank P nu level z (r + 1) =
      ∑ p ∈ P.filter (fun p : Nat ↦
        (p : Real) < z ∧ (p : Real) * (p : Real) ^ 2 < level),
        nu p * lowerRosserFailureSumAtRank P nu (level / p) p (r + 1) := by
  classical
  rw [upperSumAtRank_eq_sum_carrier]
  simp_rw [lowerSumAtRank_eq_sum_carrier, Finset.mul_sum]
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun xs _ ↦
    (⟨xs.headD 0, xs.tail⟩ : Σ _ : Nat, List Nat))
  · intro xs hxs
    have hx := mem_upperRankCarrier.mp hxs
    have hxne := upperFailure_ne_nil hx.2
    obtain ⟨p, tail, rfl⟩ := List.exists_cons_of_ne_nil hxne
    have hpData := sourceTuple_cons_iff.mp hx.1
    have hpPrime := hprime p hpData.1
    have hpReal : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have hshift := (isUpperRosserFailure_cons_iff hpReal r tail).mp hx.2
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr
      ⟨hpData.1, hpData.2.1, by simpa [RosserBoundary] using hshift.1⟩, ?_⟩
    exact mem_lowerRankCarrier.mpr ⟨hpData.2.2, hshift.2⟩
  · intro xs hxs ys hys hxy
    have hx := (mem_upperRankCarrier.mp hxs).2
    have hy := (mem_upperRankCarrier.mp hys).2
    obtain ⟨p, xtail, rfl⟩ :=
      List.exists_cons_of_ne_nil (upperFailure_ne_nil hx)
    obtain ⟨q, ytail, rfl⟩ :=
      List.exists_cons_of_ne_nil (upperFailure_ne_nil hy)
    exact congrArg (fun a : Σ _ : Nat, List Nat ↦ a.1 :: a.2) hxy
  · rintro ⟨p, tail⟩ hpair
    have hpair' := Finset.mem_sigma.mp hpair
    have hpData := Finset.mem_filter.mp hpair'.1
    have htail := mem_lowerRankCarrier.mp hpair'.2
    have hpPrime := hprime p hpData.1
    have hpReal : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    refine ⟨p :: tail, mem_upperRankCarrier.mpr ⟨?_, ?_⟩, rfl⟩
    · exact sourceTuple_cons_iff.mpr
        ⟨hpData.1, hpData.2.1, htail.1⟩
    · exact (isUpperRosserFailure_cons_iff hpReal r tail).mpr
        ⟨by simpa [RosserBoundary] using hpData.2.2, htail.2⟩
  · intro xs hxs
    have hx := (mem_upperRankCarrier.mp hxs).2
    have hxne := upperFailure_ne_nil hx
    obtain ⟨p, tail, rfl⟩ := List.exists_cons_of_ne_nil hxne
    have hpData := (sourceTuple_cons_iff.mp
      (mem_upperRankCarrier.mp hxs).1).1
    have hpPrime := hprime p hpData
    have hpReal : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have htail := (isUpperRosserFailure_cons_iff hpReal r tail).mp hx
    exact rosserFailureMass_cons P nu p (lowerFailure_ne_nil htail.2)

end PrimesRestrictedDigits
