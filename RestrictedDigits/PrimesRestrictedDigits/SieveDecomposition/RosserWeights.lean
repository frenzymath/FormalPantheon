import PrimesRestrictedDigits.SieveDecomposition.LowerBoundingSieve
import PrimesRestrictedDigits.SieveDecomposition.RosserParity
import Mathlib.Data.Finset.Sort

/-!
# Canonical dimension-one Rosser weights

The source coefficients are defined intrinsically from each natural number's distinct prime
factors in descending order. The squarefree-divisor/sublist reindex proves the global upper
and lower Moebius inequalities.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace PrimesRestrictedDigits

private theorem sublist_eq_of_toFinset_eq {alpha : Type*}
    [DecidableEq alpha] {ambient xs ys : List alpha}
    (hambient : ambient.Nodup) (hxs : List.Sublist xs ambient)
    (hys : List.Sublist ys ambient) (hset : xs.toFinset = ys.toFinset) :
    xs = ys := by
  have hxnodup := hambient.sublist hxs
  have hynodup := hambient.sublist hys
  have hperm : xs.Perm ys := by
    rw [List.perm_ext_iff_of_nodup hxnodup hynodup]
    intro x
    simpa only [List.mem_toFinset] using Finset.ext_iff.mp hset x
  exact (hambient.perm_iff_eq_of_sublist hxs hys).mp hperm

private theorem sum_powerset_eq_sum_sublists {alpha : Type*}
    [DecidableEq alpha] (ambient : List alpha) (hambient : ambient.Nodup)
    (f : Finset alpha → Real) :
    (∑ s ∈ ambient.toFinset.powerset, f s) =
      (ambient.sublists.map fun xs => f xs.toFinset).sum := by
  classical
  rw [← List.sum_toFinset (fun xs => f xs.toFinset) hambient.sublists]
  symm
  apply Finset.sum_bij (fun xs _ => xs.toFinset)
  · intro xs hxs
    rw [Finset.mem_powerset]
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact (List.mem_sublists.mp (List.mem_toFinset.mp hxs)).subset hx
  · intro xs hxs ys hys hxy
    exact sublist_eq_of_toFinset_eq hambient
      (List.mem_sublists.mp (List.mem_toFinset.mp hxs))
      (List.mem_sublists.mp (List.mem_toFinset.mp hys)) hxy
  · intro s hs
    let xs := ambient.filter (fun x => x ∈ s)
    have hxsSub : List.Sublist xs ambient := List.filter_sublist
    have hxsMem : xs ∈ ambient.sublists := List.mem_sublists.mpr hxsSub
    refine ⟨xs, List.mem_toFinset.mpr hxsMem, ?_⟩
    ext x
    simp only [xs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun hx => hx.2
    · intro hx
      exact ⟨by
        have hsubset := Finset.mem_powerset.mp hs
        rw [← List.mem_toFinset]
        exact hsubset hx, hx⟩
  · intro xs hxs
    rfl

/-- Canonical distinct prime factors in the source's decreasing order. -/
def descendingPrimeFactors (d : Nat) : List Nat :=
  d.primeFactorsList.reverse

/-- Distinct decreasing factors used only to reindex squarefree divisors. -/
private def divisorPrimeFactors (n : Nat) : List Nat :=
  n.primeFactorsList.dedup.reverse

private theorem divisorPrimeFactors_nodup (n : Nat) :
    (divisorPrimeFactors n).Nodup := by
  rw [divisorPrimeFactors, List.nodup_reverse]
  exact List.nodup_dedup _

private theorem divisorPrimeFactors_sortedGE (n : Nat) :
    (divisorPrimeFactors n).SortedGE := by
  rw [divisorPrimeFactors, List.sortedGE_reverse]
  exact ((Nat.primeFactorsList_sorted n).pairwise.sublist
    (List.dedup_sublist _)).sortedLE

private theorem prime_of_mem_divisorPrimeFactors {n p : Nat}
    (hp : p ∈ divisorPrimeFactors n) : p.Prime := by
  apply Nat.prime_of_mem_primeFactorsList
  simpa [divisorPrimeFactors] using hp

private theorem descendingPrimeFactors_prod_of_sublist
    {n : Nat} {xs : List Nat}
    (hxs : List.Sublist xs (divisorPrimeFactors n)) :
    descendingPrimeFactors xs.prod = xs := by
  have hxprime : ∀ p, p ∈ xs → p.Prime := by
    intro p hp
    exact prime_of_mem_divisorPrimeFactors (hxs.subset hp)
  have hxsorted : xs.SortedGE :=
    ((divisorPrimeFactors_sortedGE n).pairwise.sublist hxs).sortedGE
  have hperm : xs.Perm xs.prod.primeFactorsList :=
    Nat.primeFactorsList_unique rfl hxprime
  have heq : xs.prod.primeFactorsList = xs.reverse :=
    List.Perm.eq_reverse_of_sortedLE_of_sortedGE hperm.symm
      (Nat.primeFactorsList_sorted _) hxsorted
  simp [descendingPrimeFactors, heq]

private theorem squarefree_prod_of_sublist
    {n : Nat} {xs : List Nat}
    (hxs : List.Sublist xs (divisorPrimeFactors n)) :
    Squarefree xs.prod := by
  have hxprime : ∀ p, p ∈ xs → p.Prime := by
    intro p hp
    exact prime_of_mem_divisorPrimeFactors (hxs.subset hp)
  have hprod : xs.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hxprime 0 hzero).ne_zero rfl
  rw [Nat.squarefree_iff_nodup_primeFactorsList hprod]
  have hcanonical := descendingPrimeFactors_prod_of_sublist hxs
  simp only [descendingPrimeFactors] at hcanonical
  rw [← List.nodup_reverse, hcanonical]
  exact (divisorPrimeFactors_nodup n).sublist hxs

private theorem moebius_prod_of_sublist
    {n : Nat} {xs : List Nat}
    (hxs : List.Sublist xs (divisorPrimeFactors n)) :
    (ArithmeticFunction.moebius xs.prod : Real) =
      (-1 : Real) ^ xs.length := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree
      (squarefree_prod_of_sublist hxs),
    ArithmeticFunction.cardFactors_apply]
  have hcanonical := descendingPrimeFactors_prod_of_sublist hxs
  simp only [descendingPrimeFactors] at hcanonical
  have hlength : xs.prod.primeFactorsList.length = xs.length := by
    rw [← List.length_reverse, hcanonical]
  rw [hlength]
  norm_cast

/-- The dimension-one boundary on a decreasing nonempty prime prefix. -/
def RosserBoundary (level : Real) (xs : List Nat) : Prop :=
  (xs.prod : Real) * (xs.getLastD 1 : Real) ^ 2 < level

/-- The product-times-square boundary is the source's proper-prefix cubic
boundary on every nonempty list. -/
theorem rosserBoundary_iff_dropLast_cube {level : Real} {xs : List Nat}
    (hxs : xs ≠ []) :
    RosserBoundary level xs ↔
      ((xs.dropLast.prod * xs.getLastD 1 ^ 3 : Nat) : Real) < level := by
  induction xs using List.reverseRecOn with
  | nil => simp at hxs
  | append_singleton ys p ih =>
      simp [RosserBoundary, Nat.cast_mul, Nat.cast_pow]
      ring_nf

/-- Squarefree naturals whose canonical factors pass the selected gates. -/
def IsRosserAdmissible (checked : Nat → Prop) (level : Real)
    (d : Nat) : Prop :=
  Squarefree d ∧ IsParityAdmissible checked (RosserBoundary level)
    (descendingPrimeFactors d)

/-- Canonical real Rosser coefficient for a selected prefix parity. -/
noncomputable def rosserWeight (checked : Nat → Prop) (level : Real)
    (d : Nat) : Real := by
  classical
  exact if IsRosserAdmissible checked level d then
    (ArithmeticFunction.moebius d : Real)
  else 0

/-- Upper dimension-one Rosser coefficient. -/
noncomputable def upperRosserWeight (level : Real) (d : Nat) : Real :=
  rosserWeight UpperRosserRank level d

/-- Lower dimension-one Rosser coefficient. -/
noncomputable def lowerRosserWeight (level : Real) (d : Nat) : Real :=
  rosserWeight LowerRosserRank level d

@[simp] theorem rosserWeight_zero (checked : Nat → Prop) (level : Real) :
    rosserWeight checked level 0 = 0 := by
  simp [rosserWeight, IsRosserAdmissible]

@[simp] theorem rosserWeight_one (checked : Nat → Prop) (level : Real)
    (hzero : ¬checked 0) :
    rosserWeight checked level 1 = 1 := by
  classical
  simp [rosserWeight, IsRosserAdmissible, descendingPrimeFactors,
    IsParityAdmissible, hzero]

theorem rosserWeight_eq_zero_of_not_squarefree
    (checked : Nat → Prop) (level : Real) {d : Nat}
    (hd : ¬Squarefree d) :
    rosserWeight checked level d = 0 := by
  simp [rosserWeight, IsRosserAdmissible, hd]

@[simp] theorem upperRosserWeight_zero (level : Real) :
    upperRosserWeight level 0 = 0 := by
  simp [upperRosserWeight]

@[simp] theorem lowerRosserWeight_zero (level : Real) :
    lowerRosserWeight level 0 = 0 := by
  simp [lowerRosserWeight]

@[simp] theorem upperRosserWeight_one (level : Real) :
    upperRosserWeight level 1 = 1 := by
  simp [upperRosserWeight, UpperRosserRank]

@[simp] theorem lowerRosserWeight_one (level : Real) :
    lowerRosserWeight level 1 = 1 := by
  simp [lowerRosserWeight, LowerRosserRank]

theorem upperRosserWeight_eq_zero_of_not_squarefree
    (level : Real) {d : Nat} (hd : ¬Squarefree d) :
    upperRosserWeight level d = 0 :=
  rosserWeight_eq_zero_of_not_squarefree UpperRosserRank level hd

theorem lowerRosserWeight_eq_zero_of_not_squarefree
    (level : Real) {d : Nat} (hd : ¬Squarefree d) :
    lowerRosserWeight level d = 0 :=
  rosserWeight_eq_zero_of_not_squarefree LowerRosserRank level hd

theorem abs_rosserWeight_le_one (checked : Nat → Prop)
    (level : Real) (d : Nat) :
    |rosserWeight checked level d| ≤ 1 := by
  classical
  rw [rosserWeight]
  split_ifs
  · norm_cast
    exact ArithmeticFunction.abs_moebius_le_one
  · simp

theorem abs_upperRosserWeight_le_one (level : Real) (d : Nat) :
    |upperRosserWeight level d| ≤ 1 :=
  abs_rosserWeight_le_one UpperRosserRank level d

theorem abs_lowerRosserWeight_le_one (level : Real) (d : Nat) :
    |lowerRosserWeight level d| ≤ 1 :=
  abs_rosserWeight_le_one LowerRosserRank level d

private theorem rosserWeight_prod_of_sublist
    (checked : Nat → Prop) (level : Real) {n : Nat} {xs : List Nat}
    (hxs : List.Sublist xs (divisorPrimeFactors n)) :
    rosserWeight checked level xs.prod =
      rosserSignedContribution checked (RosserBoundary level) xs := by
  classical
  have hsquarefree := squarefree_prod_of_sublist hxs
  have hcanonical := descendingPrimeFactors_prod_of_sublist hxs
  have hmoebius := moebius_prod_of_sublist hxs
  rw [rosserWeight, rosserSignedContribution]
  simp only [IsRosserAdmissible, hsquarefree, true_and, hcanonical]
  split_ifs <;> simp_all

private theorem sum_divisors_rosserWeight_eq_alternatingSublistSum
    (checked : Nat → Prop) (level : Real) {n : Nat} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, rosserWeight checked level d) =
      rosserAlternatingSublistSum checked (RosserBoundary level)
        (divisorPrimeFactors n) := by
  classical
  have hfilter :
      (∑ d ∈ n.divisors.filter Squarefree,
        rosserWeight checked level d) =
        ∑ d ∈ n.divisors, rosserWeight checked level d := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    apply rosserWeight_eq_zero_of_not_squarefree
    intro hsquarefree
    exact hnot (Finset.mem_filter.mpr ⟨hd, hsquarefree⟩)
  rw [← hfilter, Nat.sum_divisors_filter_squarefree hn]
  have hfactorSet :
      (divisorPrimeFactors n).toFinset =
        (UniqueFactorizationMonoid.normalizedFactors n).toFinset := by
    rw [Nat.factors_eq]
    ext p
    simp only [divisorPrimeFactors, List.mem_toFinset, List.mem_reverse,
      List.mem_dedup, Multiset.mem_toFinset, Multiset.mem_coe]
  rw [← hfactorSet]
  rw [sum_powerset_eq_sum_sublists
    (divisorPrimeFactors n) (divisorPrimeFactors_nodup n)]
  unfold rosserAlternatingSublistSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro xs hxs
  have hsub : List.Sublist xs (divisorPrimeFactors n) :=
    List.mem_sublists.mp hxs
  have hxnodup := (divisorPrimeFactors_nodup n).sublist hsub
  have hprod : xs.toFinset.val.prod = xs.prod := by
    calc
      xs.toFinset.val.prod = xs.toFinset.prod id := by
        rw [Finset.prod_eq_multiset_prod]
        simp
      _ = xs.prod := by simpa using List.prod_toFinset id hxnodup
  rw [hprod, rosserWeight_prod_of_sublist checked level hsub]

private theorem divisorPrimeFactors_ne_nil {n : Nat} (hn : 1 < n) :
    divisorPrimeFactors n ≠ [] := by
  simp [divisorPrimeFactors, List.dedup_eq_nil,
    (Nat.primeFactorsList_ne_nil n).mpr hn]

/-- The canonical upper coefficient majorizes the coprimality indicator after
divisor summation for every natural input. -/
theorem upperRosserWeight_isUpperMoebius (level : Real) :
    BoundingSieve.IsUpperMoebius (upperRosserWeight level) := by
  intro n
  rcases n with (_ | _ | n)
  · simp
  · simp
  · have hn : 1 < n + 2 := by omega
    have hnzero : n + 2 ≠ 0 := by omega
    rw [if_neg (by omega)]
    change 0 ≤ ∑ d ∈ (n + 2).divisors,
      rosserWeight UpperRosserRank level d
    rw [sum_divisors_rosserWeight_eq_alternatingSublistSum
      UpperRosserRank level hnzero]
    exact rosserAlternatingSublistSum_upper_nonneg_of_ne_nil
      (RosserBoundary level) (divisorPrimeFactors_ne_nil hn)

/-- The canonical untruncated lower coefficient minorizes the coprimality
indicator after divisor summation for every natural input. -/
theorem lowerRosserWeight_isLowerMoebius (level : Real) :
    BoundingSieve.IsLowerMoebius (lowerRosserWeight level) := by
  intro n
  rcases n with (_ | _ | n)
  · simp
  · simp
  · have hn : 1 < n + 2 := by omega
    have hnzero : n + 2 ≠ 0 := by omega
    rw [if_neg (by omega)]
    change (∑ d ∈ (n + 2).divisors,
      rosserWeight LowerRosserRank level d) ≤ 0
    rw [sum_divisors_rosserWeight_eq_alternatingSublistSum
      LowerRosserRank level hnzero]
    exact rosserAlternatingSublistSum_lower_nonpos_of_ne_nil
      (RosserBoundary level) (divisorPrimeFactors_ne_nil hn)

end PrimesRestrictedDigits
