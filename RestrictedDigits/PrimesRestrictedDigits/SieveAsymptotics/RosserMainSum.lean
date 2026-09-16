import PrimesRestrictedDigits.SieveAsymptotics.RosserFailurePartition
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Rosser selected main-sum identities

Squarefree divisors of the sieving product are reindexed by decreasing prime tuples. The
first-failure partition then gives Iwaniec's exact finite equations (4.1)--(4.2).
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace PrimesRestrictedDigits

theorem arithmeticFunction_prod_eq_prod_map
    {nu : ArithmeticFunction Real} (hnu : nu.IsMultiplicative)
    {xs : List Nat} (hprime : ∀ p ∈ xs, p.Prime)
    (hnodup : xs.Nodup) :
    nu xs.prod = (xs.map nu).prod := by
  calc
    nu xs.prod = nu (∏ p ∈ xs.toFinset, p) := by
      congr 1
      simpa using (List.prod_toFinset id hnodup).symm
    _ = ∏ p ∈ xs.toFinset, nu p := by
      exact hnu.map_prod_of_prime xs.toFinset (by simpa using hprime)
    _ = (xs.map nu).prod := by
      simpa using List.prod_toFinset nu hnodup

theorem descendingPrimeFactors_prod_of_sortedPrimeList
    {xs : List Nat} (hprime : ∀ p ∈ xs, p.Prime)
    (hsorted : xs.SortedGT) :
    descendingPrimeFactors xs.prod = xs := by
  have hperm : xs.Perm xs.prod.primeFactorsList :=
    Nat.primeFactorsList_unique rfl hprime
  have heq : xs.prod.primeFactorsList = xs.reverse :=
    List.Perm.eq_reverse_of_sortedLE_of_sortedGE hperm.symm
      (Nat.primeFactorsList_sorted _) hsorted.sortedGE
  simp [descendingPrimeFactors, heq]

private theorem squarefree_prod_of_sortedPrimeList
    {xs : List Nat} (hprime : ∀ p ∈ xs, p.Prime)
    (hsorted : xs.SortedGT) : Squarefree xs.prod := by
  have hprod : xs.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hprime 0 hzero).ne_zero rfl
  rw [Nat.squarefree_iff_nodup_primeFactorsList hprod]
  have hcanonical :=
    descendingPrimeFactors_prod_of_sortedPrimeList hprime hsorted
  simp only [descendingPrimeFactors] at hcanonical
  rw [← List.nodup_reverse, hcanonical]
  exact hsorted.nodup

private theorem moebius_prod_of_sortedPrimeList
    {xs : List Nat} (hprime : ∀ p ∈ xs, p.Prime)
    (hsorted : xs.SortedGT) :
    (ArithmeticFunction.moebius xs.prod : Real) =
      (-1 : Real) ^ xs.length := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree
      (squarefree_prod_of_sortedPrimeList hprime hsorted),
    ArithmeticFunction.cardFactors_apply]
  have hcanonical :=
    descendingPrimeFactors_prod_of_sortedPrimeList hprime hsorted
  simp only [descendingPrimeFactors] at hcanonical
  have hlength : xs.prod.primeFactorsList.length = xs.length := by
    rw [← List.length_reverse, hcanonical]
  rw [hlength]
  norm_cast

theorem rosserWeight_prod_of_sortedPrimeList
    (checked : Nat → Prop) (level : Real) {xs : List Nat}
    (hprime : ∀ p ∈ xs, p.Prime) (hsorted : xs.SortedGT) :
    rosserWeight checked level xs.prod =
      rosserSignedContribution checked (RosserBoundary level) xs := by
  classical
  have hsquarefree := squarefree_prod_of_sortedPrimeList hprime hsorted
  have hcanonical :=
    descendingPrimeFactors_prod_of_sortedPrimeList hprime hsorted
  have hmoebius := moebius_prod_of_sortedPrimeList hprime hsorted
  rw [rosserWeight, rosserSignedContribution]
  simp only [IsRosserAdmissible, hsquarefree, true_and, hcanonical]
  split_ifs <;> simp_all

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

private theorem sieveFactorsBelow_toFinset_eq
    (P : Finset Nat) {z : Real}
    (hcutoff : ∀ p ∈ P, (p : Real) < z) :
    (sieveFactorsBelow P z).toFinset = P := by
  ext p
  constructor
  · intro hp
    exact (mem_sieveFactorsBelow.mp (List.mem_toFinset.mp hp)).1
  · intro hp
    exact List.mem_toFinset.mpr
      (mem_sieveFactorsBelow.mpr ⟨hp, hcutoff p hp⟩)

theorem boundingSieveMainSum_rosserWeight_eq_weightedSublistSum
    (s : BoundingSieve) (checked : Nat → Prop) (level z : Real)
    (hcutoff : ∀ p ∈ s.prodPrimes.primeFactors, (p : Real) < z) :
    s.mainSum (rosserWeight checked level) =
      rosserWeightedSublistSum checked (RosserBoundary level) s.nu
        (sieveFactorsBelow s.prodPrimes.primeFactors z) := by
  classical
  let P := s.prodPrimes.primeFactors
  let ambient := sieveFactorsBelow P z
  have hambient : ambient.Nodup := (sieveFactorsBelow_sortedGT P z).nodup
  have hto : ambient.toFinset = P :=
    sieveFactorsBelow_toFinset_eq P hcutoff
  have hfilter :
      (∑ d ∈ (Nat.divisors s.prodPrimes).filter Squarefree,
        rosserWeight checked level d * s.nu d) =
        ∑ d ∈ Nat.divisors s.prodPrimes,
          rosserWeight checked level d * s.nu d := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    exact (hnot (Finset.mem_filter.mpr
      ⟨hd, s.squarefree_of_mem_divisors_prodPrimes hd⟩)).elim
  rw [BoundingSieve.mainSum, ← hfilter,
    Nat.sum_divisors_filter_squarefree s.prodPrimes_ne_zero,
    Nat.factors_eq]
  change (∑ t ∈ P.powerset,
      rosserWeight checked level t.val.prod * s.nu t.val.prod) =
    rosserWeightedSublistSum checked (RosserBoundary level) s.nu ambient
  rw [← hto]
  rw [sum_powerset_eq_sum_sublists ambient hambient
    (fun t ↦ rosserWeight checked level t.val.prod * s.nu t.val.prod)]
  rw [rosserWeightedSublistSum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro xs hxs
  have hsub : List.Sublist xs ambient := List.mem_sublists.mp hxs
  have hsource := sourceTuple_of_sublist_sieveFactorsBelow hsub
  have hprime : ∀ p ∈ xs, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (hsource.2 p hp).1
  have hxnodup := hsource.1.nodup
  have hprod : xs.toFinset.val.prod = xs.prod := by
    calc
      xs.toFinset.val.prod = xs.toFinset.prod id := by
        rw [Finset.prod_eq_multiset_prod]
        simp
      _ = xs.prod := by simpa using List.prod_toFinset id hxnodup
  rw [hprod,
    rosserWeight_prod_of_sortedPrimeList checked level hprime hsource.1,
    arithmeticFunction_prod_eq_prod_map s.nu_mult hprime hxnodup]
  rfl

/-- Iwaniec's finite upper selected-main identity, equation (4.1). -/
theorem boundingSieveMainSum_upperRosserWeight_eq_add_failureSum
    (s : BoundingSieve) (level z : Real)
    (hcutoff : ∀ p ∈ s.prodPrimes.primeFactors, (p : Real) < z) :
    s.mainSum (upperRosserWeight level) =
      sieveDensityBelow s.prodPrimes.primeFactors s.nu z +
        upperRosserFailureSum s.prodPrimes.primeFactors s.nu level z := by
  change s.mainSum (rosserWeight UpperRosserRank level) = _
  rw [boundingSieveMainSum_rosserWeight_eq_weightedSublistSum
    s UpperRosserRank level z hcutoff]
  exact sum_sublists_upperRosserWeight_eq_density_add_failureSum
    s.prodPrimes.primeFactors s.nu level z hcutoff

/-- Iwaniec's finite lower selected-main identity, equation (4.2). -/
theorem boundingSieveMainSum_lowerRosserWeight_eq_sub_failureSum
    (s : BoundingSieve) (level z : Real)
    (hcutoff : ∀ p ∈ s.prodPrimes.primeFactors, (p : Real) < z) :
    s.mainSum (lowerRosserWeight level) =
      sieveDensityBelow s.prodPrimes.primeFactors s.nu z -
        lowerRosserFailureSum s.prodPrimes.primeFactors s.nu level z := by
  change s.mainSum (rosserWeight LowerRosserRank level) = _
  rw [boundingSieveMainSum_rosserWeight_eq_weightedSublistSum
    s LowerRosserRank level z hcutoff]
  exact sum_sublists_lowerRosserWeight_eq_density_sub_failureSum
    s.prodPrimes.primeFactors s.nu level z hcutoff

end PrimesRestrictedDigits
