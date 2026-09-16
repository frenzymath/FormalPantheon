import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureSums

/-!
# First-failure partition of a weighted Rosser sum

The finite inclusion-exclusion sum is partitioned by its unique first failed gate. Odd first
failures contribute with a plus sign and positive even first failures with a minus sign.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- One selected signed sublist contribution with local weights. -/
noncomputable def rosserWeightedContribution {alpha : Type*}
    (checked : Nat → Prop) (condition : List alpha → Prop)
    (weight : alpha → Real) (xs : List alpha) : Real :=
  rosserSignedContribution checked condition xs * (xs.map weight).prod

/-- The selected weighted inclusion-exclusion sum over all sublists. -/
noncomputable def rosserWeightedSublistSum {alpha : Type*}
    (checked : Nat → Prop) (condition : List alpha → Prop)
    (weight : alpha → Real) (ambient : List alpha) : Real :=
  (ambient.sublists.map
    (rosserWeightedContribution checked condition weight)).sum

private noncomputable def rosserNewFailureContribution {alpha : Type*}
    (checked : Nat → Prop) (condition : List alpha → Prop)
    (weight : alpha → Real) (xs : List alpha) (x : alpha) : Real := by
  classical
  exact if IsParityAdmissible checked condition xs ∧
      ¬IsParityAdmissible checked condition (xs ++ [x]) then
    (-1 : Real) ^ (xs ++ [x]).length * ((xs ++ [x]).map weight).prod
  else 0

private theorem weightedContribution_add_append_singleton
    {alpha : Type*} (checked : Nat → Prop)
    (condition : List alpha → Prop) (weight : alpha → Real)
    (xs : List alpha) (x : alpha) :
    rosserWeightedContribution checked condition weight xs +
        rosserWeightedContribution checked condition weight (xs ++ [x]) =
      (1 - weight x) *
          rosserWeightedContribution checked condition weight xs -
        rosserNewFailureContribution checked condition weight xs x := by
  classical
  by_cases hxs : IsParityAdmissible checked condition xs
  · by_cases hx : IsParityAdmissible checked condition (xs ++ [x])
    · simp [rosserWeightedContribution, rosserSignedContribution,
        rosserNewFailureContribution, hxs, hx, pow_succ]
      ring
    · simp [rosserWeightedContribution, rosserSignedContribution,
        rosserNewFailureContribution, hxs, hx, pow_succ]
      ring
  · have hx : ¬IsParityAdmissible checked condition (xs ++ [x]) := by
      intro h
      exact hxs ((isParityAdmissible_append_singleton_iff
        checked condition xs x).mp h).1
    simp [rosserWeightedContribution, rosserSignedContribution,
      rosserNewFailureContribution, hxs, hx]

private theorem rosserWeightedSublistSum_append_singleton
    {alpha : Type*} (checked : Nat → Prop)
    (condition : List alpha → Prop) (weight : alpha → Real)
    (ambient : List alpha) (x : alpha) :
    rosserWeightedSublistSum checked condition weight (ambient ++ [x]) =
      (1 - weight x) *
          rosserWeightedSublistSum checked condition weight ambient -
        (ambient.sublists.map fun xs ↦
          rosserNewFailureContribution checked condition weight xs x).sum := by
  classical
  simp only [rosserWeightedSublistSum, List.sublists_concat,
    List.map_append, List.sum_append, List.map_map]
  rw [← List.sum_map_add]
  simp only [Function.comp_apply]
  simp_rw [weightedContribution_add_append_singleton]
  generalize ambient.sublists = terms
  induction terms with
  | nil => simp
  | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

private noncomputable def rosserSignedFailureSum
    (checked : Nat → Prop) (level : Real) (weight : Nat → Real)
    (ambient : List Nat) : Real := by
  classical
  exact (ambient.sublists.map fun xs ↦
    if IsFirstRosserFailure checked level xs then
      (-1 : Real) ^ xs.length * (xs.map weight).prod *
        sieveDensityBelow ambient.toFinset weight (xs.getLastD 1)
    else 0).sum

private theorem density_concat_at_old_last
    {ambient xs : List Nat} {x : Nat}
    (hx : ∀ q ∈ ambient, x < q) (hxs : List.Sublist xs ambient)
    (hne : xs ≠ []) (weight : Nat → Real) :
    sieveDensityBelow (ambient ++ [x]).toFinset weight (xs.getLastD 1) =
      (1 - weight x) *
        sieveDensityBelow ambient.toFinset weight (xs.getLastD 1) := by
  have hxnot : x ∉ ambient := by
    intro hmem
    exact (Nat.lt_irrefl x) (hx x hmem)
  have hlastmem : xs.getLastD 1 ∈ ambient := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons a xs =>
        exact hxs.subset (by
          simpa only [List.getLastD_cons] using
            (List.getLastD_mem_cons (l := xs) (a := a)))
  have hxlast : (x : Real) < (xs.getLastD 1 : Real) := by
    exact_mod_cast hx _ hlastmem
  have hto : (ambient ++ [x]).toFinset = insert x ambient.toFinset := by
    simp [Finset.union_singleton]
  rw [sieveDensityBelow, hto, Finset.filter_insert, if_pos hxlast]
  rw [Finset.prod_insert]
  · rw [sieveDensityBelow]
  · simp [hxnot]

private theorem density_concat_at_new_last
    {ambient : List Nat} {x : Nat} (hx : ∀ q ∈ ambient, x < q)
    (weight : Nat → Real) :
    sieveDensityBelow (ambient ++ [x]).toFinset weight x = 1 := by
  have hto : (ambient ++ [x]).toFinset = insert x ambient.toFinset := by
    simp [Finset.union_singleton]
  have hfilter :
      (insert x ambient.toFinset).filter
          (fun q : Nat ↦ (q : Real) < x) = ∅ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_insert,
      Finset.notMem_empty, iff_false]
    rintro ⟨hqx | hq, hlt⟩
    · subst q
      norm_num at hlt
    · have hqx := hx q (List.mem_toFinset.mp hq)
      exact (not_lt_of_ge (by exact_mod_cast hqx.le)) hlt
  rw [sieveDensityBelow, hto, hfilter]
  simp

private theorem rosserSignedFailureSum_append_singleton
    (checked : Nat → Prop) (level : Real) (weight : Nat → Real)
    (ambient : List Nat) (x : Nat) (hx : ∀ q ∈ ambient, x < q) :
    rosserSignedFailureSum checked level weight (ambient ++ [x]) =
      (1 - weight x) * rosserSignedFailureSum checked level weight ambient +
        (ambient.sublists.map fun xs ↦
          rosserNewFailureContribution checked (RosserBoundary level)
            weight xs x).sum := by
  classical
  rw [rosserSignedFailureSum, rosserSignedFailureSum,
    List.sublists_concat, List.map_append, List.sum_append, List.map_map]
  have hold :
      (ambient.sublists.map fun xs ↦
        if IsFirstRosserFailure checked level xs then
          (-1 : Real) ^ xs.length * (xs.map weight).prod *
            sieveDensityBelow (ambient ++ [x]).toFinset weight
              (xs.getLastD 1)
        else 0).sum =
        (1 - weight x) *
          (ambient.sublists.map fun xs ↦
            if IsFirstRosserFailure checked level xs then
              (-1 : Real) ^ xs.length * (xs.map weight).prod *
                sieveDensityBelow ambient.toFinset weight (xs.getLastD 1)
            else 0).sum := by
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro xs hxs
    by_cases hfailure : IsFirstRosserFailure checked level xs
    · simp only [hfailure, if_true]
      rw [density_concat_at_old_last hx
        (List.mem_sublists.mp hxs) hfailure.1]
      ring
    · simp [hfailure]
  rw [hold]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro xs hxs
  simp only [Function.comp_apply]
  rw [isFirstRosserFailure_append_singleton_iff]
  by_cases hfailure :
      IsParityAdmissible checked (RosserBoundary level) xs ∧
        ¬IsParityAdmissible checked (RosserBoundary level) (xs ++ [x])
  · rw [if_pos hfailure, rosserNewFailureContribution, if_pos hfailure,
      List.getLastD_concat, density_concat_at_new_last hx]
    ring
  · rw [if_neg hfailure, rosserNewFailureContribution, if_neg hfailure]

private theorem weightedSublistSum_eq_prod_sub_signedFailureSum
    (checked : Nat → Prop) (level : Real) (weight : Nat → Real)
    {ambient : List Nat} (hzero : ¬checked 0) (hsorted : ambient.SortedGT) :
    rosserWeightedSublistSum checked (RosserBoundary level) weight ambient =
      (ambient.map fun p ↦ 1 - weight p).prod -
        rosserSignedFailureSum checked level weight ambient := by
  induction ambient using List.reverseRecOn with
  | nil =>
      simp [rosserWeightedSublistSum, rosserWeightedContribution,
        rosserSignedContribution, IsParityAdmissible, hzero,
        rosserSignedFailureSum, IsFirstRosserFailure]
  | append_singleton ambient x ih =>
      have hambient : ambient.SortedGT :=
        (hsorted.pairwise.sublist
          (List.sublist_append_left ambient [x])).sortedGT
      have hx : ∀ q ∈ ambient, x < q := by
        intro q hq
        exact (List.pairwise_append.mp hsorted.pairwise).2.2
          q hq x (by simp)
      rw [rosserWeightedSublistSum_append_singleton,
        rosserSignedFailureSum_append_singleton checked level weight
          ambient x hx,
        List.map_append, List.map_singleton, List.prod_append,
        List.prod_singleton, ih hambient]
      ring

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

private theorem signedUpperFailureSum_eq_neg
    (P : Finset Nat) (weight : Nat → Real) (level z : Real)
    (hcutoff : ∀ p ∈ P, (p : Real) < z) :
    rosserSignedFailureSum UpperRosserRank level weight
        (sieveFactorsBelow P z) =
      -upperRosserFailureSum P weight level z := by
  classical
  rw [upperRosserFailureSum_eq_firstFailureSum,
    rosserFirstFailureSum, rosserSignedFailureSum]
  rw [← List.sum_toFinset _ (sieveFactorsBelow_sortedGT P z).nodup.sublists]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro xs hxs
  by_cases hfirst : IsFirstRosserFailure UpperRosserRank level xs
  · rw [if_pos hfirst, if_pos hfirst,
      sieveFactorsBelow_toFinset_eq P hcutoff,
      hfirst.2.2.1.neg_one_pow]
    simp [rosserFailureMass]
  · rw [if_neg hfirst, if_neg hfirst]
    simp

private theorem signedLowerFailureSum_eq
    (P : Finset Nat) (weight : Nat → Real) (level z : Real)
    (hcutoff : ∀ p ∈ P, (p : Real) < z) :
    rosserSignedFailureSum LowerRosserRank level weight
        (sieveFactorsBelow P z) =
      lowerRosserFailureSum P weight level z := by
  classical
  rw [lowerRosserFailureSum_eq_firstFailureSum,
    rosserFirstFailureSum, rosserSignedFailureSum]
  rw [← List.sum_toFinset _ (sieveFactorsBelow_sortedGT P z).nodup.sublists]
  apply Finset.sum_congr rfl
  intro xs hxs
  by_cases hfirst : IsFirstRosserFailure LowerRosserRank level xs
  · rw [if_pos hfirst, if_pos hfirst,
      sieveFactorsBelow_toFinset_eq P hcutoff,
      hfirst.2.2.1.2.neg_one_pow]
    simp [rosserFailureMass]
  · rw [if_neg hfirst, if_neg hfirst]

private theorem prod_one_sub_factors_eq_density
    (P : Finset Nat) (weight : Nat → Real) {z : Real}
    (hcutoff : ∀ p ∈ P, (p : Real) < z) :
    ((sieveFactorsBelow P z).map fun p ↦ 1 - weight p).prod =
      sieveDensityBelow P weight z := by
  calc
    ((sieveFactorsBelow P z).map fun p ↦ 1 - weight p).prod =
        ∏ p ∈ (sieveFactorsBelow P z).toFinset, (1 - weight p) := by
      symm
      exact List.prod_toFinset _ (sieveFactorsBelow_sortedGT P z).nodup
    _ = ∏ p ∈ P, (1 - weight p) := by
      rw [sieveFactorsBelow_toFinset_eq P hcutoff]
    _ = sieveDensityBelow P weight z :=
      (sieveDensityBelow_eq_fullProduct P weight hcutoff).symm

theorem sum_sublists_upperRosserWeight_eq_density_add_failureSum
    (P : Finset Nat) (weight : Nat → Real) (level z : Real)
    (hcutoff : ∀ p ∈ P, (p : Real) < z) :
    rosserWeightedSublistSum UpperRosserRank (RosserBoundary level)
        weight (sieveFactorsBelow P z) =
      sieveDensityBelow P weight z +
        upperRosserFailureSum P weight level z := by
  rw [weightedSublistSum_eq_prod_sub_signedFailureSum
      UpperRosserRank level weight upperRosserRank_zero
      (sieveFactorsBelow_sortedGT P z),
    prod_one_sub_factors_eq_density P weight hcutoff,
    signedUpperFailureSum_eq_neg P weight level z hcutoff]
  ring

theorem sum_sublists_lowerRosserWeight_eq_density_sub_failureSum
    (P : Finset Nat) (weight : Nat → Real) (level z : Real)
    (hcutoff : ∀ p ∈ P, (p : Real) < z) :
    rosserWeightedSublistSum LowerRosserRank (RosserBoundary level)
        weight (sieveFactorsBelow P z) =
      sieveDensityBelow P weight z -
        lowerRosserFailureSum P weight level z := by
  rw [weightedSublistSum_eq_prod_sub_signedFailureSum
      LowerRosserRank level weight lowerRosserRank_zero
      (sieveFactorsBelow_sortedGT P z),
    prod_one_sub_factors_eq_density P weight hcutoff,
    signedLowerFailureSum_eq P weight level z hcutoff]

end PrimesRestrictedDigits
