import PrimesRestrictedDigits.SieveDecomposition.RosserWeights

/-!
# Support of dimension-one Rosser weights

Upper support is globally below the level apart from one. Lower support also has an
unavoidable prime alternative; strict lower level support is therefore proved only for
divisors of the sieve prime product.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace PrimesRestrictedDigits

private theorem prod_lt_level_of_rosserBoundary
    {level : Real} {xs : List Nat} (hne : xs ≠ [])
    (hprime : ∀ p, p ∈ xs → p.Prime)
    (hcondition : RosserBoundary level xs) :
    (xs.prod : Real) < level := by
  obtain hnil | ⟨ys, p, hxs⟩ := xs.eq_nil_or_concat
  · exact (hne hnil).elim
  · subst xs
    have hp : p.Prime := hprime p (by simp)
    have hprodNat : 0 < (ys.concat p).prod := by
      apply List.prod_pos
      intro q hq
      exact (hprime q (by simpa using hq)).pos
    have hprod : (0 : Real) < ((ys.concat p).prod : Nat) := by
      exact_mod_cast hprodNat
    have hpTwo : (2 : Real) ≤ p := by exact_mod_cast hp.two_le
    have hfactor : (1 : Real) < (p : Real) ^ 2 := by nlinarith
    have hcondition' :
        ((ys.concat p).prod : Real) * (p : Real) ^ 2 < level := by
      simpa [RosserBoundary] using hcondition
    exact lt_trans (lt_mul_of_one_lt_right hprod hfactor) hcondition'

private theorem prime_of_mem_descendingPrimeFactors {d p : Nat}
    (hp : p ∈ descendingPrimeFactors d) : p.Prime := by
  exact Nat.prime_of_mem_primeFactorsList (by
    simpa [descendingPrimeFactors] using hp)

private theorem descendingPrimeFactors_sortedGT {d : Nat}
    (hd : Squarefree d) :
    (descendingPrimeFactors d).SortedGT := by
  have hnodup : (descendingPrimeFactors d).Nodup := by
    rw [descendingPrimeFactors, List.nodup_reverse]
    exact hd.nodup_primeFactorsList
  have hsorted : (descendingPrimeFactors d).SortedGE := by
    simpa [descendingPrimeFactors] using Nat.primeFactorsList_sorted d
  exact hsorted.sortedGT_of_nodup hnodup

private theorem prod_lt_level_of_dropLast_rosserBoundary
    {level : Real} {xs : List Nat} (hlength : 2 ≤ xs.length)
    (hprime : ∀ p, p ∈ xs → p.Prime) (hsorted : xs.SortedGT)
    (hcondition : RosserBoundary level xs.dropLast) :
    (xs.prod : Real) < level := by
  obtain hnil | ⟨ys, q, hxs⟩ := xs.eq_nil_or_concat
  · simp [hnil] at hlength
  · subst xs
    have hys : ys ≠ [] := by
      intro h
      simp [h] at hlength
    obtain hnil | ⟨zs, p, hysEq⟩ := ys.eq_nil_or_concat
    · exact (hys hnil).elim
    · subst ys
      have hp : p.Prime := hprime p (by simp)
      have hq : q.Prime := hprime q (by simp)
      have hpq : q < p := by
        have hsorted' : (zs.concat p ++ [q]).Pairwise
            (fun a b => a > b) := by
          simpa using hsorted.pairwise
        exact hsorted'.rel_of_mem_append (by simp) (by simp)
      have hbaseNat : 0 < (zs.concat p).prod := by
        apply List.prod_pos
        intro r hr
        apply (hprime r ?_).pos
        have hmem : r ∈ (zs.concat p).concat q := by
          rw [List.concat_eq_append, List.mem_append]
          exact Or.inl hr
        exact hmem
      have hbase : (0 : Real) < ((zs.concat p).prod : Nat) := by
        exact_mod_cast hbaseNat
      have hqpSq : (q : Real) < (p : Real) ^ 2 := by
        have hpTwo : (2 : Real) ≤ p := by exact_mod_cast hp.two_le
        have hpqReal : (q : Real) < p := by exact_mod_cast hpq
        nlinarith
      have hcondition' :
          ((zs.concat p).prod : Real) * (p : Real) ^ 2 < level := by
        simpa [RosserBoundary] using hcondition
      have hprodEq : ((zs.concat p).concat q).prod =
          (zs.concat p).prod * q := by
        simp [mul_assoc]
      rw [hprodEq, Nat.cast_mul]
      exact lt_trans (mul_lt_mul_of_pos_left hqpSq hbase) hcondition'

private theorem upper_admissible_prod_support
    {level : Real} {xs : List Nat}
    (hprime : ∀ p, p ∈ xs → p.Prime) (hsorted : xs.SortedGT)
    (hadmissible : IsParityAdmissible UpperRosserRank
      (RosserBoundary level) xs) :
    xs = [] ∨ (xs.prod : Real) < level := by
  by_cases hnil : xs = []
  · exact Or.inl hnil
  · right
    by_cases hodd : UpperRosserRank xs.length
    · apply prod_lt_level_of_rosserBoundary hnil hprime
      exact hadmissible xs (by simp) hodd
    · have heven : Even xs.length := Nat.not_odd_iff_even.mp hodd
      have hlength : 2 ≤ xs.length := by
        rcases heven with ⟨k, hk⟩
        have hpos : 0 < xs.length := List.length_pos_of_ne_nil hnil
        omega
      apply prod_lt_level_of_dropLast_rosserBoundary hlength hprime hsorted
      apply hadmissible xs.dropLast
      · exact (List.mem_inits _ _).2 (List.dropLast_prefix xs)
      · rcases heven with ⟨k, hk⟩
        refine ⟨k - 1, ?_⟩
        simp [List.length_dropLast]
        omega

private theorem lower_admissible_prod_support
    {level : Real} {xs : List Nat}
    (hprime : ∀ p, p ∈ xs → p.Prime) (hsorted : xs.SortedGT)
    (hadmissible : IsParityAdmissible LowerRosserRank
      (RosserBoundary level) xs) :
    xs = [] ∨ xs.length = 1 ∨ (xs.prod : Real) < level := by
  by_cases hnil : xs = []
  · exact Or.inl hnil
  · right
    by_cases hone : xs.length = 1
    · exact Or.inl hone
    · right
      have hlength : 2 ≤ xs.length := by
        have hpos : 0 < xs.length := List.length_pos_of_ne_nil hnil
        omega
      by_cases hrank : LowerRosserRank xs.length
      · apply prod_lt_level_of_rosserBoundary hnil hprime
        exact hadmissible xs (by simp) hrank
      · have hnotEven : ¬Even xs.length := by
          intro heven
          exact hrank ⟨by omega, heven⟩
        have hodd : Odd xs.length := Nat.not_even_iff_odd.mp hnotEven
        apply prod_lt_level_of_dropLast_rosserBoundary hlength hprime hsorted
        apply hadmissible xs.dropLast
        · exact (List.mem_inits _ _).2 (List.dropLast_prefix xs)
        · constructor
          · simp [List.length_dropLast]
            omega
          · rcases hodd with ⟨k, hk⟩
            refine ⟨k, ?_⟩
            simp [List.length_dropLast]
            omega

private theorem isRosserAdmissible_of_rosserWeight_ne_zero
    {checked : Nat → Prop} {level : Real} {d : Nat}
    (hweight : rosserWeight checked level d ≠ 0) :
    IsRosserAdmissible checked level d := by
  classical
  rw [rosserWeight] at hweight
  split at hweight
  · assumption
  · simp at hweight

private theorem prod_descendingPrimeFactors {d : Nat} (hd : d ≠ 0) :
    (descendingPrimeFactors d).prod = d := by
  simp [descendingPrimeFactors, Nat.prod_primeFactorsList hd]

/-- Global upper support: only one can survive at or above the level. -/
theorem upperRosserWeight_ne_zero_support {level : Real} {d : Nat}
    (hweight : upperRosserWeight level d ≠ 0) :
    d = 1 ∨ (d : Real) < level := by
  obtain ⟨hsquarefree, hadmissible⟩ :=
    isRosserAdmissible_of_rosserWeight_ne_zero
      (by simpa [upperRosserWeight] using hweight)
  let xs := descendingPrimeFactors d
  have hprime : ∀ p, p ∈ xs → p.Prime := by
    intro p hp
    exact prime_of_mem_descendingPrimeFactors hp
  have hsorted : xs.SortedGT :=
    descendingPrimeFactors_sortedGT hsquarefree
  have hprod : xs.prod = d :=
    prod_descendingPrimeFactors hsquarefree.ne_zero
  rcases upper_admissible_prod_support hprime hsorted hadmissible with
    hnil | hlt
  · left
    simpa [xs, hnil] using hprod.symm
  · right
    simpa [hprod] using hlt

/-- Global lower support has an unavoidable prime alternative. -/
theorem lowerRosserWeight_ne_zero_support {level : Real} {d : Nat}
    (hweight : lowerRosserWeight level d ≠ 0) :
    d = 1 ∨ d.Prime ∨ (d : Real) < level := by
  obtain ⟨hsquarefree, hadmissible⟩ :=
    isRosserAdmissible_of_rosserWeight_ne_zero
      (by simpa [lowerRosserWeight] using hweight)
  let xs := descendingPrimeFactors d
  have hprime : ∀ p, p ∈ xs → p.Prime := by
    intro p hp
    exact prime_of_mem_descendingPrimeFactors hp
  have hsorted : xs.SortedGT :=
    descendingPrimeFactors_sortedGT hsquarefree
  have hprod : xs.prod = d :=
    prod_descendingPrimeFactors hsquarefree.ne_zero
  rcases lower_admissible_prod_support hprime hsorted hadmissible with
    hnil | hone | hlt
  · left
    simpa [xs, hnil] using hprod.symm
  · right; left
    obtain ⟨p, hpList⟩ := List.length_eq_one_iff.mp hone
    have hp : p.Prime := hprime p (by simp [hpList])
    have hpd : p = d := by simpa [hpList] using hprod
    simpa [← hpd] using hp
  · exact Or.inr (Or.inr (by simpa [hprod] using hlt))

/-- Lower strict level support on divisors of a controlled sieve product. -/
theorem lowerRosserWeight_ne_zero_relative_support
    {level : Real} {P d : Nat} (hlevel : 1 < level)
    (hprimes : ∀ p, p.Prime → p ∣ P → (p : Real) < level)
    (hdP : d ∣ P) (hweight : lowerRosserWeight level d ≠ 0) :
    (d : Real) < level := by
  rcases lowerRosserWeight_ne_zero_support hweight with
    hone | hprime | hlt
  · simpa [hone] using hlevel
  · exact hprimes d hprime hdP
  · exact hlt

/-- Upper Rosser error is supported strictly below the level. -/
theorem errSum_upperRosserWeight_le_level
    (s : BoundingSieve) {level : Real} (hlevel : 1 < level) :
    s.errSum (upperRosserWeight level) ≤
      ∑ d ∈ (Nat.divisors s.prodPrimes).filter
        (fun d : Nat => (d : Real) < level), |s.rem d| := by
  calc
    s.errSum (upperRosserWeight level) ≤
        ∑ d ∈ (Nat.divisors s.prodPrimes).filter
          (fun d => upperRosserWeight level d ≠ 0), |s.rem d| :=
      s.errSum_le_sum_abs_rem_nonzeroSupport _
        (fun d _ => abs_upperRosserWeight_le_one level d)
    _ ≤ ∑ d ∈ (Nat.divisors s.prodPrimes).filter
        (fun d : Nat => (d : Real) < level), |s.rem d| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Finset.mem_filter] at hd ⊢
        refine ⟨hd.1, ?_⟩
        rcases upperRosserWeight_ne_zero_support hd.2 with hone | hlt
        · simpa [hone] using hlevel
        · exact hlt
      · intro d _ _
        exact abs_nonneg _

/-- Lower Rosser error is supported strictly below the level on a sieve whose
prime product satisfies the explicit prime bound. -/
theorem errSum_lowerRosserWeight_le_level
    (s : BoundingSieve) {level : Real} (hlevel : 1 < level)
    (hprimes : ∀ p, p.Prime → p ∣ s.prodPrimes → (p : Real) < level) :
    s.errSum (lowerRosserWeight level) ≤
      ∑ d ∈ (Nat.divisors s.prodPrimes).filter
        (fun d : Nat => (d : Real) < level), |s.rem d| := by
  calc
    s.errSum (lowerRosserWeight level) ≤
        ∑ d ∈ (Nat.divisors s.prodPrimes).filter
          (fun d => lowerRosserWeight level d ≠ 0), |s.rem d| :=
      s.errSum_le_sum_abs_rem_nonzeroSupport _
        (fun d _ => abs_lowerRosserWeight_le_one level d)
    _ ≤ ∑ d ∈ (Nat.divisors s.prodPrimes).filter
        (fun d : Nat => (d : Real) < level), |s.rem d| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Finset.mem_filter] at hd ⊢
        refine ⟨hd.1, ?_⟩
        have hdP : d ∣ s.prodPrimes := (Nat.mem_divisors.mp hd.1).1
        exact lowerRosserWeight_ne_zero_relative_support
          hlevel hprimes hdP hd.2
      · intro d _ _
        exact abs_nonneg _

/-- The upper coefficient of a prime is selected exactly below its cubic
boundary. -/
theorem upperRosserWeight_prime (level : Real) {p : Nat} (hp : p.Prime) :
    upperRosserWeight level p =
      if (p : Real) ^ 3 < level then -1 else 0 := by
  classical
  simp [upperRosserWeight, rosserWeight, IsRosserAdmissible,
    descendingPrimeFactors, Nat.primeFactorsList_prime hp,
    IsParityAdmissible, UpperRosserRank, RosserBoundary, hp.squarefree,
    ArithmeticFunction.moebius_apply_prime hp, pow_succ, mul_assoc]

/-- Every prime has lower coefficient minus one, independently of level. -/
@[simp] theorem lowerRosserWeight_prime (level : Real) {p : Nat}
    (hp : p.Prime) :
    lowerRosserWeight level p = -1 := by
  classical
  simp [lowerRosserWeight, rosserWeight, IsRosserAdmissible,
    descendingPrimeFactors, Nat.primeFactorsList_prime hp,
    IsParityAdmissible, LowerRosserRank, hp.squarefree,
    ArithmeticFunction.moebius_apply_prime hp]

/-- Equality at the strict cubic gate rejects an upper prime coefficient. -/
theorem upperRosserWeight_prime_boundary {p : Nat} (hp : p.Prime) :
    upperRosserWeight ((p : Real) ^ 3) p = 0 := by
  rw [upperRosserWeight_prime _ hp]
  simp

end PrimesRestrictedDigits
