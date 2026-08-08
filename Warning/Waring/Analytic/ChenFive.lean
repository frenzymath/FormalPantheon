import Waring.Analytic.ChenFiveLocal
import Waring.Analytic.ChenFiveConstant

/-!
# Conditional assembly of Chen's Lemma 5

This file assembles the normalized CRT theorem and Chen's explicit finite
product.  The only remaining hypotheses are the primitive prime-field input
to Lemma 4 and Hua's degree-five estimate at `2`, `3`, `5`, and `7`.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- A source-shaped overestimate for the local factor at a distinct prime. -/
noncomputable def chenFivePrimeFactor (p : Nat) : Real :=
  if p < 11 then 5 ^ 3
  else if p ≤ 31 then (p : Real) ^ (1 / 5 : Real)
  else if p ≤ 211 then 5 * (p : Real) ^ (-3 / 10 : Real)
  else 1

/-- The four primes to which Hua's uniform degree-five factor is applied. -/
def chenFiveTinyPrimes : Finset Nat := {2, 3, 5, 7}

/-- The seven primes carrying the `p^(1/5)` overestimate in equation (7). -/
def chenFiveLowPrimes : Finset Nat := {11, 13, 17, 19, 23, 29, 31}

/-- The 36 primes carrying the `5*p^(-3/10)` factor in equation (7). -/
def chenFiveMediumPrimes : Finset Nat :=
  {37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103,
    107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
    179, 181, 191, 193, 197, 199, 211}

/-- Every prime below 212 that can contribute a nonunit factor. -/
def chenFiveSpecialPrimes : Finset Nat :=
  chenFiveTinyPrimes ∪ chenFiveLowPrimes ∪ chenFiveMediumPrimes

/-- Exact upper endpoint needed to show the middle local factor is at least
one. -/
lemma rpow_three_tenths_le_five_of_le_twoHundredEleven
    {p : Nat} (hpUpper : p ≤ 211) :
    (p : Real) ^ (3 / 10 : Real) ≤ 5 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (10 : Nat) ≠ 0)
    (by norm_num : (0 : Real) ≤ 5)
  rw [← Real.rpow_mul_natCast (by positivity : (0 : Real) ≤ p)]
  norm_num [Real.rpow_natCast]
  have hpReal : (p : Real) ≤ 211 := by exact_mod_cast hpUpper
  have hpCube : (p : Real) ^ 3 ≤ (211 : Real) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hpReal 3
  norm_num at hpCube ⊢
  linarith

/-- Exact lower endpoint needed to absorb the decreasing local factor. -/
lemma five_le_rpow_three_tenths_of_twoHundredTwentyThree_le
    {p : Nat} (hpLower : 223 ≤ p) :
    (5 : Real) ≤ (p : Real) ^ (3 / 10 : Real) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (10 : Nat) ≠ 0)
    (Real.rpow_nonneg (by positivity) _)
  rw [← Real.rpow_mul_natCast (by positivity : (0 : Real) ≤ p)]
  norm_num [Real.rpow_natCast]
  have hpReal : (223 : Real) ≤ p := by exact_mod_cast hpLower
  have hpCube : (223 : Real) ^ 3 ≤ (p : Real) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hpReal 3
  norm_num at hpCube ⊢
  linarith

/-- Throughout the medium range, the decreasing factor is still at least
one. -/
lemma one_le_five_mul_rpow_neg_three_tenths
    {p : Nat} (hp : 0 < p) (hpUpper : p ≤ 211) :
    (1 : Real) ≤ 5 * (p : Real) ^ (-3 / 10 : Real) := by
  have hroot := rpow_three_tenths_le_five_of_le_twoHundredEleven hpUpper
  have hrootPos : 0 < (p : Real) ^ (3 / 10 : Real) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp) _
  rw [show (-3 / 10 : Real) = -(3 / 10) by ring,
    Real.rpow_neg (by positivity : (0 : Real) ≤ p), ← div_eq_mul_inv,
    le_div_iff₀ hrootPos]
  simpa using hroot

/-- At and above 223, the decreasing candidate is absorbed by one. -/
lemma five_mul_rpow_neg_three_tenths_le_one
    {p : Nat} (hpLower : 223 ≤ p) :
    5 * (p : Real) ^ (-3 / 10 : Real) ≤ 1 := by
  have hroot := five_le_rpow_three_tenths_of_twoHundredTwentyThree_le hpLower
  have hp : 0 < p := by omega
  have hrootPos : 0 < (p : Real) ^ (3 / 10 : Real) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp) _
  rw [show (-3 / 10 : Real) = -(3 / 10) by ring,
    Real.rpow_neg (by positivity : (0 : Real) ≤ p), ← div_eq_mul_inv,
    div_le_one hrootPos]
  exact hroot

/-- A prime strictly above 211 is at least 223. -/
lemma twoHundredTwentyThree_le_of_prime_of_twoHundredEleven_lt
    {p : Nat} (hp : p.Prime) (hpLower : 211 < p) : 223 ≤ p := by
  by_contra hp223
  have hpUpper : p ≤ 222 := by omega
  have htable : ∀ r : Fin 223, 211 < r.val → ¬ r.val.Prime := by
    set_option maxRecDepth 100000 in
      decide
  exact (htable ⟨p, by omega⟩ hpLower) hp

/-- Above 223 Chen's exact max/min local factor is one. -/
lemma chenFourPrimeFactor_eq_one_of_twoHundredTwentyThree_le
    {p : Nat} (hpLower : 223 ≤ p) :
    chenFourPrimeFactor p = 1 := by
  rw [chenFourPrimeFactor]
  apply max_eq_left
  refine (min_le_right _ _).trans ?_
  have hexponent : (-(3 / 10 : Real)) = (-3 / 10 : Real) := by ring
  rw [hexponent]
  exact five_mul_rpow_neg_three_tenths_le_one hpLower

/-- For every prime at least eleven, the exact Lemma 4 factor is bounded by
the piecewise factor used in Chen's finite product. -/
lemma chenFourPrimeFactor_le_chenFivePrimeFactor
    {p : Nat} (hp : p.Prime) (hpLarge : 11 ≤ p) :
    chenFourPrimeFactor p ≤ chenFivePrimeFactor p := by
  rw [chenFivePrimeFactor, if_neg (by omega)]
  split_ifs with hpLow hpMedium
  · rw [chenFourPrimeFactor]
    apply max_le
    · exact Real.one_le_rpow (by exact_mod_cast hp.one_le) (by norm_num)
    · exact min_le_left _ _
  · rw [chenFourPrimeFactor]
    apply max_le
    · exact one_le_five_mul_rpow_neg_three_tenths hp.pos hpMedium
    · calc
        min ((p : Real) ^ (1 / 5 : Real))
              (5 * (p : Real) ^ (-(3 / 10 : Real))) ≤
            5 * (p : Real) ^ (-(3 / 10 : Real)) := min_le_right _ _
        _ = 5 * (p : Real) ^ (-3 / 10 : Real) := by congr 2; ring
  · have hp223 :=
      twoHundredTwentyThree_le_of_prime_of_twoHundredEleven_lt hp (by omega)
    rw [chenFourPrimeFactor_eq_one_of_twoHundredTwentyThree_le hp223]

/-- Kernel-checked classification of every prime below 212 into Chen's three
fixed exceptional sets. -/
lemma chenFiveSpecialPrimeTable :
    ∀ p : Fin 212, p.val.Prime → p.val ∈ chenFiveSpecialPrimes := by
  set_option maxRecDepth 100000 in
    decide

/-- Every member of the explicit special set is prime. -/
lemma prime_of_mem_chenFiveSpecialPrimes {p : Nat}
    (hp : p ∈ chenFiveSpecialPrimes) : p.Prime := by
  revert p
  set_option maxRecDepth 100000 in
    decide

/-- Every member of the explicit special set is below 212. -/
lemma lt_twoHundredTwelve_of_mem_chenFiveSpecialPrimes {p : Nat}
    (hp : p ∈ chenFiveSpecialPrimes) : p < 212 := by
  revert p
  set_option maxRecDepth 100000 in
    decide

/-- A prime outside the fixed exceptional set has source-shaped factor one. -/
lemma chenFivePrimeFactor_eq_one_of_not_mem {p : Nat} (hp : p.Prime)
    (hmem : p ∉ chenFiveSpecialPrimes) : chenFivePrimeFactor p = 1 := by
  have hpLower : 212 ≤ p := by
    by_contra hp212
    have hpFin : p < 212 := by omega
    exact hmem (chenFiveSpecialPrimeTable ⟨p, hpFin⟩ hp)
  rw [chenFivePrimeFactor, if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- Every source-shaped local factor is nonnegative. -/
lemma chenFivePrimeFactor_nonneg (p : Nat) : 0 ≤ chenFivePrimeFactor p := by
  rw [chenFivePrimeFactor]
  split_ifs <;> positivity

/-- Every exceptional prime factor is at least one, allowing a partial prime
divisor product to be enlarged to the full fixed set. -/
lemma one_le_chenFivePrimeFactor_of_prime_lt_twoHundredTwelve
    {p : Nat} (hp : p.Prime) (hpUpper : p < 212) :
    (1 : Real) ≤ chenFivePrimeFactor p := by
  rw [chenFivePrimeFactor]
  split_ifs with hpTiny hpLow hpMedium
  · norm_num
  · exact Real.one_le_rpow (by exact_mod_cast hp.one_le) (by norm_num)
  · exact one_le_five_mul_rpow_neg_three_tenths hp.pos hpMedium
  · omega

/-- Factors outside the fixed set can be removed from the distinct-prime
product. -/
lemma fivePolynomialFactor_chenFive_eq_filter_special (q : Nat) :
    fivePolynomialFactor chenFivePrimeFactor q =
      ∏ p ∈ q.primeFactors.filter (· ∈ chenFiveSpecialPrimes),
        chenFivePrimeFactor p := by
  rw [fivePolynomialFactor]
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro p hpPrime hpFilter
  apply chenFivePrimeFactor_eq_one_of_not_mem
  · exact Nat.prime_of_mem_primeFactors hpPrime
  · simpa only [Finset.mem_filter, hpPrime, true_and] using hpFilter

/-- The local-factor product for any modulus is bounded by the product over
the full fixed exceptional set. -/
lemma fivePolynomialFactor_chenFive_le_specialProduct (q : Nat) :
    fivePolynomialFactor chenFivePrimeFactor q ≤
      ∏ p ∈ chenFiveSpecialPrimes, chenFivePrimeFactor p := by
  rw [fivePolynomialFactor_chenFive_eq_filter_special]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p _
    exact chenFivePrimeFactor_nonneg p
  · intro p hp _
    exact one_le_chenFivePrimeFactor_of_prime_lt_twoHundredTwelve
      (prime_of_mem_chenFiveSpecialPrimes hp)
      (lt_twoHundredTwelve_of_mem_chenFiveSpecialPrimes hp)

/-- Evaluation of the four uniform Hua factors. -/
lemma chenFiveTinyProduct_eq :
    (∏ p ∈ chenFiveTinyPrimes, chenFivePrimeFactor p) =
      (5 ^ 3 : Real) ^ 4 := by
  norm_num [chenFiveTinyPrimes, chenFivePrimeFactor]

/-- Evaluation of the seven increasing factors. -/
lemma chenFiveLowProduct_eq :
    (∏ p ∈ chenFiveLowPrimes, chenFivePrimeFactor p) =
      (chenFiveSmallPrimeProduct : Real) ^ (1 / 5 : Real) := by
  calc
    (∏ p ∈ chenFiveLowPrimes, chenFivePrimeFactor p) =
        ∏ p ∈ chenFiveLowPrimes, (p : Real) ^ (1 / 5 : Real) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp only [chenFiveLowPrimes, Finset.mem_insert,
        Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [chenFivePrimeFactor]
    _ = (∏ p ∈ chenFiveLowPrimes, (p : Real)) ^ (1 / 5 : Real) := by
      rw [Real.finsetProd_rpow _ _ (fun _ _ ↦ by positivity)]
    _ = (chenFiveSmallPrimeProduct : Real) ^ (1 / 5 : Real) := by
      norm_num [chenFiveLowPrimes, chenFiveSmallPrimeProduct]

/-- Evaluation of the 36 decreasing factors. -/
lemma chenFiveMediumProduct_eq :
    (∏ p ∈ chenFiveMediumPrimes, chenFivePrimeFactor p) =
      5 ^ 36 *
        (chenFiveMediumPrimeProduct : Real) ^ (-3 / 10 : Real) := by
  calc
    (∏ p ∈ chenFiveMediumPrimes, chenFivePrimeFactor p) =
        ∏ p ∈ chenFiveMediumPrimes,
          5 * (p : Real) ^ (-3 / 10 : Real) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp only [chenFiveMediumPrimes, Finset.mem_insert,
        Finset.mem_singleton] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num [chenFivePrimeFactor]
    _ = 5 ^ chenFiveMediumPrimes.card *
        (∏ p ∈ chenFiveMediumPrimes, (p : Real)) ^
          (-3 / 10 : Real) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Real.finsetProd_rpow _ _ (fun _ _ ↦ by positivity)]
    _ = 5 ^ 36 *
        (chenFiveMediumPrimeProduct : Real) ^ (-3 / 10 : Real) := by
      norm_num [chenFiveMediumPrimes, chenFiveMediumPrimeProduct]

/-- The full fixed-set product is precisely Hua's four factors times Chen's
equation (7) expression. -/
lemma chenFiveSpecialProduct_eq :
    (∏ p ∈ chenFiveSpecialPrimes, chenFivePrimeFactor p) =
      (5 ^ 3 : Real) ^ 4 *
        (chenFiveSmallPrimeProduct : Real) ^ (1 / 5 : Real) * 5 ^ 36 *
        (chenFiveMediumPrimeProduct : Real) ^ (-3 / 10 : Real) := by
  rw [chenFiveSpecialPrimes,
    Finset.prod_union
      (by decide : Disjoint (chenFiveTinyPrimes ∪ chenFiveLowPrimes)
        chenFiveMediumPrimes),
    Finset.prod_union (by decide : Disjoint chenFiveTinyPrimes chenFiveLowPrimes),
    chenFiveTinyProduct_eq, chenFiveLowProduct_eq, chenFiveMediumProduct_eq]
  ring

/-- Chen's complete distinct-prime factor is at most the printed `10^15`. -/
theorem fivePolynomialFactor_chenFive_le_tenPowFifteen (q : Nat) :
    fivePolynomialFactor chenFivePrimeFactor q ≤ 10 ^ 15 := by
  calc
    fivePolynomialFactor chenFivePrimeFactor q ≤
        ∏ p ∈ chenFiveSpecialPrimes, chenFivePrimeFactor p :=
      fivePolynomialFactor_chenFive_le_specialProduct q
    _ = (5 ^ 3 : Real) ^ 4 *
        (chenFiveSmallPrimeProduct : Real) ^ (1 / 5 : Real) * 5 ^ 36 *
        (chenFiveMediumPrimeProduct : Real) ^ (-3 / 10 : Real) :=
      chenFiveSpecialProduct_eq
    _ ≤ 10 ^ 15 := by
      calc
        (5 ^ 3 : Real) ^ 4 *
              (chenFiveSmallPrimeProduct : Real) ^ (1 / 5 : Real) * 5 ^ 36 *
              (chenFiveMediumPrimeProduct : Real) ^ (-3 / 10 : Real) =
            (chenFiveSmallPrimeProduct : Real) ^ (1 / 5 : Real) * 5 ^ 36 *
              (chenFiveMediumPrimeProduct : Real) ^ (-3 / 10 : Real) *
              (5 ^ 3) ^ 4 := by ring
        _ ≤ 10 ^ 15 := chen_five_exceptional_mul_hua_small_factors_le

/-- The remaining Hua input at the four primes below eleven. -/
def ChenFiveHuaSmallPrimePowerBound : Prop :=
  ∀ (p alpha : Nat) (hp : p.Prime), 0 < alpha → p < 11 →
    ∀ (a : FiveCoefficients (p ^ alpha)),
      PrimitiveFiveCoefficients a →
        ‖@fivePolynomialCompleteSum (p ^ alpha)
            ⟨pow_ne_zero alpha hp.ne_zero⟩ a‖ ≤
          125 * (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real))

/-- The remaining prime-field input at primes at least eleven. -/
def ChenFiveLargePrimeFieldBound : Prop :=
  ∀ (p : Nat) (hp : p.Prime), 11 ≤ p →
    @ChenFourPrimeFieldBound p ⟨hp.ne_zero⟩ (chenFourPrimeFactor p)

/-- Conditional source-shaped Lemma 5: after the two isolated analytic inputs,
all local-to-global algebra and the printed `10^15` constant are proved. -/
theorem chen_five_polynomialCompleteSum_bound
    (hsmall : ChenFiveHuaSmallPrimePowerBound)
    (hlarge : ChenFiveLargePrimeFieldBound)
    {q : Nat} [NeZero q] (a : FiveCoefficients q)
    (ha : PrimitiveFiveCoefficients a) :
    ‖fivePolynomialCompleteSum a‖ ≤
      10 ^ 15 * (q : Real) ^ (4 / 5 : Real) := by
  have hlocal : FivePolynomialPrimePowerBound chenFivePrimeFactor := by
    intro p alpha hp hAlpha b hb
    by_cases hpLarge : 11 ≤ p
    · have hExact :=
        norm_fivePolynomialCompleteSum_primePower_le_chenFourPrimeFactor
          p alpha hp hpLarge (hlarge p hp hpLarge) hAlpha b hb
      exact hExact.trans (mul_le_mul_of_nonneg_right
        (chenFourPrimeFactor_le_chenFivePrimeFactor hp hpLarge)
        (Real.rpow_nonneg (by positivity) _))
    · have hpSmall : p < 11 := by omega
      have h := hsmall p alpha hp hAlpha hpSmall b hb
      rw [chenFivePrimeFactor, if_pos hpSmall]
      norm_num
      simpa only [Nat.cast_pow] using h
  have hGlobal :=
    norm_fivePolynomialCompleteSum_le_fivePolynomialFactor
      chenFivePrimeFactor hlocal a ha
  exact hGlobal.trans (mul_le_mul_of_nonneg_right
    (fivePolynomialFactor_chenFive_le_tenPowFifteen q)
    (Real.rpow_nonneg (by positivity) _))

end Waring.Analytic
