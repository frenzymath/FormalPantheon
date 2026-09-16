import Waring.Analytic.ChenTwoConstant
import Waring.Analytic.NonfivePrimePowerBounds
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Chen's Lemma 2

This file assembles the local prime-power estimates through normalized CRT
factorization and proves Chen's global `40*q^(4/5)` complete-sum bound
[CHEN1964-EN, pp. 1547-1548; CHEN1964-ZH, pp. 715-716].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The local constant attached to a distinct prime divisor in Chen's
factorization. -/
noncomputable def chenTwoPrimeFactor (p : Nat) : Real :=
  if p = 5 then 5
  else if 5 ∣ p - 1 ∧ p ≤ 128 then 4 * (p : Real) ^ (-3 / 10 : Real)
  else 1

/-- The product of Chen's local constants over the distinct prime divisors. -/
noncomputable def chenTwoFactor (q : Nat) : Real :=
  ∏ p ∈ q.primeFactors, chenTwoPrimeFactor p

/-- The prime factors of a positive prime power form a singleton. -/
lemma primeFactors_primePow {p alpha : Nat} (hp : p.Prime)
    (hAlpha : 0 < alpha) :
    (p ^ alpha).primeFactors = {p} := by
  rw [Nat.primeFactors_pow p hAlpha.ne']
  ext q
  simp only [Nat.mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hqp, _⟩
    exact (Nat.dvd_prime hp).mp hqp |>.resolve_left hq.ne_one
  · rintro rfl
    exact ⟨hp, dvd_rfl, hp.ne_zero⟩

/-- The factor product is multiplicative on positive coprime moduli. -/
lemma chenTwoFactor_mul {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcoprime : m.Coprime n) :
    chenTwoFactor (m * n) = chenTwoFactor m * chenTwoFactor n := by
  rw [chenTwoFactor, chenTwoFactor, chenTwoFactor,
    Nat.primeFactors_mul hm hn, Finset.prod_union hcoprime.disjoint_primeFactors]

/-- Raising a prime power to the real exponent `4/5` agrees with the exponent
notation used in the local estimates. -/
lemma primePow_rpow_four_fifths (p alpha : Nat) :
    (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) =
      (p : Real) ^ (((4 * alpha : Nat) : Real) / 5) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity : (0 : Real) ≤ p)]
  congr 1
  push_cast
  ring

/-- The three non-five branches and the five-adic branch combine into one
prime-power estimate with the local factor `chenTwoPrimeFactor p`. -/
theorem chen_two_primePower {p alpha : Nat} [NeZero p] (hp : p.Prime)
    (hAlpha : 0 < alpha) (a : ZMod (p ^ alpha)) (ha : IsUnit a) :
    ‖completePowerSum 5 a‖ ≤
      chenTwoPrimeFactor p *
        (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) := by
  obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective a
  have hbPow : b.Coprime (p ^ alpha) :=
    (ZMod.isUnit_iff_coprime b (p ^ alpha)).mp ha
  have hb : b.Coprime p :=
    (Nat.coprime_pow_right_iff hAlpha b p).mp hbPow
  rw [primePow_rpow_four_fifths p alpha]
  by_cases hpFive : p = 5
  · subst p
    simpa [chenTwoPrimeFactor] using
      chen_two_five_primePower hAlpha b hb
  · by_cases hFive : 5 ∣ p - 1
    · by_cases hpUpper : p ≤ 128
      · simpa [chenTwoPrimeFactor, hpFive, hFive, hpUpper] using
          chen_two_exceptional_primePower hp hAlpha hFive hpUpper b hb
      · have hpLower : 128 ≤ p := by omega
        simpa [chenTwoPrimeFactor, hpFive, hFive, hpUpper] using
          chen_two_large_exceptional_primePower hp hAlpha hFive hpLower b hb
    · have hGcd : (p - 1).gcd 5 ≠ 5 := by
        intro hEq
        exact hFive (Nat.gcd_eq_right_iff_dvd.mp hEq)
      simpa [chenTwoPrimeFactor, hpFive, hFive] using
        chen_two_generic_primePower hp hAlpha hpFive hGcd b hb

/-- The complete sum is bounded by the product of its distinct local constants
times `q^(4/5)`. -/
theorem norm_completePowerSum_le_chenTwoFactor {q : Nat} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    ‖completePowerSum 5 a‖ ≤
      chenTwoFactor q * (q : Real) ^ (4 / 5 : Real) := by
  let motive : Nat → Prop := fun n =>
    ∀ (hn : n ≠ 0) (b : ZMod n), IsUnit b →
      ‖@completePowerSum n ⟨hn⟩ 5 b‖ ≤
        chenTwoFactor n * (n : Real) ^ (4 / 5 : Real)
  have hAll : ∀ n, motive n := by
    apply Nat.recOnPosPrimePosCoprime
    · intro p alpha hp hAlpha hn b hb
      letI : NeZero p := ⟨hp.ne_zero⟩
      simpa [chenTwoFactor, primeFactors_primePow hp hAlpha] using
        chen_two_primePower hp hAlpha b hb
    · intro hn
      exact (hn rfl).elim
    · intro _hn b _hb
      have hBound := @norm_completePowerSum_le 1 ⟨one_ne_zero⟩ 5 b
      simpa [chenTwoFactor, Nat.primeFactors_one] using hBound
    · intro m n hmOne hnOne hcoprime hmInd hnInd hmn b hb
      have hm : m ≠ 0 := by omega
      have hn : n ≠ 0 := by omega
      letI : NeZero m := ⟨hm⟩
      letI : NeZero n := ⟨hn⟩
      let leftCoefficient : ZMod m :=
        (n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime b).1
      let rightCoefficient : ZMod n :=
        (m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime b).2
      have hUnits := normalizedCrtCoefficients_isUnit hcoprime hb
      have hLeft := hmInd hm leftCoefficient hUnits.1
      have hRight := hnInd hn rightCoefficient hUnits.2
      rw [completePowerSum_mul_standard hcoprime, norm_mul]
      change ‖completePowerSum 5 leftCoefficient‖ *
          ‖completePowerSum 5 rightCoefficient‖ ≤ _
      calc
        ‖completePowerSum 5 leftCoefficient‖ *
            ‖completePowerSum 5 rightCoefficient‖ ≤
            (chenTwoFactor m * (m : Real) ^ (4 / 5 : Real)) *
              (chenTwoFactor n * (n : Real) ^ (4 / 5 : Real)) :=
          mul_le_mul hLeft hRight (norm_nonneg _)
            ((norm_nonneg _).trans hLeft)
        _ = (chenTwoFactor m * chenTwoFactor n) *
            ((m : Real) * n) ^ (4 / 5 : Real) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          ring
        _ = chenTwoFactor (m * n) *
            ((m * n : Nat) : Real) ^ (4 / 5 : Real) := by
          rw [chenTwoFactor_mul hm hn hcoprime]
          norm_num [Nat.cast_mul]
  exact hAll q (NeZero.ne q) a ha

/-- The six small exceptional primes in Chen's local estimate. -/
def chenTwoExceptionalPrimes : Finset Nat := {11, 31, 41, 61, 71, 101}

/-- All primes that can contribute a nontrivial local constant. -/
def chenTwoSpecialPrimes : Finset Nat :=
  insert 5 chenTwoExceptionalPrimes

/-- Kernel-checked classification of primes below 102 that are one modulo
five. -/
lemma chenTwoExceptionalPrimeTable :
    ∀ p : Fin 102, p.val.Prime → 5 ∣ p.val - 1 →
      p.val ∈ chenTwoExceptionalPrimes := by
  decide

/-- A prime outside the fixed seven-prime set has local factor one. -/
lemma chenTwoPrimeFactor_eq_one_of_not_mem {p : Nat} (hp : p.Prime)
    (hmem : p ∉ chenTwoSpecialPrimes) :
    chenTwoPrimeFactor p = 1 := by
  rw [chenTwoPrimeFactor]
  split_ifs with hpFive hExceptional
  · apply (hmem _).elim
    simp [chenTwoSpecialPrimes, hpFive]
  · have hpUpper : p ≤ 101 :=
      exceptional_prime_le_hundredOne hp hExceptional.1 hExceptional.2
    have hpFin : p < 102 := by omega
    have hpExceptional :=
      chenTwoExceptionalPrimeTable ⟨p, hpFin⟩ hp hExceptional.1
    apply (hmem _).elim
    simp [chenTwoSpecialPrimes, hpExceptional]
  · rfl

/-- Every local factor is nonnegative. -/
lemma chenTwoPrimeFactor_nonneg (p : Nat) : 0 ≤ chenTwoPrimeFactor p := by
  rw [chenTwoPrimeFactor]
  split_ifs <;> positivity

/-- The small exceptional local factor is at least one. -/
lemma one_le_small_exceptional_factor {p : Nat} (hpPos : 0 < p)
    (hpUpper : p ≤ 101) :
    (1 : Real) ≤ 4 * (p : Real) ^ (-3 / 10 : Real) := by
  have hRoot := prime_rpow_three_tenths_lt_four hpUpper
  have hRootPos : 0 < (p : Real) ^ (3 / 10 : Real) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hpPos) _
  rw [show (-3 / 10 : Real) = -(3 / 10) by ring,
    Real.rpow_neg (by positivity : (0 : Real) ≤ p)]
  rw [le_mul_inv_iff₀ hRootPos]
  simpa using hRoot.le

/-- Every factor in the fixed seven-prime set is at least one. -/
lemma one_le_chenTwoPrimeFactor_of_mem_special {p : Nat}
    (hp : p ∈ chenTwoSpecialPrimes) :
    (1 : Real) ≤ chenTwoPrimeFactor p := by
  simp only [chenTwoSpecialPrimes, chenTwoExceptionalPrimes,
    Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [chenTwoPrimeFactor]
  · simpa [chenTwoPrimeFactor] using
      (one_le_small_exceptional_factor (p := 11) (by norm_num) (by norm_num))
  · simpa [chenTwoPrimeFactor] using
      (one_le_small_exceptional_factor (p := 31) (by norm_num) (by norm_num))
  · simpa [chenTwoPrimeFactor] using
      (one_le_small_exceptional_factor (p := 41) (by norm_num) (by norm_num))
  · simpa [chenTwoPrimeFactor] using
      (one_le_small_exceptional_factor (p := 61) (by norm_num) (by norm_num))
  · simpa [chenTwoPrimeFactor] using
      (one_le_small_exceptional_factor (p := 71) (by norm_num) (by norm_num))
  · simpa [chenTwoPrimeFactor] using
      (one_le_small_exceptional_factor (p := 101) (by norm_num) (by norm_num))

/-- Factors outside the special set can be removed from the prime-factor
product. -/
lemma chenTwoFactor_eq_filter_special (q : Nat) :
    chenTwoFactor q =
      ∏ p ∈ q.primeFactors.filter (· ∈ chenTwoSpecialPrimes),
        chenTwoPrimeFactor p := by
  rw [chenTwoFactor]
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro p hpPrime hpFilter
  apply chenTwoPrimeFactor_eq_one_of_not_mem
  · exact Nat.prime_of_mem_primeFactors hpPrime
  · simpa only [Finset.mem_filter, hpPrime, true_and] using hpFilter

/-- The factor for any modulus is bounded by the product over the full fixed
special-prime set. -/
lemma chenTwoFactor_le_specialProduct (q : Nat) :
    chenTwoFactor q ≤
      ∏ p ∈ chenTwoSpecialPrimes, chenTwoPrimeFactor p := by
  rw [chenTwoFactor_eq_filter_special]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p _
    exact chenTwoPrimeFactor_nonneg p
  · intro p hp _
    exact one_le_chenTwoPrimeFactor_of_mem_special hp

/-- On the exceptional set, the local factor has its nontrivial formula. -/
lemma chenTwoPrimeFactor_eq_of_mem_exceptional {p : Nat}
    (hp : p ∈ chenTwoExceptionalPrimes) :
    chenTwoPrimeFactor p = 4 * (p : Real) ^ (-3 / 10 : Real) := by
  simp only [chenTwoExceptionalPrimes, Finset.mem_insert,
    Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [chenTwoPrimeFactor]

/-- Product algebra for a finite collection of the exceptional local factors. -/
lemma prod_four_mul_rpow_neg_three_tenths (s : Finset Nat) :
    (∏ p ∈ s, 4 * (p : Real) ^ (-3 / 10 : Real)) =
      4 ^ s.card /
        ((∏ p ∈ s, (p : Real)) ^ (3 / 10 : Real)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Real.finsetProd_rpow s (fun p : Nat => (p : Real))
    (fun _ _ => by positivity) (-3 / 10 : Real)]
  rw [show (-3 / 10 : Real) = -(3 / 10) by ring,
    Real.rpow_neg (Finset.prod_nonneg fun _ _ => by positivity)]
  rfl

/-- The full special-prime product is Chen's explicit numerical factor. -/
lemma chenTwoSpecialProduct_eq :
    (∏ p ∈ chenTwoSpecialPrimes, chenTwoPrimeFactor p) =
      (5 : Real) * 4 ^ 6 /
        ((11 * 31 * 41 * 61 * 71 * 101 : Real) ^ (3 / 10 : Real)) := by
  rw [chenTwoSpecialPrimes, Finset.prod_insert (by decide)]
  have hExceptional :
      (∏ p ∈ chenTwoExceptionalPrimes, chenTwoPrimeFactor p) =
        ∏ p ∈ chenTwoExceptionalPrimes,
          4 * (p : Real) ^ (-3 / 10 : Real) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact chenTwoPrimeFactor_eq_of_mem_exceptional hp
  rw [hExceptional,
    prod_four_mul_rpow_neg_three_tenths chenTwoExceptionalPrimes]
  norm_num [chenTwoPrimeFactor, chenTwoExceptionalPrimes]
  ring

/-- Chen's global complete fifth-power-sum estimate. -/
theorem chen_two_completePowerSum_bound {q : Nat} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    ‖completePowerSum 5 a‖ ≤ 40 * (q : Real) ^ (4 / 5 : Real) := by
  have hFactor := norm_completePowerSum_le_chenTwoFactor a ha
  have hSpecial := chenTwoFactor_le_specialProduct q
  have hqPos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hPowerPos : 0 < (q : Real) ^ (4 / 5 : Real) := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast hqPos) _
  calc
    ‖completePowerSum 5 a‖ ≤
        chenTwoFactor q * (q : Real) ^ (4 / 5 : Real) := hFactor
    _ ≤ (∏ p ∈ chenTwoSpecialPrimes, chenTwoPrimeFactor p) *
        (q : Real) ^ (4 / 5 : Real) :=
      mul_le_mul_of_nonneg_right hSpecial (Real.rpow_nonneg (by positivity) _)
    _ ≤ 40 * (q : Real) ^ (4 / 5 : Real) := by
      apply le_of_lt
      rw [chenTwoSpecialProduct_eq]
      exact mul_lt_mul_of_pos_right chen_two_exceptional_factor_lt hPowerPos

end Waring.Analytic
