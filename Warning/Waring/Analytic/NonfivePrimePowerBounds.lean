import Waring.Analytic.PrimeGauss

/-!
# Bounds for non-five prime-power fifth-power sums

This file completes the local prime-power estimates in Chen's Lemma 2 away
from the prime five [CHEN1964-EN, pp. 1547-1548; CHEN1964-ZH, pp. 715-716].
-/

namespace Waring.Analytic

/-- Since five is prime, a gcd with five that is not five must be one. -/
lemma coprime_five_of_gcd_ne_five {n : Nat} (h : n.gcd 5 ≠ 5) :
    n.Coprime 5 := by
  have hd : n.gcd 5 ∣ 5 := Nat.gcd_dvd_right n 5
  rw [Nat.dvd_prime Nat.prime_five] at hd
  rcases hd with hOne | hFive
  · exact hOne
  · exact (h hFive).elim

/-- Prime-power form of the exact five-step stationary-phase recurrence. -/
lemma completePowerSum_fifth_primePow_add_five (p beta a : Nat) [NeZero p]
    (hp : p.Prime) (hpFive : p ≠ 5) (ha : a.Coprime p) :
    completePowerSum 5 ((a : Nat) : ZMod (p ^ (beta + 5))) =
      (p ^ 4 : Nat) *
        completePowerSum 5 ((a : Nat) : ZMod (p ^ beta)) := by
  calc
    _ = completePowerSum 5
        ((a : Nat) : ZMod (p ^ 5 * p ^ beta)) := by
      apply completePowerSum_natCast_modulus_congr
      ring
    _ = _ := completePowerSum_fifth_prime_recurrence
      p (p ^ beta) hp hpFive a ha

/-- The exact initial values for exponents two through five satisfy the
generic `p^(4*alpha/5)` estimate. -/
lemma prime_pow_pred_le_rpow_four_fifths {p alpha : Nat} (hp : p.Prime)
    (hAlpha : alpha ≤ 5) :
    ((p ^ (alpha - 1) : Nat) : Real) ≤
      (p : Real) ^ (((4 * alpha : Nat) : Real) / 5) := by
  have hNat : 5 * (alpha - 1) ≤ 4 * alpha := by omega
  have hNatReal :
      ((5 * (alpha - 1) : Nat) : Real) ≤ ((4 * alpha : Nat) : Real) := by
    exact_mod_cast hNat
  have hExponent :
      ((alpha - 1 : Nat) : Real) ≤ (((4 * alpha : Nat) : Real) / 5) := by
    push_cast at hNatReal ⊢
    linarith
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hp.one_le) hExponent

/-- The real target bound has the same five-step scaling as the complete sum. -/
lemma prime_rpow_four_fifths_add_five (p alpha : Nat) (hp : p.Prime) :
    ((p ^ 4 : Nat) : Real) *
        (p : Real) ^ (((4 * alpha : Nat) : Real) / 5) =
      (p : Real) ^ (((4 * (alpha + 5) : Nat) : Real) / 5) := by
  have hExponent :
      (((4 * (alpha + 5) : Nat) : Real) / 5) =
        (((4 * alpha : Nat) : Real) / 5) + 4 := by
    push_cast
    ring
  rw [Nat.cast_pow, hExponent,
    Real.rpow_add (by exact_mod_cast hp.pos)]
  norm_num [Real.rpow_natCast]
  ring

/-- Chen's generic non-five prime-power estimate. The gcd hypothesis makes
the prime-modulus sum vanish; exact initial values and the five-step recurrence
handle every higher exponent. -/
theorem chen_two_generic_primePower {p alpha : Nat} [NeZero p]
    (hp : p.Prime) (hAlpha : 0 < alpha) (hpFive : p ≠ 5)
    (hFifth : (p - 1).gcd 5 ≠ 5) (a : Nat) (ha : a.Coprime p) :
    ‖completePowerSum 5 ((a : Nat) : ZMod (p ^ alpha))‖ ≤
      (p : Real) ^ (((4 * alpha : Nat) : Real) / 5) := by
  revert hAlpha
  refine Nat.strong_induction_on alpha ?_
  intro alpha ih hAlpha
  by_cases hOne : alpha = 1
  · subst alpha
    have hZero :
        completePowerSum 5 ((a : Nat) : ZMod (p ^ 1)) = 0 := by
      calc
        _ = completePowerSum 5 ((a : Nat) : ZMod p) := by
          apply completePowerSum_natCast_modulus_congr
          ring
        _ = 0 := completePowerSum_fifth_prime_eq_zero hp
          (coprime_five_of_gcd_ne_five hFifth) ha
    rw [hZero, norm_zero]
    exact Real.rpow_nonneg (by positivity) _
  by_cases hInitial : alpha ≤ 5
  · have hLower : 1 < alpha := by omega
    rw [completePowerSum_fifth_primePow_small hp hpFive hLower hInitial a ha,
      Complex.norm_natCast]
    exact prime_pow_pred_le_rpow_four_fifths hp hInitial
  · let beta := alpha - 5
    have hBetaLt : beta < alpha := by omega
    have hBetaPos : 0 < beta := by omega
    have hAlphaEq : alpha = beta + 5 := by omega
    have hInduction := ih beta hBetaLt hBetaPos
    rw [hAlphaEq, completePowerSum_fifth_primePow_add_five p beta a hp hpFive ha,
      norm_mul, Complex.norm_natCast]
    calc
      ((p ^ 4 : Nat) : Real) *
          ‖completePowerSum 5 ((a : Nat) : ZMod (p ^ beta))‖ ≤
          ((p ^ 4 : Nat) : Real) *
            (p : Real) ^ (((4 * beta : Nat) : Real) / 5) :=
        mul_le_mul_of_nonneg_left hInduction (by positivity)
      _ = (p : Real) ^ (((4 * (beta + 5) : Nat) : Real) / 5) :=
        prime_rpow_four_fifths_add_five p beta hp

/-- A prime at most 128 that is one modulo five is in fact at most 101. -/
lemma exceptional_prime_le_hundredOne {p : Nat} (hp : p.Prime)
    (hFive : 5 ∣ p - 1) (hpUpper : p ≤ 128) : p ≤ 101 := by
  by_contra h
  have hpLower : 102 ≤ p := by omega
  interval_cases p <;> norm_num at hFive
  case «106» =>
    have hd := (Nat.prime_def.mp hp).2 2 (by norm_num)
    omega
  case «111» =>
    have hd := (Nat.prime_def.mp hp).2 3 (by norm_num)
    omega
  case «116» =>
    have hd := (Nat.prime_def.mp hp).2 2 (by norm_num)
    omega
  case «121» =>
    have hd := (Nat.prime_def.mp hp).2 11 (by norm_num)
    omega
  case «126» =>
    have hd := (Nat.prime_def.mp hp).2 2 (by norm_num)
    omega

/-- The closed tenth-power certificate needed for the fourth and fifth
exceptional initial exponents. -/
lemma prime_rpow_three_tenths_lt_four {p : Nat} (hpUpper : p ≤ 101) :
    (p : Real) ^ (3 / 10 : Real) < 4 := by
  apply lt_of_pow_lt_pow_left₀ 10 (by norm_num : (0 : Real) ≤ 4)
  rw [← Real.rpow_mul_natCast (by positivity : (0 : Real) ≤ p)]
  norm_num [Real.rpow_natCast]
  have hpReal : (p : Real) ≤ 101 := by exact_mod_cast hpUpper
  have hpCube : (p : Real) ^ 3 ≤ (101 : Real) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hpReal 3
  norm_num at hpCube ⊢
  linarith

/-- The exact initial values at exponents two through five satisfy Chen's
exceptional-prime estimate. -/
lemma exceptional_prime_pow_pred_le_bound {p alpha : Nat} (hp : p.Prime)
    (hpUpper : p ≤ 101) (hAlpha : 1 < alpha) (hAlphaUpper : alpha ≤ 5) :
    ((p ^ (alpha - 1) : Nat) : Real) ≤
      4 * (p : Real) ^ (-3 / 10 : Real) *
        (p : Real) ^ (((4 * alpha : Nat) : Real) / 5) := by
  have hpOne : (1 : Real) ≤ p := by exact_mod_cast hp.one_le
  have hRootThree : (p : Real) ^ (3 / 10 : Real) < 4 :=
    prime_rpow_three_tenths_lt_four hpUpper
  have hRootOne : (p : Real) ^ (1 / 10 : Real) ≤ 4 := by
    exact (Real.rpow_le_rpow_of_exponent_le hpOne (by norm_num)).trans
      hRootThree.le
  interval_cases alpha
  · norm_num [Nat.cast_pow, Real.rpow_natCast]
    have hpow :
        (p : Real) ^ (1 : Real) ≤ (p : Real) ^ (13 / 10 : Real) :=
      Real.rpow_le_rpow_of_exponent_le hpOne (by norm_num)
    have hcombine :
        (p : Real) ^ (-(3 / 10) : Real) *
            (p : Real) ^ (8 / 5 : Real) =
          (p : Real) ^ (13 / 10 : Real) := by
      rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
      congr 1
      norm_num
    calc
      (p : Real) ≤ (p : Real) ^ (13 / 10 : Real) := by simpa using hpow
      _ ≤ 4 * (p : Real) ^ (13 / 10 : Real) :=
        le_mul_of_one_le_left (Real.rpow_nonneg (by positivity) _) (by norm_num)
      _ = 4 * ((p : Real) ^ (-(3 / 10) : Real) *
          (p : Real) ^ (8 / 5 : Real)) := by rw [hcombine]
      _ = 4 * (p : Real) ^ (-(3 / 10) : Real) *
          (p : Real) ^ (8 / 5 : Real) := by ring
  · norm_num [Nat.cast_pow, Real.rpow_natCast]
    have hpow :
        (p : Real) ^ (2 : Real) ≤ (p : Real) ^ (21 / 10 : Real) :=
      Real.rpow_le_rpow_of_exponent_le hpOne (by norm_num)
    have hcombine :
        (p : Real) ^ (-(3 / 10) : Real) *
            (p : Real) ^ (12 / 5 : Real) =
          (p : Real) ^ (21 / 10 : Real) := by
      rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
      congr 1
      norm_num
    calc
      (p : Real) ^ (2 : Nat) = (p : Real) ^ (2 : Real) := by
        norm_num [Real.rpow_natCast]
      _ ≤ (p : Real) ^ (21 / 10 : Real) := hpow
      _ ≤ 4 * (p : Real) ^ (21 / 10 : Real) :=
        le_mul_of_one_le_left (Real.rpow_nonneg (by positivity) _) (by norm_num)
      _ = 4 * ((p : Real) ^ (-(3 / 10) : Real) *
          (p : Real) ^ (12 / 5 : Real)) := by rw [hcombine]
      _ = 4 * (p : Real) ^ (-(3 / 10) : Real) *
          (p : Real) ^ (12 / 5 : Real) := by ring
  · norm_num [Nat.cast_pow, Real.rpow_natCast]
    have hcombineOne :
        (p : Real) ^ (1 / 10 : Real) *
            (p : Real) ^ (29 / 10 : Real) =
          (p : Real) ^ (3 : Real) := by
      rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
      congr 1
      norm_num
    have hcombineTarget :
        (p : Real) ^ (-(3 / 10) : Real) *
            (p : Real) ^ (16 / 5 : Real) =
          (p : Real) ^ (29 / 10 : Real) := by
      rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
      congr 1
      norm_num
    calc
      (p : Real) ^ (3 : Nat) = (p : Real) ^ (3 : Real) := by
        norm_num [Real.rpow_natCast]
      _ = (p : Real) ^ (1 / 10 : Real) *
          (p : Real) ^ (29 / 10 : Real) := hcombineOne.symm
      _ ≤ 4 * (p : Real) ^ (29 / 10 : Real) :=
        mul_le_mul_of_nonneg_right hRootOne (Real.rpow_nonneg (by positivity) _)
      _ = 4 * ((p : Real) ^ (-(3 / 10) : Real) *
          (p : Real) ^ (16 / 5 : Real)) := by rw [hcombineTarget]
      _ = 4 * (p : Real) ^ (-(3 / 10) : Real) *
          (p : Real) ^ (16 / 5 : Real) := by ring
  · norm_num [Nat.cast_pow, Real.rpow_natCast]
    have hcombineThree :
        (p : Real) ^ (3 / 10 : Real) *
            (p : Real) ^ (37 / 10 : Real) =
          (p : Real) ^ (4 : Real) := by
      rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
      congr 1
      norm_num
    have hcombineTarget :
        (p : Real) ^ (-(3 / 10) : Real) *
            (p : Real) ^ (4 : Real) =
          (p : Real) ^ (37 / 10 : Real) := by
      rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
      congr 1
      norm_num
    calc
      (p : Real) ^ (4 : Nat) = (p : Real) ^ (4 : Real) := by
        norm_num [Real.rpow_natCast]
      _ = (p : Real) ^ (3 / 10 : Real) *
          (p : Real) ^ (37 / 10 : Real) := hcombineThree.symm
      _ ≤ 4 * (p : Real) ^ (37 / 10 : Real) :=
        mul_le_mul_of_nonneg_right hRootThree.le
          (Real.rpow_nonneg (by positivity) _)
      _ = 4 * ((p : Real) ^ (-(3 / 10) : Real) *
          (p : Real) ^ (4 : Real)) := by rw [hcombineTarget]
      _ = 4 * (p : Real) ^ (-(3 / 10) : Real) *
          (p : Real) ^ (4 : Nat) := by
        rw [← Real.rpow_natCast (p : Real) 4]
        ring_nf

/-- The square-root prime bound is exactly the exponent-one instance of
Chen's exceptional-prime target. -/
lemma four_sqrt_eq_exceptional_prime_bound {p : Nat} (hp : p.Prime) :
    4 * Real.sqrt p =
      4 * (p : Real) ^ (-3 / 10 : Real) *
        (p : Real) ^ (4 / 5 : Real) := by
  rw [Real.sqrt_eq_rpow]
  have hcombine :
      (p : Real) ^ (-3 / 10 : Real) * (p : Real) ^ (4 / 5 : Real) =
        (p : Real) ^ (1 / 2 : Real) := by
    rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
    congr 1
    norm_num
  calc
    4 * (p : Real) ^ (1 / 2 : Real) =
        4 * ((p : Real) ^ (-3 / 10 : Real) *
          (p : Real) ^ (4 / 5 : Real)) := by rw [hcombine]
    _ = 4 * (p : Real) ^ (-3 / 10 : Real) *
        (p : Real) ^ (4 / 5 : Real) := by ring

/-- Chen's exceptional non-five prime-power estimate. -/
theorem chen_two_exceptional_primePower {p alpha : Nat} [NeZero p]
    (hp : p.Prime) (hAlpha : 0 < alpha) (hFive : 5 ∣ p - 1)
    (hpUpper : p ≤ 128) (a : Nat) (ha : a.Coprime p) :
    ‖completePowerSum 5 ((a : Nat) : ZMod (p ^ alpha))‖ ≤
      4 * (p : Real) ^ (-3 / 10 : Real) *
        (p : Real) ^ (((4 * alpha : Nat) : Real) / 5) := by
  have hpFive : p ≠ 5 := by
    intro hpEq
    subst p
    norm_num at hFive
  have hpHundredOne : p ≤ 101 :=
    exceptional_prime_le_hundredOne hp hFive hpUpper
  revert hAlpha
  refine Nat.strong_induction_on alpha ?_
  intro alpha ih hAlpha
  by_cases hOne : alpha = 1
  · subst alpha
    have hModulus :
        completePowerSum 5 ((a : Nat) : ZMod (p ^ 1)) =
          completePowerSum 5 ((a : Nat) : ZMod p) := by
      apply completePowerSum_natCast_modulus_congr
      ring
    rw [hModulus]
    calc
      ‖completePowerSum 5 ((a : Nat) : ZMod p)‖ ≤ 4 * Real.sqrt p :=
        completePowerSum_fifth_prime_le_four_sqrt hp hFive ha
      _ = 4 * (p : Real) ^ (-3 / 10 : Real) *
          (p : Real) ^ (4 / 5 : Real) :=
        four_sqrt_eq_exceptional_prime_bound hp
      _ = 4 * (p : Real) ^ (-3 / 10 : Real) *
          (p : Real) ^ (((4 * 1 : Nat) : Real) / 5) := by norm_num
  by_cases hInitial : alpha ≤ 5
  · have hLower : 1 < alpha := by omega
    rw [completePowerSum_fifth_primePow_small hp hpFive hLower hInitial a ha,
      Complex.norm_natCast]
    exact exceptional_prime_pow_pred_le_bound hp hpHundredOne hLower hInitial
  · let beta := alpha - 5
    have hBetaLt : beta < alpha := by omega
    have hBetaPos : 0 < beta := by omega
    have hAlphaEq : alpha = beta + 5 := by omega
    have hInduction := ih beta hBetaLt hBetaPos
    rw [hAlphaEq, completePowerSum_fifth_primePow_add_five p beta a hp hpFive ha,
      norm_mul, Complex.norm_natCast]
    calc
      ((p ^ 4 : Nat) : Real) *
          ‖completePowerSum 5 ((a : Nat) : ZMod (p ^ beta))‖ ≤
          ((p ^ 4 : Nat) : Real) *
            (4 * (p : Real) ^ (-3 / 10 : Real) *
              (p : Real) ^ (((4 * beta : Nat) : Real) / 5)) :=
        mul_le_mul_of_nonneg_left hInduction (by positivity)
      _ = 4 * (p : Real) ^ (-3 / 10 : Real) *
          (((p ^ 4 : Nat) : Real) *
            (p : Real) ^ (((4 * beta : Nat) : Real) / 5)) := by ring
      _ = 4 * (p : Real) ^ (-3 / 10 : Real) *
          (p : Real) ^ (((4 * (beta + 5) : Nat) : Real) / 5) := by
        rw [prime_rpow_four_fifths_add_five p beta hp]

/-- The numerical endpoint behind the unit constant for exceptional primes at
least 128. -/
lemma four_lt_oneTwentyEight_rpow_three_tenths :
    (4 : Real) < (128 : Real) ^ (3 / 10 : Real) := by
  apply lt_of_pow_lt_pow_left₀ 10 (Real.rpow_nonneg (by norm_num) _)
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 128)]
  norm_num [Real.rpow_natCast]

/-- Above 128, the coefficient four in the Gauss estimate is absorbed by
`p^(3/10)`. -/
lemma four_le_prime_rpow_three_tenths {p : Nat} (hpLower : 128 ≤ p) :
    (4 : Real) ≤ (p : Real) ^ (3 / 10 : Real) := by
  calc
    (4 : Real) ≤ (128 : Real) ^ (3 / 10 : Real) :=
      four_lt_oneTwentyEight_rpow_three_tenths.le
    _ ≤ (p : Real) ^ (3 / 10 : Real) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hpLower) (by norm_num)

/-- At a prime at least 128, the four-square-root estimate is at most the
unit-constant exponent-one target. -/
lemma four_sqrt_le_prime_rpow_four_fifths {p : Nat} (hp : p.Prime)
    (hpLower : 128 ≤ p) :
    4 * Real.sqrt p ≤ (p : Real) ^ (4 / 5 : Real) := by
  rw [Real.sqrt_eq_rpow]
  calc
    4 * (p : Real) ^ (1 / 2 : Real) ≤
        (p : Real) ^ (3 / 10 : Real) *
          (p : Real) ^ (1 / 2 : Real) :=
      mul_le_mul_of_nonneg_right (four_le_prime_rpow_three_tenths hpLower)
        (Real.rpow_nonneg (by positivity) _)
    _ = (p : Real) ^ (4 / 5 : Real) := by
      rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
      congr 1
      norm_num

/-- Chen's unit-constant estimate for the exceptional primes at least 128. -/
theorem chen_two_large_exceptional_primePower {p alpha : Nat} [NeZero p]
    (hp : p.Prime) (hAlpha : 0 < alpha) (hFive : 5 ∣ p - 1)
    (hpLower : 128 ≤ p) (a : Nat) (ha : a.Coprime p) :
    ‖completePowerSum 5 ((a : Nat) : ZMod (p ^ alpha))‖ ≤
      (p : Real) ^ (((4 * alpha : Nat) : Real) / 5) := by
  have hpFive : p ≠ 5 := by omega
  revert hAlpha
  refine Nat.strong_induction_on alpha ?_
  intro alpha ih hAlpha
  by_cases hOne : alpha = 1
  · subst alpha
    have hModulus :
        completePowerSum 5 ((a : Nat) : ZMod (p ^ 1)) =
          completePowerSum 5 ((a : Nat) : ZMod p) := by
      apply completePowerSum_natCast_modulus_congr
      ring
    rw [hModulus]
    calc
      ‖completePowerSum 5 ((a : Nat) : ZMod p)‖ ≤ 4 * Real.sqrt p :=
        completePowerSum_fifth_prime_le_four_sqrt hp hFive ha
      _ ≤ (p : Real) ^ (4 / 5 : Real) :=
        four_sqrt_le_prime_rpow_four_fifths hp hpLower
      _ = (p : Real) ^ (((4 * 1 : Nat) : Real) / 5) := by norm_num
  by_cases hInitial : alpha ≤ 5
  · have hLower : 1 < alpha := by omega
    rw [completePowerSum_fifth_primePow_small hp hpFive hLower hInitial a ha,
      Complex.norm_natCast]
    exact prime_pow_pred_le_rpow_four_fifths hp hInitial
  · let beta := alpha - 5
    have hBetaLt : beta < alpha := by omega
    have hBetaPos : 0 < beta := by omega
    have hAlphaEq : alpha = beta + 5 := by omega
    have hInduction := ih beta hBetaLt hBetaPos
    rw [hAlphaEq, completePowerSum_fifth_primePow_add_five p beta a hp hpFive ha,
      norm_mul, Complex.norm_natCast]
    calc
      ((p ^ 4 : Nat) : Real) *
          ‖completePowerSum 5 ((a : Nat) : ZMod (p ^ beta))‖ ≤
          ((p ^ 4 : Nat) : Real) *
            (p : Real) ^ (((4 * beta : Nat) : Real) / 5) :=
        mul_le_mul_of_nonneg_left hInduction (by positivity)
      _ = (p : Real) ^ (((4 * (beta + 5) : Nat) : Real) / 5) :=
        prime_rpow_four_fifths_add_five p beta hp

end Waring.Analytic
