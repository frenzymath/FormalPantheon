import PrimesRestrictedDigits.PrimeNumberTheorem.DecimalSmooth
import PrimesRestrictedDigits.PrimeNumberTheorem.PrimitiveEulerFactors

/-!
# Uniform bounds for decimal primitive Euler factors

This file proves the fixed-prime estimates. They are uniform in every decimal-smooth level and
every complex character.
-/

namespace PrimesRestrictedDigits

open DirichletCharacter

/-- Prime factors of a decimal-smooth number are among two and five. -/
theorem IsDecimalSmooth.primeFactors_subset {q : Nat}
    (hq : IsDecimalSmooth q) : q.primeFactors ⊆ {2, 5} :=
  Nat.primeFactors_subset_of_mem_factoredNumbers hq

/-- A decimal-smooth number has at most two distinct prime factors. -/
theorem IsDecimalSmooth.card_primeFactors_le_two {q : Nat}
    (hq : IsDecimalSmooth q) : q.primeFactors.card ≤ 2 := by
  have hcard := Finset.card_le_card hq.primeFactors_subset
  simpa using hcard

/-- On `Re(s) >= 1/2`, every prime-power term from a prime is bounded by the
convenient rational constant `3/4`. -/
theorem norm_prime_cpow_le_three_four {p : Nat} (hp : p.Prime)
    {s : Complex} (hs : (1 : Real) / 2 ≤ s.re) :
    ‖(p : Complex) ^ (-s)‖ ≤ (3 : Real) / 4 := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos]
  have hp2 : (2 : Real) ≤ p := by
    exact_mod_cast hp.two_le
  have hsqrt : (4 : Real) / 3 ≤ √2 := by
    have hsquare := Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num)
    have hsqrt0 := Real.sqrt_nonneg (2 : Real)
    nlinarith
  calc
    (p : Real) ^ (-s).re ≤ (p : Real) ^ (-(1 / 2 : Real)) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast hp.one_le
      · simp only [Complex.neg_re]
        linarith
    _ ≤ (2 : Real) ^ (-(1 / 2 : Real)) := by
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    _ = (√2)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    _ ≤ ((4 : Real) / 3)⁻¹ :=
      (inv_le_inv₀ (Real.sqrt_pos.2 (by norm_num)) (by norm_num)).2 hsqrt
    _ = (3 : Real) / 4 := by norm_num

/-- Each local correction factor has norm at most two on the closed
half-plane `Re(s) >= 1/2`. -/
theorem norm_primitiveEulerFactor_le_two {d p : Nat}
    (chi : DirichletCharacter Complex d) (hp : p.Prime)
    {s : Complex} (hs : (1 : Real) / 2 ≤ s.re) :
    ‖primitiveEulerFactor chi p s‖ ≤ 2 := by
  have hpow := norm_prime_cpow_le_three_four hp hs
  rw [primitiveEulerFactor]
  calc
    ‖1 - chi p * (p : Complex) ^ (-s)‖ ≤
        ‖(1 : Complex)‖ + ‖chi p * (p : Complex) ^ (-s)‖ :=
      norm_sub_le _ _
    _ = 1 + ‖chi p‖ * ‖(p : Complex) ^ (-s)‖ := by
      rw [norm_one, norm_mul]
    _ ≤ 1 + 1 * ((3 : Real) / 4) := by
      gcongr
      exact chi.norm_le_one p
    _ ≤ 2 := by norm_num

/-- Each local correction factor stays at least one fourth away from zero on
the closed half-plane `Re(s) >= 1/2`. -/
theorem one_fourth_le_norm_primitiveEulerFactor {d p : Nat}
    (chi : DirichletCharacter Complex d) (hp : p.Prime)
    {s : Complex} (hs : (1 : Real) / 2 ≤ s.re) :
    (1 : Real) / 4 ≤ ‖primitiveEulerFactor chi p s‖ := by
  have hpow := norm_prime_cpow_le_three_four hp hs
  have hmul : ‖chi p * (p : Complex) ^ (-s)‖ ≤ (3 : Real) / 4 := by
    rw [norm_mul]
    calc
      ‖chi p‖ * ‖(p : Complex) ^ (-s)‖ ≤
          1 * ‖(p : Complex) ^ (-s)‖ := by
        gcongr
        exact chi.norm_le_one p
      _ ≤ (3 : Real) / 4 := by simpa only [one_mul] using hpow
  rw [primitiveEulerFactor]
  calc
    (1 : Real) / 4 ≤ 1 - ‖chi p * (p : Complex) ^ (-s)‖ := by
      linarith
    _ = ‖(1 : Complex)‖ - ‖chi p * (p : Complex) ^ (-s)‖ := by
      rw [norm_one]
    _ ≤ ‖(1 : Complex) - chi p * (p : Complex) ^ (-s)‖ :=
      norm_sub_norm_le _ _

/-- The full correction has a uniform lower norm bound independent of the
exponents of two and five in the level. -/
theorem one_sixteenth_le_norm_primitiveEulerCorrection {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : IsDecimalSmooth q)
    {s : Complex} (hs : (1 : Real) / 2 ≤ s.re) :
    (1 : Real) / 16 ≤ ‖primitiveEulerCorrection chi s‖ := by
  have hcard := hq.card_primeFactors_le_two
  rw [primitiveEulerCorrection, norm_prod]
  calc
    (1 : Real) / 16 = ((1 : Real) / 4) ^ 2 := by norm_num
    _ ≤ ((1 : Real) / 4) ^ q.primeFactors.card :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
    _ = ∏ _p ∈ q.primeFactors, ((1 : Real) / 4) := by
      rw [Finset.prod_const]
    _ ≤ ∏ p ∈ q.primeFactors,
        ‖primitiveEulerFactor chi.primitiveCharacter p s‖ := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        exact one_fourth_le_norm_primitiveEulerFactor chi.primitiveCharacter
          (Nat.prime_of_mem_primeFactors hp) hs

/-- The full correction has a uniform upper norm bound independent of the
exponents of two and five in the level. -/
theorem norm_primitiveEulerCorrection_le_four {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : IsDecimalSmooth q)
    {s : Complex} (hs : (1 : Real) / 2 ≤ s.re) :
    ‖primitiveEulerCorrection chi s‖ ≤ 4 := by
  have hcard := hq.card_primeFactors_le_two
  rw [primitiveEulerCorrection, norm_prod]
  calc
    (∏ p ∈ q.primeFactors,
        ‖primitiveEulerFactor chi.primitiveCharacter p s‖) ≤
        ∏ _p ∈ q.primeFactors, (2 : Real) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        exact norm_primitiveEulerFactor_le_two chi.primitiveCharacter
          (Nat.prime_of_mem_primeFactors hp) hs
    _ = (2 : Real) ^ q.primeFactors.card := by rw [Finset.prod_const]
    _ ≤ (2 : Real) ^ 2 := pow_le_pow_right₀ (by norm_num) hcard
    _ = 4 := by norm_num

/-- One logarithmic-derivative correction term is bounded uniformly for the
two decimal primes. -/
theorem norm_primitiveEulerLogDerivTerm_le_four_log_five
    {d p : Nat} (chi : DirichletCharacter Complex d) (hp : p.Prime)
    (hp5 : p ≤ 5) {s : Complex} (hs : (1 : Real) / 2 ≤ s.re) :
    ‖chi p * Complex.log p * (p : Complex) ^ (-s) /
        primitiveEulerFactor chi p s‖ ≤ 4 * Real.log 5 := by
  have hpow34 := norm_prime_cpow_le_three_four hp hs
  have hpow : ‖(p : Complex) ^ (-s)‖ ≤ 1 :=
    hpow34.trans (by norm_num)
  have hlog : ‖Complex.log (p : Complex)‖ = Real.log p := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg p)]
  have hlog5 : Real.log p ≤ Real.log 5 :=
    Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hp5)
  have hnum :
      ‖chi p * Complex.log p * (p : Complex) ^ (-s)‖ ≤ Real.log 5 := by
    rw [norm_mul, norm_mul, hlog]
    calc
      ‖chi p‖ * Real.log p * ‖(p : Complex) ^ (-s)‖ ≤
          1 * Real.log 5 * 1 := by
        gcongr
        exact chi.norm_le_one p
      _ = Real.log 5 := by ring
  have hden : (1 : Real) / 4 ≤ ‖primitiveEulerFactor chi p s‖ :=
    one_fourth_le_norm_primitiveEulerFactor chi hp hs
  rw [norm_div]
  calc
    ‖chi p * Complex.log p * (p : Complex) ^ (-s)‖ /
        ‖primitiveEulerFactor chi p s‖ ≤
        Real.log 5 / ((1 : Real) / 4) :=
      div_le_div₀ (Real.log_nonneg (by norm_num)) hnum (by norm_num) hden
    _ = 4 * Real.log 5 := by ring

/-- The logarithmic derivative of the correction is bounded by one fixed
constant on `Re(s) >= 1/2`. -/
theorem norm_primitiveEulerLogDerivCorrection_le {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : IsDecimalSmooth q)
    {s : Complex} (hs : (1 : Real) / 2 ≤ s.re) :
    ‖primitiveEulerLogDerivCorrection chi s‖ ≤ 8 * Real.log 5 := by
  have hcard := hq.card_primeFactors_le_two
  rw [primitiveEulerLogDerivCorrection]
  calc
    ‖∑ p ∈ q.primeFactors,
        chi.primitiveCharacter p * Complex.log p * (p : Complex) ^ (-s) /
          primitiveEulerFactor chi.primitiveCharacter p s‖ ≤
        ∑ p ∈ q.primeFactors,
          ‖chi.primitiveCharacter p * Complex.log p *
            (p : Complex) ^ (-s) /
              primitiveEulerFactor chi.primitiveCharacter p s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ q.primeFactors, 4 * Real.log 5 := by
      apply Finset.sum_le_sum
      intro p hp
      have hp5 : p ≤ 5 := by
        have hmem := hq.primeFactors_subset hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        omega
      exact norm_primitiveEulerLogDerivTerm_le_four_log_five
        chi.primitiveCharacter (Nat.prime_of_mem_primeFactors hp) hp5 hs
    _ = q.primeFactors.card * (4 * Real.log 5) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (4 * Real.log 5) := by
      gcongr
      exact_mod_cast hcard
    _ = 8 * Real.log 5 := by ring

/-- The imprimitive L-value cannot be much smaller than its primitive
counterpart on the fixed half-plane. -/
theorem norm_LFunction_primitive_div_sixteen_le {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) [NeZero chi.conductor]
    (hq : IsDecimalSmooth q) {s : Complex}
    (hs : (1 : Real) / 2 ≤ s.re)
    (hregular : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1) :
    ‖chi.primitiveCharacter.LFunction s‖ / 16 ≤ ‖chi.LFunction s‖ := by
  rw [LFunction_eq_primitive_mul_eulerCorrection chi hregular, norm_mul]
  have hE := one_sixteenth_le_norm_primitiveEulerCorrection chi hq hs
  nlinarith [norm_nonneg (chi.primitiveCharacter.LFunction s)]

/-- The imprimitive L-value cannot be much larger than its primitive
counterpart on the fixed half-plane. -/
theorem norm_LFunction_le_four_mul_primitive {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) [NeZero chi.conductor]
    (hq : IsDecimalSmooth q) {s : Complex}
    (hs : (1 : Real) / 2 ≤ s.re)
    (hregular : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1) :
    ‖chi.LFunction s‖ ≤ 4 * ‖chi.primitiveCharacter.LFunction s‖ := by
  rw [LFunction_eq_primitive_mul_eulerCorrection chi hregular, norm_mul]
  have hE := norm_primitiveEulerCorrection_le_four chi hq hs
  nlinarith [norm_nonneg (chi.primitiveCharacter.LFunction s)]

/-- Primitive and imprimitive logarithmic derivatives differ by a fixed
amount on the half-plane, away from primitive zeros and the principal pole. -/
theorem norm_logDeriv_LFunction_sub_primitive_le {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) [NeZero chi.conductor]
    (hq : IsDecimalSmooth q) {s : Complex}
    (hs : (1 : Real) / 2 ≤ s.re)
    (hregular : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1)
    (hL : chi.primitiveCharacter.LFunction s ≠ 0) :
    ‖logDeriv chi.LFunction s -
        logDeriv chi.primitiveCharacter.LFunction s‖ ≤
      8 * Real.log 5 := by
  have hs0 : 0 < s.re := lt_of_lt_of_le (by norm_num) hs
  rw [logDeriv_LFunction_eq_primitive_add chi hs0 hregular hL,
    add_sub_cancel_left]
  exact norm_primitiveEulerLogDerivCorrection_le chi hq hs

end PrimesRestrictedDigits
