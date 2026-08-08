import Waring.Analytic.FivePrimePower

/-!
# Complete fifth-power sums at prime powers away from five

This file proves the exact stationary-phase recurrence and the small-exponent
identities used in the non-five branches of Chen's Lemma 2
[CHEN1964-EN, pp. 1547-1548; CHEN1964-ZH, pp. 715-716].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The fifth-power binomial congruence used in one prime stationary-phase
block. -/
theorem fifthPower_add_primeScale (p s : Nat)
    (eta xi : ZMod (p * (p * s))) :
    (eta + (p * s : Nat) * xi) ^ 5 =
      eta ^ 5 + (5 * (p * s) : Nat) * eta ^ 4 * xi := by
  have hmod : (p * (p * s) : Nat) = (0 : ZMod (p * (p * s))) :=
    ZMod.natCast_self (p * (p * s))
  calc
    (eta + (p * s : Nat) * xi) ^ 5 =
        eta ^ 5 + (5 * (p * s) : Nat) * eta ^ 4 * xi +
          (p * (p * s) : Nat) *
            (10 * s * eta ^ 3 * xi ^ 2 +
              10 * p * s ^ 2 * eta ^ 2 * xi ^ 3 +
              5 * p ^ 2 * s ^ 3 * eta * xi ^ 4 +
              p ^ 3 * s ^ 4 * xi ^ 5) := by
      push_cast
      ring
    _ = eta ^ 5 + (5 * (p * s) : Nat) * eta ^ 4 * xi := by
      rw [hmod, zero_mul, add_zero]

/-- Reindex a complete sum modulo `p*(p*s)` into `p` stationary-phase
blocks. -/
theorem completePowerSum_fifth_prime_reindex (p s : Nat) [NeZero p] [NeZero s]
    (a : ZMod (p * (p * s))) :
    completePowerSum 5 a =
      ∑ eta : Fin (p * s), ∑ xi : Fin p,
        ZMod.stdAddChar
          (a * (((eta : Nat) : ZMod (p * (p * s))) ^ 5 +
            ((5 * (p * s) : Nat) : ZMod (p * (p * s))) *
              ((eta : Nat) : ZMod (p * (p * s))) ^ 4 *
              ((xi : Nat) : ZMod (p * (p * s))))) := by
  rw [completePowerSum, powerSum]
  rw [← (ZMod.finEquiv (p * (p * s))).toEquiv.sum_comp]
  rw [← (finProdFinEquiv : Fin p × Fin (p * s) ≃
    Fin (p * (p * s))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro eta _
  apply Finset.sum_congr rfl
  intro xi _
  rw [show
      (ZMod.finEquiv (p * (p * s))).toEquiv (finProdFinEquiv (xi, eta)) =
        ((eta : Nat) : ZMod (p * (p * s))) +
          (p * s : Nat) * ((xi : Nat) : ZMod (p * (p * s))) by
    change ZMod.finEquiv (p * (p * s)) (finProdFinEquiv (xi, eta)) = _
    rw [zmod_finEquiv_apply]
    change ((eta.val + (p * s) * xi.val : Nat) : ZMod (p * (p * s))) = _
    push_cast
    ring]
  rw [fifthPower_add_primeScale]

/-- The inner stationary-phase block is a complete additive-character sum
modulo `p`. -/
theorem fifth_prime_inner_sum (p s : Nat) [NeZero p] [NeZero s]
    (a eta : Nat) :
    ∑ xi : Fin p,
        ZMod.stdAddChar
          (((a : Nat) : ZMod (p * (p * s))) *
            ((5 * (p * s) : Nat) : ZMod (p * (p * s))) *
              ((eta : Nat) : ZMod (p * (p * s))) ^ 4 *
                ((xi : Nat) : ZMod (p * (p * s)))) =
      if ((5 * a * eta ^ 4 : Nat) : ZMod p) = 0 then p else 0 := by
  let c : ZMod p := (5 * a * eta ^ 4 : Nat)
  calc
    ∑ xi : Fin p,
        ZMod.stdAddChar
          (((a : Nat) : ZMod (p * (p * s))) *
            ((5 * (p * s) : Nat) : ZMod (p * (p * s))) *
              ((eta : Nat) : ZMod (p * (p * s))) ^ 4 *
                ((xi : Nat) : ZMod (p * (p * s)))) =
        ∑ xi : Fin p,
          ZMod.stdAddChar
            (zmodScale p (p * s) ((ZMod.finEquiv p).toEquiv xi * c)) := by
      apply Finset.sum_congr rfl
      intro xi _
      apply congrArg ZMod.stdAddChar
      rw [show (ZMod.finEquiv p).toEquiv xi = ((xi : Nat) : ZMod p) by
        change ZMod.finEquiv p xi = _
        exact zmod_finEquiv_apply xi]
      dsimp [c]
      rw [show ((xi : Nat) : ZMod p) *
          ((5 * a * eta ^ 4 : Nat) : ZMod p) =
          ((xi.val * (5 * a * eta ^ 4) : Nat) : ZMod p) by
        push_cast
        rfl]
      rw [show zmodScale p (p * s)
          ((xi.val * (5 * a * eta ^ 4) : Nat) : ZMod p) =
          ((p * s : Nat) : ZMod (p * (p * s))) *
            ((xi.val * (5 * a * eta ^ 4) : Nat) :
              ZMod (p * (p * s))) by
        simpa only [Int.cast_natCast] using
          zmodScale_intCast p (p * s)
            ((xi.val * (5 * a * eta ^ 4) : Nat) : Int)]
      push_cast
      ring
    _ = if c = 0 then p else 0 := by
      simpa using sum_fin_stdAddChar_zmodScale p (p * s) c
    _ = if ((5 * a * eta ^ 4 : Nat) : ZMod p) = 0 then p else 0 := rfl

/-- Away from five and under a unit-coefficient hypothesis, a stationary
block survives exactly at residues divisible by `p`. -/
theorem fifth_prime_coefficient_eq_zero_iff {p a eta : Nat}
    (hp : p.Prime) (hpFive : p ≠ 5) (ha : a.Coprime p) :
    ((5 * a * eta ^ 4 : Nat) : ZMod p) = 0 ↔ p ∣ eta := by
  rw [ZMod.natCast_eq_zero_iff]
  constructor
  · intro hdiv
    rcases hp.dvd_or_dvd hdiv with hFiveA | hetaPow
    · rcases hp.dvd_or_dvd hFiveA with hFive | haDiv
      · exact (hpFive ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hFive)).elim
      · exact (hp.coprime_iff_not_dvd.mp ha.symm haDiv).elim
    · exact hp.dvd_of_dvd_pow hetaPow
  · rintro ⟨k, rfl⟩
    refine ⟨5 * a * p ^ 3 * k ^ 4, ?_⟩
    ring

/-- One stationary-phase block leaves only the residue classes divisible by
`p`. -/
theorem completePowerSum_fifth_prime_survivors (p s : Nat) [NeZero p] [NeZero s]
    (hp : p.Prime) (hpFive : p ≠ 5) (a : Nat) (ha : a.Coprime p) :
    completePowerSum 5 ((a : Nat) : ZMod (p * (p * s))) =
      ∑ eta : Fin (p * s),
        (if p ∣ eta.val then
          (p : Complex) * ZMod.stdAddChar
            (((a : Nat) : ZMod (p * (p * s))) *
              ((eta.val : Nat) : ZMod (p * (p * s))) ^ 5)
        else 0) := by
  rw [completePowerSum_fifth_prime_reindex]
  apply Finset.sum_congr rfl
  intro eta _
  calc
    ∑ xi : Fin p,
        ZMod.stdAddChar
          (((a : Nat) : ZMod (p * (p * s))) *
            (((eta : Nat) : ZMod (p * (p * s))) ^ 5 +
              ((5 * (p * s) : Nat) : ZMod (p * (p * s))) *
                ((eta : Nat) : ZMod (p * (p * s))) ^ 4 *
                  ((xi : Nat) : ZMod (p * (p * s))))) =
        ZMod.stdAddChar
            (((a : Nat) : ZMod (p * (p * s))) *
              ((eta.val : Nat) : ZMod (p * (p * s))) ^ 5) *
          ∑ xi : Fin p,
            ZMod.stdAddChar
              (((a : Nat) : ZMod (p * (p * s))) *
                ((5 * (p * s) : Nat) : ZMod (p * (p * s))) *
                  ((eta.val : Nat) : ZMod (p * (p * s))) ^ 4 *
                    ((xi : Nat) : ZMod (p * (p * s)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xi _
      rw [mul_add, AddChar.map_add_eq_mul]
      ring_nf
    _ = ZMod.stdAddChar
          (((a : Nat) : ZMod (p * (p * s))) *
            ((eta.val : Nat) : ZMod (p * (p * s))) ^ 5) *
          (if ((5 * a * eta.val ^ 4 : Nat) : ZMod p) = 0 then p else 0) := by
      rw [fifth_prime_inner_sum]
    _ = if p ∣ eta.val then
          (p : Complex) * ZMod.stdAddChar
            (((a : Nat) : ZMod (p * (p * s))) *
              ((eta.val : Nat) : ZMod (p * (p * s))) ^ 5)
        else 0 := by
      rw [if_congr (fifth_prime_coefficient_eq_zero_iff hp hpFive ha) rfl rfl]
      split_ifs <;> simp_all [mul_comm]

/-- The zero-based decomposition `eta=p*k+r`. -/
def finPrimeBlocks (p s : Nat) : Fin s × Fin p ≃ Fin (p * s) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm s p))

@[simp] theorem finPrimeBlocks_val (p s : Nat) (x : Fin s × Fin p) :
    (finPrimeBlocks p s x).val = x.2.val + p * x.1.val := by
  rfl

/-- Exactly `s` indices in `Fin (p*s)` are divisible by the positive prime
`p`. -/
theorem sum_fin_prime_dvd (p s : Nat) (hp : p.Prime) :
    ∑ eta : Fin (p * s),
      (if p ∣ eta.val then (p : Complex) else 0) = p * s := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [← (finPrimeBlocks p s).sum_comp]
  rw [Fintype.sum_prod_type]
  calc
    ∑ k : Fin s, ∑ r : Fin p,
        (if p ∣ (finPrimeBlocks p s (k, r)).val then
          (p : Complex) else 0) =
        ∑ _k : Fin s, (p : Complex) := by
      apply Finset.sum_congr rfl
      intro k _
      have hdiv (r : Fin p) : p ∣ r.val + p * k.val ↔ r.val = 0 := by
        rw [Nat.dvd_iff_mod_eq_zero]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
      simp_rw [finPrimeBlocks_val, hdiv]
      simp
    _ = p * s := by simp [mul_comm]

/-- If `s` divides `p^3`, every phase surviving the stationary block is one. -/
theorem fifthPower_prime_phase_eq_zero (p s : Nat) (hs : s ∣ p ^ 3)
    (eta : Fin (p * s)) (heta : p ∣ eta.val) :
    ((eta.val ^ 5 : Nat) : ZMod (p * (p * s))) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  rcases hs with ⟨d, hd⟩
  rcases heta with ⟨k, hk⟩
  refine ⟨d * k ^ 5, ?_⟩
  rw [hk]
  calc
    (p * k) ^ 5 = p ^ 2 * p ^ 3 * k ^ 5 := by ring
    _ = p ^ 2 * (s * d) * k ^ 5 := by rw [hd]
    _ = p * (p * s) * (d * k ^ 5) := by ring

/-- Exact initial stationary-phase value in the modulus shape `p*(p*s)`. -/
theorem completePowerSum_fifth_prime_small_shape (p s : Nat)
    [NeZero p] [NeZero s] (hp : p.Prime) (hpFive : p ≠ 5)
    (hs : s ∣ p ^ 3) (a : Nat) (ha : a.Coprime p) :
    completePowerSum 5 ((a : Nat) : ZMod (p * (p * s))) = p * s := by
  rw [completePowerSum_fifth_prime_survivors p s hp hpFive a ha]
  calc
    ∑ eta : Fin (p * s),
        (if p ∣ eta.val then
          (p : Complex) * ZMod.stdAddChar
            (((a : Nat) : ZMod (p * (p * s))) *
              ((eta.val : Nat) : ZMod (p * (p * s))) ^ 5)
        else 0) =
        ∑ eta : Fin (p * s),
          (if p ∣ eta.val then (p : Complex) else 0) := by
      apply Finset.sum_congr rfl
      intro eta _
      split_ifs with heta
      · rw [← Nat.cast_pow, fifthPower_prime_phase_eq_zero p s hs eta heta]
        simp
      · rfl
    _ = p * s := sum_fin_prime_dvd p s hp

/-- Cancelling a common factor `p^5` in a fifth-power phase preserves the
standard additive character. -/
theorem stdAddChar_fifth_primeScale (p u : Nat) [NeZero p] [NeZero u]
    (a y : Nat) :
    ZMod.stdAddChar
        ((a * (p * y) ^ 5 : Nat) : ZMod (p ^ 5 * u)) =
      ZMod.stdAddChar ((a * y ^ 5 : Nat) : ZMod u) := by
  calc
    ZMod.stdAddChar ((a * (p * y) ^ 5 : Nat) : ZMod (p ^ 5 * u)) =
        Complex.exp
          (2 * Real.pi * Complex.I *
            ((a * (p * y) ^ 5 : Nat) : Complex) /
              ((p ^ 5 * u : Nat) : Complex)) := by
      simpa only [Int.cast_natCast] using
        ZMod.stdAddChar_coe (N := p ^ 5 * u)
          ((a * (p * y) ^ 5 : Nat) : Int)
    _ = Complex.exp
        (2 * Real.pi * Complex.I * ((a * y ^ 5 : Nat) : Complex) /
          (u : Complex)) := by
      congr 1
      push_cast
      have hp : (p : Complex) ≠ 0 := by exact_mod_cast NeZero.ne p
      have hu : (u : Complex) ≠ 0 := by exact_mod_cast NeZero.ne u
      field_simp [hp, hu]
    _ = ZMod.stdAddChar ((a * y ^ 5 : Nat) : ZMod u) := by
      symm
      simpa only [Int.cast_natCast] using
        ZMod.stdAddChar_coe (N := u) ((a * y ^ 5 : Nat) : Int)

/-- The character-scaling identity in the stationary-phase modulus shape. -/
theorem stdAddChar_fifth_primeScale_block (p u : Nat) [NeZero p] [NeZero u]
    (a y : Nat) :
    ZMod.stdAddChar
        (((a : Nat) : ZMod (p * (p * (p ^ 3 * u)))) *
          (((p * y : Nat) : ZMod (p * (p * (p ^ 3 * u)))) ^ 5)) =
      ZMod.stdAddChar ((a * y ^ 5 : Nat) : ZMod u) := by
  have hmod : p * (p * (p ^ 3 * u)) = p ^ 5 * u := by ring
  calc
    ZMod.stdAddChar
        (((a : Nat) : ZMod (p * (p * (p ^ 3 * u)))) *
          (((p * y : Nat) : ZMod (p * (p * (p ^ 3 * u)))) ^ 5)) =
        ZMod.stdAddChar
          ((a * (p * y) ^ 5 : Nat) : ZMod (p * (p * (p ^ 3 * u)))) := by
      congr 1
      push_cast
      rfl
    _ = ZMod.stdAddChar
        ((a * (p * y) ^ 5 : Nat) : ZMod (p ^ 5 * u)) :=
      stdAddChar_natCast_modulus_congr hmod _
    _ = ZMod.stdAddChar ((a * y ^ 5 : Nat) : ZMod u) :=
      stdAddChar_fifth_primeScale p u a y

/-- After stationary-phase cancellation, the surviving residues modulo
`p^5*u` are exactly the multiples of `p`. -/
theorem completePowerSum_fifth_prime_eq_multiples (p u : Nat)
    [NeZero p] [NeZero u] (hp : p.Prime) (hpFive : p ≠ 5)
    (a : Nat) (ha : a.Coprime p) :
    completePowerSum 5
        ((a : Nat) : ZMod (p * (p * (p ^ 3 * u)))) =
      ∑ y : Fin (p ^ 3 * u),
        (p : Complex) * ZMod.stdAddChar
          (((a : Nat) : ZMod (p * (p * (p ^ 3 * u)))) *
            (((p * y.val : Nat) : ZMod (p * (p * (p ^ 3 * u)))) ^ 5)) := by
  rw [completePowerSum_fifth_prime_survivors p (p ^ 3 * u)
    hp hpFive a ha]
  rw [← (finPrimeBlocks p (p ^ 3 * u)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  have hdiv (r : Fin p) : p ∣ r.val + p * y.val ↔ r.val = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
  simp_rw [finPrimeBlocks_val, hdiv]
  simp

/-- Cancelling the common fifth-power factor rewrites every surviving phase as
a phase modulo `u`. -/
theorem completePowerSum_fifth_prime_eq_scaledResidues (p u : Nat)
    [NeZero p] [NeZero u] (hp : p.Prime) (hpFive : p ≠ 5)
    (a : Nat) (ha : a.Coprime p) :
    completePowerSum 5
        ((a : Nat) : ZMod (p * (p * (p ^ 3 * u)))) =
      ∑ y : Fin (p ^ 3 * u),
        (p : Complex) *
          ZMod.stdAddChar ((a * y.val ^ 5 : Nat) : ZMod u) := by
  rw [completePowerSum_fifth_prime_eq_multiples p u hp hpFive a ha]
  apply Finset.sum_congr rfl
  intro y _
  rw [stdAddChar_fifth_primeScale_block]

/-- Exact five-step recurrence in the stationary-phase modulus shape. -/
theorem completePowerSum_fifth_prime_recurrence_block (p u : Nat)
    [NeZero p] [NeZero u] (hp : p.Prime) (hpFive : p ≠ 5)
    (a : Nat) (ha : a.Coprime p) :
    completePowerSum 5
        ((a : Nat) : ZMod (p * (p * (p ^ 3 * u)))) =
      (p ^ 4 : Nat) * completePowerSum 5 ((a : Nat) : ZMod u) := by
  rw [completePowerSum_fifth_prime_eq_scaledResidues p u hp hpFive a ha]
  rw [← (finProdFinEquiv : Fin (p ^ 3) × Fin u ≃
    Fin (p ^ 3 * u)).sum_comp]
  rw [Fintype.sum_prod_type]
  rw [completePowerSum_fifth_natCast_eq_fin]
  calc
    ∑ xi : Fin (p ^ 3), ∑ y : Fin u,
        (p : Complex) * ZMod.stdAddChar
          ((a * (finProdFinEquiv (xi, y)).val ^ 5 : Nat) : ZMod u) =
        ∑ _xi : Fin (p ^ 3), ∑ y : Fin u,
          (p : Complex) *
            ZMod.stdAddChar ((a * y.val ^ 5 : Nat) : ZMod u) := by
      apply Finset.sum_congr rfl
      intro xi _
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      apply congrArg ZMod.stdAddChar
      push_cast
      have hy :
          (((finProdFinEquiv (xi, y)).val : Nat) : ZMod u) =
            ((y.val : Nat) : ZMod u) := by
        change ((y.val + u * xi.val : Nat) : ZMod u) = _
        push_cast
        rw [ZMod.natCast_self]
        simp
      rw [hy]
    _ = (p ^ 4 : Nat) * ∑ y : Fin u,
        ZMod.stdAddChar ((a * y.val ^ 5 : Nat) : ZMod u) := by
      simp only [Finset.mul_sum]
      simp
      rw [← Finset.mul_sum]
      rw [← Finset.mul_sum]
      ring

/-- Exact recurrence when the modulus is multiplied by `p^5`. -/
theorem completePowerSum_fifth_prime_recurrence (p u : Nat)
    [NeZero p] [NeZero u] (hp : p.Prime) (hpFive : p ≠ 5)
    (a : Nat) (ha : a.Coprime p) :
    completePowerSum 5 ((a : Nat) : ZMod (p ^ 5 * u)) =
      (p ^ 4 : Nat) * completePowerSum 5 ((a : Nat) : ZMod u) := by
  calc
    completePowerSum 5 ((a : Nat) : ZMod (p ^ 5 * u)) =
        completePowerSum 5
          ((a : Nat) : ZMod (p * (p * (p ^ 3 * u)))) := by
      apply completePowerSum_natCast_modulus_congr
      ring
    _ = (p ^ 4 : Nat) * completePowerSum 5 ((a : Nat) : ZMod u) :=
      completePowerSum_fifth_prime_recurrence_block p u hp hpFive a ha

/-- Exact initial values for exponents two through five. -/
theorem completePowerSum_fifth_primePow_small {p alpha : Nat} [NeZero p]
    (hp : p.Prime) (hpFive : p ≠ 5) (hLower : 1 < alpha)
    (hUpper : alpha ≤ 5) (a : Nat) (ha : a.Coprime p) :
    completePowerSum 5 ((a : Nat) : ZMod (p ^ alpha)) =
      ((p ^ (alpha - 1) : Nat) : Complex) := by
  interval_cases alpha
  · have h := completePowerSum_fifth_prime_small_shape p 1 hp hpFive
      (by simp) a ha
    calc
      completePowerSum 5 ((a : Nat) : ZMod (p ^ 2)) =
          completePowerSum 5 ((a : Nat) : ZMod (p * (p * 1))) := by
        apply completePowerSum_natCast_modulus_congr
        ring
      _ = (p : Nat) * 1 := by simpa only [Nat.cast_one] using h
      _ = ((p ^ (2 - 1) : Nat) : Complex) := by norm_num
  · have h := completePowerSum_fifth_prime_small_shape p p hp hpFive
      (dvd_pow_self p (by norm_num)) a ha
    calc
      completePowerSum 5 ((a : Nat) : ZMod (p ^ 3)) =
          completePowerSum 5 ((a : Nat) : ZMod (p * (p * p))) := by
        apply completePowerSum_natCast_modulus_congr
        ring
      _ = (p : Nat) * p := h
      _ = ((p ^ (3 - 1) : Nat) : Complex) := by push_cast; ring
  · have h := completePowerSum_fifth_prime_small_shape p (p ^ 2) hp hpFive
      (pow_dvd_pow p (by norm_num)) a ha
    calc
      completePowerSum 5 ((a : Nat) : ZMod (p ^ 4)) =
          completePowerSum 5 ((a : Nat) : ZMod (p * (p * p ^ 2))) := by
        apply completePowerSum_natCast_modulus_congr
        ring
      _ = (p : Nat) * p ^ 2 := by simpa only [Nat.cast_pow] using h
      _ = ((p ^ (4 - 1) : Nat) : Complex) := by push_cast; ring
  · have h := completePowerSum_fifth_prime_small_shape p (p ^ 3) hp hpFive
      dvd_rfl a ha
    calc
      completePowerSum 5 ((a : Nat) : ZMod (p ^ 5)) =
          completePowerSum 5 ((a : Nat) : ZMod (p * (p * p ^ 3))) := by
        apply completePowerSum_natCast_modulus_congr
        ring
      _ = (p : Nat) * p ^ 3 := by simpa only [Nat.cast_pow] using h
      _ = ((p ^ (5 - 1) : Nat) : Complex) := by push_cast; ring

end Waring.Analytic
