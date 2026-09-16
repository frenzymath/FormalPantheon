import PrimesRestrictedDigits.MajorArcs.Partition
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum

/-!
# Nondivisor denominators at a power of ten

This implements the arithmetic denominator factor used in the M1 discussion
of `MAYNARD-PRD-PUBLISHED`, Section 11, p. 186. The separate hypotheses of
Lemma 10.1 remain downstream obligations.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

private theorem eventually_majorArcPowerTen_log_pow_le_two_pow (D : Nat) :
    ∀ᶠ k : Nat in atTop,
      Real.log (((10 ^ k : Nat) : Real)) ^ D ≤
        ((2 ^ k : Nat) : Real) := by
  have hbound :=
    ((isLittleO_pow_const_const_pow_of_one_lt (R := Real) D
      (by norm_num : (1 : Real) < 2)).const_mul_left
        (Real.log 10 ^ D)).bound zero_lt_one
  filter_upwards [hbound] with k hk
  have hlog : 0 ≤ Real.log 10 ^ D :=
    pow_nonneg (Real.log_nonneg (by norm_num)) D
  have hkpow : 0 ≤ (k : Real) ^ D := by positivity
  have htwo : 0 ≤ (2 : Real) ^ k := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hlog hkpow),
    Real.norm_eq_abs, abs_of_nonneg htwo, one_mul] at hk
  calc
    Real.log (((10 ^ k : Nat) : Real)) ^ D =
        ((k : Real) * Real.log 10) ^ D := by
          simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    _ = Real.log 10 ^ D * (k : Real) ^ D := by
          rw [mul_pow, mul_comm]
    _ ≤ (2 : Real) ^ k := hk
    _ = ((2 ^ k : Nat) : Real) := by norm_num

/-- A fixed power of `log (10^k)` is eventually at most `2^k`. -/
theorem exists_majorArcPowerTenFactorThreshold (D : Nat) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      Real.log (((10 ^ k : Nat) : Real)) ^ D ≤
        ((2 ^ k : Nat) : Real) :=
  eventually_atTop.mp (eventually_majorArcPowerTen_log_pow_le_two_pow D)

/-- A sufficiently small nondivisor of `10^k` has a prime factor coprime to
ten. The size hypothesis is essential, as `4` does not divide `10`. -/
theorem exists_prime_coprime_ten_of_le_two_pow_of_not_dvd_ten_pow
    {q k : Nat} (hq : 0 < q) (hqle : q ≤ 2 ^ k)
    (hnot : ¬q ∣ 10 ^ k) :
    ∃ p : Nat, p.Prime ∧ p ∣ q ∧ Nat.Coprime p 10 ∧
      q = p * (q / p) := by
  have hex :
      ∃ p : Nat, p.Prime ∧ p ∣ q ∧ Nat.Coprime p 10 := by
    by_contra hnone
    apply hnot
    rw [← Nat.factorization_prime_le_iff_dvd hq.ne'
      (pow_ne_zero k (by decide : 10 ≠ 0))]
    intro p hp
    by_cases hpc : Nat.Coprime p 10
    · have hpdq : ¬p ∣ q := fun hpdq =>
        hnone ⟨p, hp, hpdq, hpc⟩
      simp [Nat.factorization_eq_zero_of_not_dvd hpdq]
    · have hpd10 : p ∣ 10 := by
        by_contra hpnot
        exact hpc ((hp.coprime_iff_not_dvd).2 hpnot)
      have hqpow : q ≤ p ^ k :=
        hqle.trans (Nat.pow_le_pow_left hp.two_le k)
      have hfacQ : q.factorization p ≤ k :=
        Nat.factorization_le_of_le_pow hqpow
      have hfacX : k ≤ (10 ^ k).factorization p :=
        (hp.pow_dvd_iff_le_factorization
          (pow_ne_zero k (by decide : 10 ≠ 0))).mp
            (pow_dvd_pow_of_dvd hpd10 k)
      exact hfacQ.trans hfacX
  rcases hex with ⟨p, hp, hpdq, hpc⟩
  exact ⟨p, hp, hpdq, hpc, (Nat.mul_div_cancel' hpdq).symm⟩

/-- The canonical reduced denominator factor required by the source M1
argument, without claiming the later analytic decay. -/
theorem majorArcClassOne_exists_sourceDenominatorFactor
    {k frequency : Nat} {Q : Real}
    (hQ : Q ≤ ((2 ^ k : Nat) : Real))
    (hclass : majorArcClassOne (10 ^ k) frequency Q) :
    ∃ r : Rat, ∃ q1 q2 : Nat,
      majorArcRationalApproximation (10 ^ k) frequency Q r ∧
        r.den = q1 * q2 ∧ q1.Prime ∧ Nat.Coprime q1 10 ∧
        1 < q1 ∧ Nat.Coprime r.num.natAbs r.den := by
  rcases hclass.nondivisor with ⟨r, hr, hnot⟩
  have hdenLeReal : (r.den : Real) ≤ ((2 ^ k : Nat) : Real) :=
    hr.2.trans hQ
  have hdenLe : r.den ≤ 2 ^ k := by exact_mod_cast hdenLeReal
  rcases exists_prime_coprime_ten_of_le_two_pow_of_not_dvd_ten_pow
      r.den_pos hdenLe hnot with ⟨p, hp, _, hpc, heq⟩
  exact ⟨r, p, r.den / p, hr, heq, hp, hpc, hp.one_lt, r.reduced⟩

/-- The source-logarithmic specialization of the M1 denominator factor. -/
theorem exists_majorArcClassOneLogPowerSourceDenominatorFactorThreshold
    (D : Nat) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      ∀ frequency : Nat,
        majorArcClassOne (10 ^ k) frequency
          (Real.log (((10 ^ k : Nat) : Real)) ^ D) →
        ∃ r : Rat, ∃ q1 q2 : Nat,
          majorArcRationalApproximation (10 ^ k) frequency
              (Real.log (((10 ^ k : Nat) : Real)) ^ D) r ∧
            r.den = q1 * q2 ∧ q1.Prime ∧ Nat.Coprime q1 10 ∧
              1 < q1 ∧ Nat.Coprime r.num.natAbs r.den := by
  rcases exists_majorArcPowerTenFactorThreshold D with ⟨k0, hk0⟩
  refine ⟨k0, ?_⟩
  intro k hk frequency hclass
  exact majorArcClassOne_exists_sourceDenominatorFactor (hk0 k hk) hclass

end PrimesRestrictedDigits
