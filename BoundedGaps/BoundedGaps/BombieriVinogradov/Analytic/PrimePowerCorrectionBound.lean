import BoundedGaps.BombieriVinogradov.Analytic.PrimePowerCorrection
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Logarithmic bound for the imprimitive correction

This file implements the finite estimate reviewed in SEM-416 and sourced from
`AkbaryHambrook2013v2`, Section 7, p. 24. It reindexes the correction by prime
base and positive exponent, bounds each base's contribution by `log x`, and
proves the source bound `(log (q * x)) ^ 2`. It proves no character mean-value
or Bombieri--Vinogradov estimate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- The scalar logarithmic mass dominating a prime-power correction. -/
noncomputable def primePowerCorrectionMass (x q : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x with IsPrimePow n ∧ ¬Nat.Coprime n q,
    Real.log (n.minFac : ℝ)

/-- Prime bases dividing `q`, paired with positive exponents whose powers are at most `x`. -/
def primePowerCorrectionPairs (x q : ℕ) : Finset (ℕ × ℕ) :=
  (q.primeFactors ×ˢ Finset.Icc 1 x).filter fun pk => pk.1 ^ pk.2 ≤ x

theorem primePowerCorrectionMass_eq_pair_sum
    {x q : ℕ} (hq : q ≠ 0) :
    primePowerCorrectionMass x q =
      ∑ pk ∈ primePowerCorrectionPairs x q,
        Real.log (pk.1 : ℝ) := by
  rw [primePowerCorrectionMass, primePowerCorrectionPairs]
  apply Finset.sum_bij
      (fun n _ => (n.minFac, n.factorization n.minFac))
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnx, hpp, hncop⟩
    have hnx_bounds : 1 ≤ n ∧ n ≤ x := Finset.mem_Icc.mp hnx
    have hp : Nat.Prime n.minFac := Nat.minFac_prime hpp.ne_one
    have hk : 0 < n.factorization n.minFac := by
      rw [pos_iff_ne_zero]
      intro hkzero
      apply hpp.ne_one
      simpa [hkzero] using hpp.minFac_pow_factorization_eq.symm
    have hpow := hpp.minFac_pow_factorization_eq
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Nat.mem_primeFactors.mpr
        ⟨hp, minFac_dvd_of_isPrimePow_not_coprime hpp hncop, hq⟩,
      Finset.mem_Icc.mpr
        ⟨hk, (Nat.lt_pow_self hp.one_lt).le.trans
          (hpow.trans_le hnx_bounds.2)⟩⟩,
      hpow.trans_le hnx_bounds.2⟩
  · intro n₁ hn₁ n₂ hn₂ hpair
    have hpp₁ : IsPrimePow n₁ := (Finset.mem_filter.mp hn₁).2.1
    have hpp₂ : IsPrimePow n₂ := (Finset.mem_filter.mp hn₂).2.1
    have hpow₁ := hpp₁.minFac_pow_factorization_eq
    have hpow₂ := hpp₂.minFac_pow_factorization_eq
    calc
      n₁ = n₁.minFac ^ n₁.factorization n₁.minFac := hpow₁.symm
      _ = n₂.minFac ^ n₂.factorization n₂.minFac :=
        congrArg (fun z : ℕ × ℕ => z.1 ^ z.2) hpair
      _ = n₂ := hpow₂
  · rintro ⟨p, k⟩ hpk
    rcases Finset.mem_filter.mp hpk with ⟨hprod, hpow⟩
    rcases Finset.mem_product.mp hprod with ⟨hpq, hkx⟩
    have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpq
    have hpdvd : p ∣ q := Nat.dvd_of_mem_primeFactors hpq
    have hk : 0 < k := (Finset.mem_Icc.mp hkx).1
    have hpp : IsPrimePow (p ^ k) :=
      (isPrimePow_nat_iff (p ^ k)).mpr ⟨p, k, hp, hk, rfl⟩
    have hncop : ¬Nat.Coprime (p ^ k) q := by
      rw [not_coprime_iff_minFac_dvd_of_isPrimePow hpp,
        hp.pow_minFac hk.ne']
      exact hpdvd
    have hone : 1 ≤ p ^ k := one_le_pow₀ hp.one_le
    have hnmem : p ^ k ∈
        (Finset.Icc 1 x).filter
          (fun n => IsPrimePow n ∧ ¬Nat.Coprime n q) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hone, hpow⟩, hpp, hncop⟩
    refine ⟨p ^ k, hnmem, ?_⟩
    simp [hp.pow_minFac hk.ne', hp.factorization_pow]
  · intro n hn
    rfl

theorem sum_prime_powers_log_le_log
    {x p : ℕ} (hx : 2 ≤ x) (hp : Nat.Prime p) :
    (∑ k ∈ Finset.Icc 1 x with p ^ k ≤ x,
      Real.log (p : ℝ)) ≤ Real.log (x : ℝ) := by
  have hx0 : x ≠ 0 := by omega
  have hfilter :
      (Finset.Icc 1 x).filter (fun k => p ^ k ≤ x) =
        Finset.Icc 1 (p.log x) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, _⟩, hpow⟩
      exact ⟨hk1, Nat.le_log_of_pow_le hp.one_lt hpow⟩
    · rintro ⟨hk1, hklog⟩
      have hpow : p ^ k ≤ x :=
        (Nat.le_log_iff_pow_le hp.one_lt hx0).mp hklog
      have hkx : k ≤ x :=
        (Nat.lt_pow_self hp.one_lt).le.trans hpow
      exact ⟨⟨hk1, hkx⟩, hpow⟩
  rw [hfilter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hnatlog : (p.log x : ℝ) ≤ Real.log (x : ℝ) / Real.log (p : ℝ) := by
    simpa [Real.logb] using Real.natLog_le_logb x p
  have hmul := mul_le_mul_of_nonneg_right hnatlog hlogp.le
  field_simp [hlogp.ne'] at hmul
  simpa [Nat.cast_ofNat] using hmul

theorem primePowerCorrectionMass_le_log_mul_card_primeFactors
    {x q : ℕ} (hx : 2 ≤ x) (hq : 1 ≤ q) :
    primePowerCorrectionMass x q ≤
      Real.log (x : ℝ) * (q.primeFactors.card : ℝ) := by
  have hq0 : q ≠ 0 := by omega
  rw [primePowerCorrectionMass_eq_pair_sum hq0]
  calc
    (∑ pk ∈ primePowerCorrectionPairs x q,
        Real.log (pk.1 : ℝ)) =
        ∑ p ∈ q.primeFactors,
          ∑ k ∈ Finset.Icc 1 x with p ^ k ≤ x,
            Real.log (p : ℝ) := by
      simp only [primePowerCorrectionPairs, Finset.sum_filter,
        Finset.sum_product]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (x : ℝ) := by
      apply Finset.sum_le_sum
      intro p hpq
      exact sum_prime_powers_log_le_log hx
        (Nat.prime_of_mem_primeFactors hpq)
    _ = Real.log (x : ℝ) * (q.primeFactors.card : ℝ) := by
      simp [Finset.sum_const, mul_comm]

theorem card_primeFactors_le_two_mul_log
    {q : ℕ} (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ 2 * Real.log (q : ℝ) := by
  have hq0 : q ≠ 0 := by omega
  have htwo_prod : 2 ^ q.primeFactors.card ≤
      ∏ p ∈ q.primeFactors, p := by
    apply Finset.pow_card_le_prod
    intro p hpq
    exact (Nat.prime_of_mem_primeFactors hpq).two_le
  have hprod_q : (∏ p ∈ q.primeFactors, p) ≤ q :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have hpow_q : 2 ^ q.primeFactors.card ≤ q := htwo_prod.trans hprod_q
  have hlog_le : Real.log ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤
      Real.log (q : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hpow_q
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog_le
  have hhalf_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hcard_half : (q.primeFactors.card : ℝ) * (1 / 2) ≤
      (q.primeFactors.card : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hhalf_log_two (by positivity)
  nlinarith

theorem norm_primePowerCorrectionSum_le_mass
    (x q r : ℕ) (χ : DirichletCharacter ℂ r) :
    ‖primePowerCorrectionSum x q r χ‖ ≤
      primePowerCorrectionMass x q := by
  unfold primePowerCorrectionSum primePowerCorrectionMass
  calc
    ‖∑ n ∈ Finset.Icc 1 x with IsPrimePow n ∧ ¬Nat.Coprime n q,
        χ n * (Real.log (n.minFac : ℝ) : ℂ)‖ ≤
        ∑ n ∈ Finset.Icc 1 x with IsPrimePow n ∧ ¬Nat.Coprime n q,
          ‖χ n * (Real.log (n.minFac : ℝ) : ℂ)‖ := by
      apply norm_sum_le
    _ ≤ ∑ n ∈ Finset.Icc 1 x with IsPrimePow n ∧ ¬Nat.Coprime n q,
        Real.log (n.minFac : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      have hχ : ‖χ (n : ZMod r)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one χ (n : ZMod r)
      have hlog : 0 ≤ Real.log (n.minFac : ℝ) :=
        Real.log_natCast_nonneg _
      have hnormlog : ‖(Real.log (n.minFac : ℝ) : ℂ)‖ =
          Real.log (n.minFac : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
      rw [hnormlog]
      simpa using (mul_le_mul_of_nonneg_right hχ hlog)

theorem norm_primePowerCorrectionSum_le_log_mul_sq
    {x q r : ℕ} (χ : DirichletCharacter ℂ r)
    (hx : 2 ≤ x) (hq : 1 ≤ q) :
    ‖primePowerCorrectionSum x q r χ‖ ≤
      (Real.log ((q * x : ℕ) : ℝ)) ^ 2 := by
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hcard := card_primeFactors_le_two_mul_log hq
  have hcard_mul :
      Real.log (x : ℝ) * (q.primeFactors.card : ℝ) ≤
        Real.log (x : ℝ) * (2 * Real.log (q : ℝ)) :=
    mul_le_mul_of_nonneg_left hcard hlogx
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  calc
    ‖primePowerCorrectionSum x q r χ‖ ≤
        primePowerCorrectionMass x q :=
      norm_primePowerCorrectionSum_le_mass x q r χ
    _ ≤ Real.log (x : ℝ) * (q.primeFactors.card : ℝ) :=
      primePowerCorrectionMass_le_log_mul_card_primeFactors hx hq
    _ ≤ Real.log (x : ℝ) * (2 * Real.log (q : ℝ)) := hcard_mul
    _ ≤ (Real.log (q : ℝ) + Real.log (x : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (q : ℝ) - Real.log (x : ℝ))]
    _ = (Real.log ((q * x : ℕ) : ℝ)) ^ 2 := by
      rw [Nat.cast_mul, Real.log_mul hq0 hx0]

theorem norm_primitiveTwistedChebyshevSum_sub_le_log_mul_sq
    {x q : ℕ} (χ : DirichletCharacter ℂ q)
    (hx : 2 ≤ x) (hq : 1 ≤ q) :
    ‖twistedChebyshevSum x χ.conductor χ.primitiveCharacter -
        twistedChebyshevSum x q χ‖ ≤
      (Real.log ((q * x : ℕ) : ℝ)) ^ 2 := by
  rw [primitiveTwistedChebyshevSum_eq_add_primePowerCorrection]
  simpa using
    norm_primePowerCorrectionSum_le_log_mul_sq χ.primitiveCharacter hx hq

end BoundedGaps.Maynard
