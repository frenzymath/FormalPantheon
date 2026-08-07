import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldCrossLevelCharacters
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Goldfeld's four-factor coefficient

This file reconstructs the coefficient and initial half-plane series identity
in the proof of Koukoulopoulos Theorem 12.9, printed p. 126.  The two
individual characters retain their original levels; only their product is
formed at the canonical least-common-multiple level.  The later Mellin cutoff
and contour argument are deliberately separate.

Semantic review: `SEM-551`.
-/

noncomputable section

open scoped ComplexOrder
open ArithmeticFunction

namespace BoundedGaps.Maynard

private instance goldfeldLcmNeZero {q1 q : ℕ} [NeZero q1] [NeZero q] :
    NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

/-- The original-level fourfold Dirichlet convolution in Goldfeld's proof. -/
noncomputable def goldfeldCoefficient
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ((ArithmeticFunction.zeta * toArithmeticFunction (chi1 ·)) *
      toArithmeticFunction (chi ·)) *
    toArithmeticFunction (DirichletCharacter.mul chi1 chi ·)

/-- Canonical cross-level multiplication agrees with the original pointwise product. -/
theorem goldfeldCrossLevelMul_apply
    {q1 q n : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) :
    DirichletCharacter.mul chi1 chi n = chi1 n * chi n := by
  by_cases h1 : Nat.Coprime n q1
  · by_cases h2 : Nat.Coprime n q
    · have hlcm : Nat.Coprime n (Nat.lcm q1 q) :=
        Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul q1 q) (h1.mul_right h2)
      change
        (chi1.changeLevel (Nat.dvd_lcm_left q1 q) *
          chi.changeLevel (Nat.dvd_lcm_right q1 q)) n = _
      rw [MulChar.mul_apply]
      have hInt : IsCoprime (n : ℤ) (Nat.lcm q1 q : ℤ) :=
        Nat.Coprime.isCoprime hlcm
      simpa using congrArg₂ (· * ·)
        (DirichletCharacter.changeLevel_eq_cast_of_dvd' chi1
          (Nat.dvd_lcm_left q1 q) hInt)
        (DirichletCharacter.changeLevel_eq_cast_of_dvd' chi
          (Nat.dvd_lcm_right q1 q) hInt)
    · have hlcm : ¬Nat.Coprime n (Nat.lcm q1 q) := fun h =>
        h2 (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_right q1 q) h)
      have hpzero : DirichletCharacter.mul chi1 chi n = 0 :=
        MulChar.map_nonunit _ (by
          simpa [ZMod.isUnit_iff_coprime] using hlcm)
      have hzero : chi n = 0 :=
        MulChar.map_nonunit _ (by
          simpa [ZMod.isUnit_iff_coprime] using h2)
      rw [hpzero, hzero, mul_zero]
  · have hlcm : ¬Nat.Coprime n (Nat.lcm q1 q) := fun h =>
      h1 (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_left q1 q) h)
    have hpzero : DirichletCharacter.mul chi1 chi n = 0 :=
      MulChar.map_nonunit _ (by
        simpa [ZMod.isUnit_iff_coprime] using hlcm)
    have hzero : chi1 n = 0 :=
      MulChar.map_nonunit _ (by
        simpa [ZMod.isUnit_iff_coprime] using h1)
    rw [hpzero, hzero, zero_mul]

theorem goldfeldCoefficient_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) :
    goldfeldCoefficient chi1 chi 1 = 1 := by
  simp [goldfeldCoefficient, toArithmeticFunction]

private theorem characterAF_prime_pow
    {q p k : ℕ} (chi : DirichletCharacter ℂ q) (hp : p.Prime) :
    toArithmeticFunction (chi ·) (p ^ k) = (chi p) ^ k := by
  rw [← chi.apply_eq_toArithmeticFunction_apply (pow_ne_zero k hp.ne_zero)]
  simpa only [Nat.cast_pow] using map_pow chi (p : ZMod q) k

private theorem productAF_prime_pow
    {q1 q p k : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    (hp : p.Prime) :
    toArithmeticFunction (DirichletCharacter.mul chi1 chi ·) (p ^ k) =
      (chi1 p * chi p) ^ k := by
  rw [characterAF_prime_pow _ hp, goldfeldCrossLevelMul_apply]

private theorem zeta_prime_pow {p k : ℕ} (hp : p.Prime) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ k) = 1 := by
  have hpow : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  simp only [ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hpow, Nat.cast_one]

private theorem mul_apply_prime_pow
    (f g : ArithmeticFunction ℂ) {p k : ℕ} (hp : p.Prime) :
    (f * g) (p ^ k) =
      ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => f x * g y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.pow_div (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hp.pos]

private theorem mul_apply_prime_pow_eq_left_of_right_unit
    (f g : ArithmeticFunction ℂ) {p k : ℕ} (hp : p.Prime)
    (hone : g 1 = 1) (hzero : ∀ j, 0 < j → g (p ^ j) = 0) :
    (f * g) (p ^ k) = f (p ^ k) := by
  rw [mul_apply_prime_pow f g hp]
  classical
  rw [Finset.sum_eq_single k]
  · simp [hone]
  · intro i hi hik
    have hik' : i < k :=
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).lt_of_ne hik
    rw [hzero (k - i) (Nat.sub_pos_of_lt hik'), mul_zero]
  · simp

private theorem mul_prime_pow_nonneg_of_local_eq
    (f g : ArithmeticFunction ℂ) {p k : ℕ} (hp : p.Prime)
    (hf : ∀ n, 0 ≤ f n) (hlocal : ∀ j, g (p ^ j) = f (p ^ j)) :
    0 ≤ (f * g) (p ^ k) := by
  rw [mul_apply_prime_pow f g hp]
  exact Finset.sum_nonneg fun i _ => by
    rw [hlocal]
    exact mul_nonneg (hf _) (hf _)

private theorem goldfeldCoefficient_prime_pow_nonneg
    {q1 q p : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    (hp : p.Prime) (k : ℕ) :
    0 ≤ goldfeldCoefficient chi1 chi (p ^ k) := by
  let A := toArithmeticFunction (chi1 ·)
  let B := toArithmeticFunction (chi ·)
  let C := toArithmeticFunction (DirichletCharacter.mul chi1 chi ·)
  let Z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
  have hA : ∀ j, A (p ^ j) = (chi1 p) ^ j := fun _ =>
    characterAF_prime_pow chi1 hp
  have hB : ∀ j, B (p ^ j) = (chi p) ^ j := fun _ =>
    characterAF_prime_pow chi hp
  have hC : ∀ j, C (p ^ j) = (chi1 p * chi p) ^ j := fun _ =>
    productAF_prime_pow chi1 chi hp
  have hZ : ∀ j, Z (p ^ j) = 1 := fun _ => zeta_prime_pow hp
  have hZA : ∀ n, 0 ≤ (Z * A) n := fun n => by
    simpa [Z, A, DirichletCharacter.zetaMul] using
      chi1.zetaMul_nonneg hsquare1 n
  have hZB : ∀ n, 0 ≤ (Z * B) n := fun n => by
    simpa [Z, B, DirichletCharacter.zetaMul] using
      chi.zetaMul_nonneg hsquare n
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare1 p with ha | ha | ha
  · have hCunit : C 1 = 1 := by simpa using hC 0
    have hCzero : ∀ j, 0 < j → C (p ^ j) = 0 := by
      intro j hj
      rw [hC]
      simp [ha, zero_pow hj.ne']
    have hAC (j : ℕ) : (A * C) (p ^ j) = A (p ^ j) :=
      mul_apply_prime_pow_eq_left_of_right_unit A C hp hCunit hCzero
    have hACunit : (A * C) 1 = 1 := by
      calc
        (A * C) 1 = (A * C) (p ^ 0) := by simp
        _ = A (p ^ 0) := hAC 0
        _ = (chi1 p) ^ 0 := hA 0
        _ = 1 := by simp
    have hACzero : ∀ j, 0 < j → (A * C) (p ^ j) = 0 := by
      intro j hj
      rw [hAC, hA]
      simp [ha, zero_pow hj.ne']
    rw [goldfeldCoefficient]
    rw [show ((Z * A) * B) * C = (Z * B) * (A * C) by ac_rfl]
    rw [mul_apply_prime_pow_eq_left_of_right_unit (Z * B) (A * C)
      hp hACunit hACzero]
    exact hZB _
  · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare p with hb | hb | hb
    · have hBunit : B 1 = 1 := by simpa using hB 0
      have hBzero : ∀ j, 0 < j → B (p ^ j) = 0 := by
        intro j hj
        rw [hB]
        simp [hb, zero_pow hj.ne']
      have hCB (j : ℕ) : (C * B) (p ^ j) = C (p ^ j) :=
        mul_apply_prime_pow_eq_left_of_right_unit C B hp hBunit hBzero
      have hCBunit : (C * B) 1 = 1 := by
        calc
          (C * B) 1 = (C * B) (p ^ 0) := by simp
          _ = C (p ^ 0) := hCB 0
          _ = (chi1 p * chi p) ^ 0 := hC 0
          _ = 1 := by simp
      have hCBzero : ∀ j, 0 < j → (C * B) (p ^ j) = 0 := by
        intro j hj
        rw [hCB, hC]
        simp [hb, zero_pow hj.ne']
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (C * B) by ac_rfl]
      rw [mul_apply_prime_pow_eq_left_of_right_unit (Z * A) (C * B)
        hp hCBunit hCBzero]
      exact hZA _
    · have hpair (j : ℕ) : (B * C) (p ^ j) = (Z * A) (p ^ j) := by
        rw [mul_apply_prime_pow B C hp, mul_apply_prime_pow Z A hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hB, hC, hZ, hA]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (B * C) by ac_rfl]
      exact mul_prime_pow_nonneg_of_local_eq (Z * A) (B * C) hp hZA hpair
    · have hpair (j : ℕ) : (A * C) (p ^ j) = (Z * B) (p ^ j) := by
        rw [mul_apply_prime_pow A C hp, mul_apply_prime_pow Z B hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hA, hC, hZ, hB]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * B) * (A * C) by ac_rfl]
      exact mul_prime_pow_nonneg_of_local_eq (Z * B) (A * C) hp hZB hpair
  · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare p with hb | hb | hb
    · have hBunit : B 1 = 1 := by simpa using hB 0
      have hBzero : ∀ j, 0 < j → B (p ^ j) = 0 := by
        intro j hj
        rw [hB]
        simp [hb, zero_pow hj.ne']
      have hCB (j : ℕ) : (C * B) (p ^ j) = C (p ^ j) :=
        mul_apply_prime_pow_eq_left_of_right_unit C B hp hBunit hBzero
      have hCBunit : (C * B) 1 = 1 := by
        calc
          (C * B) 1 = (C * B) (p ^ 0) := by simp
          _ = C (p ^ 0) := hCB 0
          _ = (chi1 p * chi p) ^ 0 := hC 0
          _ = 1 := by simp
      have hCBzero : ∀ j, 0 < j → (C * B) (p ^ j) = 0 := by
        intro j hj
        rw [hCB, hC]
        simp [hb, zero_pow hj.ne']
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (C * B) by ac_rfl]
      rw [mul_apply_prime_pow_eq_left_of_right_unit (Z * A) (C * B)
        hp hCBunit hCBzero]
      exact hZA _
    · have hpair (j : ℕ) : (B * C) (p ^ j) = (Z * A) (p ^ j) := by
        rw [mul_apply_prime_pow B C hp, mul_apply_prime_pow Z A hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hB, hC, hZ, hA]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (B * C) by ac_rfl]
      exact mul_prime_pow_nonneg_of_local_eq (Z * A) (B * C) hp hZA hpair
    · have hpair (j : ℕ) : (C * B) (p ^ j) = (Z * A) (p ^ j) := by
        rw [mul_apply_prime_pow C B hp, mul_apply_prime_pow Z A hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hC, hB, hZ, hA]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (C * B) by ac_rfl]
      exact mul_prime_pow_nonneg_of_local_eq (Z * A) (C * B) hp hZA hpair

private theorem goldfeldCoefficient_isMultiplicative
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q) :
    (goldfeldCoefficient chi1 chi).IsMultiplicative := by
  exact (((ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    chi1.isMultiplicative_toArithmeticFunction).mul
      chi.isMultiplicative_toArithmeticFunction).mul
        (DirichletCharacter.mul chi1 chi).isMultiplicative_toArithmeticFunction)

/-- Every coefficient is real and nonnegative for two square-principal characters. -/
theorem goldfeldCoefficient_nonneg
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1) (n : ℕ) :
    0 ≤ goldfeldCoefficient chi1 chi n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [(goldfeldCoefficient_isMultiplicative chi1 chi).multiplicative_factorization _ hn]
    exact Finset.prod_nonneg fun p hp =>
      goldfeldCoefficient_prime_pow_nonneg chi1 chi hsquare1 hsquare
        (Nat.prime_of_mem_primeFactors hp) _

private theorem characterAF_LSeriesHasSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (toArithmeticFunction (chi ·)) s
      (DirichletCharacter.LFunction chi s) := by
  have hsummable : LSeriesSummable (toArithmeticFunction (chi ·)) s :=
    (LSeriesSummable_congr s fun hn =>
      chi.apply_eq_toArithmeticFunction_apply hn).mp
        (ZMod.LSeriesSummable_of_one_lt_re chi hs)
  rw [chi.LFunction_eq_LSeries hs,
    LSeries_congr (fun hn => chi.apply_eq_toArithmeticFunction_apply hn) s]
  exact hsummable.LSeriesHasSum

/-- The coefficient series equals Goldfeld's four-factor product on `Re(s)>1`. -/
theorem goldfeldCoefficient_LSeriesHasSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (goldfeldCoefficient chi1 chi) s
      (riemannZeta s * DirichletCharacter.LFunction chi1 s *
        DirichletCharacter.LFunction chi s *
          DirichletCharacter.LFunction
            (DirichletCharacter.mul chi1 chi) s) := by
  exact ArithmeticFunction.LSeriesHasSum_mul
    (ArithmeticFunction.LSeriesHasSum_mul
      (ArithmeticFunction.LSeriesHasSum_mul
        (ArithmeticFunction.LSeriesHasSum_zeta hs)
        (characterAF_LSeriesHasSum chi1 hs))
      (characterAF_LSeriesHasSum chi hs))
    (characterAF_LSeriesHasSum (DirichletCharacter.mul chi1 chi) hs)

end BoundedGaps.Maynard
