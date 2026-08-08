import Waring.Analytic.ChenTwo
import Waring.Analytic.ZModCharacterCorrelation

/-!
# Finite singular coefficients in Chen's Lemma 10

This file defines Chen's coefficient `A(q,n)` and proves its finite
structural properties [CHEN1964-EN, pp. 1561, 1565-1567;
CHEN1964-ZH, pp. 728, 731-733].
-/

namespace Waring.Analytic

open scoped BigOperators ComplexConjugate

/-- One unfiltered term in Chen's singular coefficient. -/
noncomputable def chenTenSingularTerm
  (q : Nat) [NeZero q] (n : Nat) (a : ZMod q) : Complex :=
  (completePowerSum 5 a / (q : Complex)) ^ 15 *
    ZMod.stdAddChar (-a * (n : ZMod q))

/-- Chen's finite singular coefficient `A(q,n)`, with the source
coprimality condition represented by the unit predicate in `ZMod q`. -/
noncomputable def chenTenSingularCoefficient
    (q : Nat) [NeZero q] (n : Nat) : Complex :=
  ∑ a : ZMod q, if IsUnit a then chenTenSingularTerm q n a else 0

/-- The conjugate of the standard additive character is its value at the
negative residue. -/
theorem conj_stdAddChar {q : Nat} [NeZero q] (u : ZMod q) :
    conj (ZMod.stdAddChar u) = ZMod.stdAddChar (-u) := by
  have h := stdAddChar_mul_conj (0 : ZMod q) u
  simpa using h

/-- Conjugating a fifth-power complete sum negates its coefficient. -/
theorem conj_completePowerSum_five {q : Nat} [NeZero q] (a : ZMod q) :
    conj (completePowerSum 5 a) = completePowerSum 5 (-a) := by
  unfold completePowerSum powerSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [conj_stdAddChar]
  congr 1
  ring

/-- Conjugating one singular-coefficient term negates its residue index. -/
theorem conj_chenTenSingularTerm
    (q : Nat) [NeZero q] (n : Nat) (a : ZMod q) :
    conj (chenTenSingularTerm q n a) =
      chenTenSingularTerm q n (-a) := by
  unfold chenTenSingularTerm
  rw [map_mul, map_pow, map_div₀, conj_completePowerSum_five,
    map_natCast, conj_stdAddChar]
  ring_nf

/-- Every finite singular coefficient is fixed by complex conjugation. -/
theorem conj_chenTenSingularCoefficient
    (q : Nat) [NeZero q] (n : Nat) :
    conj (chenTenSingularCoefficient q n) =
      chenTenSingularCoefficient q n := by
  unfold chenTenSingularCoefficient
  rw [map_sum]
  calc
    (∑ a : ZMod q,
        conj (if IsUnit a then chenTenSingularTerm q n a else 0)) =
        ∑ a : ZMod q,
          if IsUnit a then chenTenSingularTerm q n (-a) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : IsUnit a <;> simp [ha, conj_chenTenSingularTerm]
    _ = ∑ a : ZMod q,
        if IsUnit a then chenTenSingularTerm q n a else 0 := by
      apply Fintype.sum_equiv (Equiv.neg (ZMod q))
      intro a
      simp

/-- Chen's singular coefficient is real-valued. -/
theorem chenTenSingularCoefficient_im_eq_zero
    (q : Nat) [NeZero q] (n : Nat) :
    (chenTenSingularCoefficient q n).im = 0 := by
  exact Complex.conj_eq_iff_im.mp
    (conj_chenTenSingularCoefficient q n)

/-- The modulus-one coefficient is exactly one. -/
@[simp] theorem chenTenSingularCoefficient_one (n : Nat) :
    chenTenSingularCoefficient 1 n = 1 := by
  unfold chenTenSingularCoefficient
  rw [Fintype.sum_unique]
  have hunit : IsUnit (default : ZMod 1) := by
    simpa only [Subsingleton.elim (default : ZMod 1) 1] using
      (isUnit_one : IsUnit (1 : ZMod 1))
  have hterm (a : ZMod 1) : chenTenSingularTerm 1 n a = 1 := by
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    simp [chenTenSingularTerm, completePowerSum, powerSum]
  split
  · exact hterm default
  · contradiction

/-- A uniform complete-sum bound gives the coarse coefficient estimate used
for absolute convergence of the singular series. -/
theorem norm_chenTenSingularCoefficient_le
    (q : Nat) [NeZero q] (n : Nat) (B : Real) (hB0 : 0 <= B)
    (hB : ∀ a : ZMod q, IsUnit a -> ‖completePowerSum 5 a‖ <= B) :
    ‖chenTenSingularCoefficient q n‖ <=
      q * (B / q) ^ 15 := by
  have hq : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  unfold chenTenSingularCoefficient
  calc
    ‖∑ a : ZMod q, if IsUnit a then chenTenSingularTerm q n a else 0‖ <=
        ∑ a : ZMod q,
          ‖if IsUnit a then chenTenSingularTerm q n a else 0‖ :=
      norm_sum_le _ _
    _ <= ∑ _a : ZMod q, (B / q) ^ 15 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : IsUnit a
      · simp only [if_pos ha, chenTenSingularTerm, norm_mul, norm_pow,
          norm_div, Complex.norm_natCast, norm_stdAddChar, mul_one]
        exact pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_right (hB a ha) hq.le) 15
      · simp [ha]
        positivity
    _ = q * (B / q) ^ 15 := by simp

/-- Chen's global complete-sum estimate makes the singular coefficients
quadratically summable in the modulus. -/
theorem norm_chenTenSingularCoefficient_le_chenTwo
    (q : Nat) [NeZero q] (n : Nat) :
    ‖chenTenSingularCoefficient q n‖ <=
      (40 : Real) ^ 15 * (q : Real) ^ (-2 : Real) := by
  have hq : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hbound := norm_chenTenSingularCoefficient_le q n
    (40 * (q : Real) ^ (4 / 5 : Real)) (by positivity)
    (fun a ha => chen_two_completePowerSum_bound a ha)
  have hdiv :
      (40 * (q : Real) ^ (4 / 5 : Real)) / q =
        40 * (q : Real) ^ (-1 / 5 : Real) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    calc
      40 * (q : Real) ^ (4 / 5 : Real) * (q : Real) ^ (-1 : Real) =
          40 * ((q : Real) ^ (4 / 5 : Real) *
            (q : Real) ^ (-1 : Real)) := by ring
      _ = 40 * (q : Real) ^ ((4 / 5 : Real) + (-1 : Real)) := by
        rw [← Real.rpow_add hq]
      _ = 40 * (q : Real) ^ (-1 / 5 : Real) := by norm_num
  have hpow :
      ((q : Real) ^ (-1 / 5 : Real)) ^ 15 =
        (q : Real) ^ (-3 : Real) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hq.le]
    congr 2
    norm_num
  have hcombine :
      (q : Real) * (q : Real) ^ (-3 : Real) =
        (q : Real) ^ (-2 : Real) := by
    conv_lhs => lhs; rw [← Real.rpow_one (q : Real)]
    rw [← Real.rpow_add hq]
    norm_num
  calc
    ‖chenTenSingularCoefficient q n‖ <=
        q * ((40 * (q : Real) ^ (4 / 5 : Real)) / q) ^ 15 := hbound
    _ = (q : Real) * (40 * (q : Real) ^ (-1 / 5 : Real)) ^ 15 := by
      rw [hdiv]
    _ = (40 : Real) ^ 15 *
        ((q : Real) * ((q : Real) ^ (-1 / 5 : Real)) ^ 15) := by ring
    _ = (40 : Real) ^ 15 *
        ((q : Real) * (q : Real) ^ (-3 : Real)) := by rw [hpow]
    _ = (40 : Real) ^ 15 * (q : Real) ^ (-2 : Real) := by rw [hcombine]

end Waring.Analytic
